# -*- coding: utf-8 -*-
r"""
Embeddings of standard fields
=============================

The output of the method :meth:`hom` is an instance of the class
:class:`EmbeddingOfStandardFields` and represents **embedding**, i.e. an
(automatically injective) field homomorphism `\phi:K\to L`. Similar to the
class :class:`StandardField <mclf.fields.standard_fields.StandardField>`,
instances of this class have methods identical or very similar to usual
morphisms between fields in Sage. For instance, given an element `a` of `K`,
we can evaluate the map `\phi` simply with::

    sage: phi(a)

EXAMPLES::

    sage: from mclf import *
    sage: K = GF(2)
    sage: L = GF(4)
    sage: phi = K.hom(L); phi
    Ring morphism:
      From: Finite Field of size 2
      To:   Finite Field in z2 of size 2^2
      Defn: 1 |--> 1

We can turn this ring homomorphism into an object of the class
:class:`EmbeddingOfStandardFields`::

    sage: phi = embedding_of_standard_fields(phi); phi
    the embedding of Finite Field of size 2 into Finite Field in z2
    of size 2^2, sending 1 to 1

This object behaves mostly like a usual ring morphism in Sage::

    sage: phi.domain()
    Finite Field of size 2
    sage: phi.codomain()
    Finite Field in z2 of size 2^2
    sage: phi(1)
    1

Note that the result of :meth:`domain` and :meth:`codomain` are objects of the
Sage categorie ``Fields``. To obtain the corresponding objects of
:class:`StandardField <mclf.fields.standard_fields.StandardField>`, we can use
:meth:`Domain` and :meth:`Codomain`::

    sage: phi.Domain()
    the standard field with 2 elements
    sage: phi.Codomain()
    the standard field with 4 elements

"""

from sage.all import SageObject, lcm
from sage.categories.rings import Rings
from sage.categories.fields import Fields
from sage.categories.number_fields import NumberFields
from sage.categories.function_fields import FunctionFields
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from mclf.fields.standard_fields import (standard_field, StandardField,
                                         StandardFiniteField,
                                         StandardNumberField,
                                         StandardFunctionField)


def embedding_of_standard_fields(*args):
    r""" Return the embedding of standard fields defined by the input.

    INPUT:

    the input tuple ``args`` can be of the following form:

    - ``phi`` -- a morphism of fields  `\phi:K\to L`
    - `(K, L, \phi)` -- `K` and `L` are fields and `\phi` is a morphism of
                        fields defined on an overfield of `K` such that
                        `\phi(K)` is contained in `L`

    Here `K` and `L` must be Sage fields, and `\phi` a Sage morphism.

    EXAMPLES::

        sage: from mclf import *
        sage: k0 = GF(4)
        sage: R.<x> = k0[]
        sage: k1.<a> = k0.extension(x^3+x+1)
        sage: phi = k0.hom(k1)
        sage: embedding_of_standard_fields(phi)
        the embedding of Finite Field in z2 of size 2^2 into Finite Field in z6
        of size 2^6, sending z2 to z2

        sage: embedding_of_standard_fields(GF(2), k0, phi)
        the embedding of Finite Field of size 2 into Finite Field in z2
        of size 2^2, sending 1 to 1

    """
    if len(args) == 1:
        phi = args[0]
        K = standard_field(phi.domain())
        L = standard_field(phi.codomain())
    elif len(args) == 3:
        K = standard_field(args[0])
        L = standard_field(args[1])
        phi = args[2]
    else:
        raise ValueError("input doesn't have the right form")

    if K.is_finite():
        return EmbeddingOfFiniteField(K, L, phi(K.generator()))
    elif K.is_number_field():
        return EmbeddingOfNumberField(K, L, phi(K.generator()))
    elif K.is_function_field():
        phi0 = embedding_of_standard_fields(
            K.constant_base_field(), L.standard_model(), phi)
        if K.is_rational_function_field():
            x = phi(K.generator())
            return EmbeddingOfFunctionField(K, L, [x], phi0)
        else:
            x = phi(K.generators()[0])
            y = phi(K.generators()[1])
            return EmbeddingOfFunctionField(K, L, [x, y], phi0)
    else:
        raise NotImplementedError()


class EmbeddingOfStandardFields(SageObject):
    r""" Base class for an embedding `\phi:K\to L` of standard fields.

    The domain `K` and the codomain `L` may be either a Sage field, i.e.
    objects of the the Sage category ``Fields``, or instance of the class
    :class:`StandardField <mclf.fields.standard_fields.StandardField>`.
    In the former case, `K` and `L` must be in standard form.

    """

    def domain(self):
        r""" Return the domain of this embedding.

        The returned value is a field in standard form.

        """
        return self._domain.standard_model()

    def Domain(self):
        r""" Return the domain of this embedding, as a standard field.

        The returned value is an instance of the class
        :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

        """
        return self._domain

    def codomain(self):
        r""" Return the codomain of this embedding.

        The returned value is a field in standard form.

        """
        return self._codomain.standard_model()

    def Codomain(self):
        r""" Return the codomain of this embedding, as a standard field.

        The returned value is an instance of the class
        :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

        """
        return self._codomain

    def prime_field(self):
        r""" Return the common prime field of domain and codomain of this
        embedding.

        """
        return self.domain().prime_field()

    def applies_to(self, K):
        r""" Returns whether this embedding can be applied to elements of the
        field `K`.

        INPUT:

        - ``K`` -- a standard field

        OUTPUT:

        whether this embedding can be applied to elements of `L`.
        More precisely, this means that this embedding can be applied to the
        coercion `K(a)`, whenever the latter is well defined.

        """
        return self.Domain().contains_as_subfield(K)

    def maps_into(self, L):
        r""" Return whether the image of this embedding can be understood as a
        subfield of `L`.

        INPUT:

        - ``L`` -- a standard field

        OUTPUT:

        whether any result of this embedding can be coerced into `L`.

        Note that `L` may be either a Sage field or an instance of
        :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

        """
        return self.Codomain().is_subfield_of(L)

    def precompose(self, psi):
        r""" Return the composition of `\psi` with this embedding.

        INPUT:

        - ``psi`` -- an embedding `\psi:M\to K` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\phi\circ\psi:M\to L`.

        """
        return psi.post_compose(self)

    def change_coefficients(self, f):
        r""" Return the base change of a polynomial under this embedding.

        INPUT:

        - ``f`` -- a polynomial over the domain of this embedding

        OUTPUT:

        the polynomial over the codomain, obtained by applying this embedding
        to the coefficients of `f`.

        """
        return f.map_coefficients(self, self.codomain())

    def is_standard_simple_extension(self):
        r""" Return whether this embedding is the standard form of a finite
        simple extension.

        A positive answer means that the *original model* `M` of the extension
        field `L` of this embedding `\phi:K\to L` is a finite simple extension
        of `K`.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K.<alpha> = NumberField(x^2+2)
            sage: phi = embedding_of_standard_fields(QQ.hom(K))
            sage: phi.is_standard_simple_extension()
            True

        """
        K = self.domain()           # this is the base field as a bare field
        L = self.Codomain()
        M = L.original_model()
        return (hasattr(M, "base_field") and hasattr(M, "polynomial")
                and M.Domain() is K)

    # the following methods have to be implemented by the appropriate subclass

    def __call__(self):
        raise NotImplementedError()

    def post_compose(self, psi):
        raise NotImplementedError()

    def inverse(self):
        raise NotImplementedError()

    def is_finite(self):
        raise NotImplementedError()

    def finite_extension(self):
        raise NotImplementedError()

    def common_subfield(self):
        r""" Return a common subfield of the domain and codomain
        of this embedding.

        Let `\phi:K\to L` denote this embedding.

        OUTPUT:

        A triple `(L_0, s, t)`, where

        .. TODO::

            Provide a precise description of the desired result.
            It is used in
            ``standard_model_of_finite_extension_of_function_fields``,
            so maybe we only need it for function fields.

        """
        raise NotImplementedError()


class EmbeddingOfFiniteField(EmbeddingOfStandardFields):
    r""" Return an embedding of a finite field into another field.

    INPUT:

    - ``K``, ``L`` -- fields, where `K` is finite
    - ``a`` -- an element of `L`

    The fields `K,L` must be given as objects of the class
    :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

    OUTPUT:

    the unique embedding `\phi:K\to L` sending the standard generator of `K`
    to `a\in L`.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, a):

        from sage.categories.fields import Fields
        if K in Fields:
            assert K.is_finite()
            K = standard_field(K)
            a = K(a)
        else:
            assert isinstance(K, StandardFiniteField)
        if L in Fields:
            L = standard_field(L)
        else:
            assert isinstance(L, StandardField)

        assert K.polynomial()(a).is_zero()
        self._domain = K
        self._codomain = L
        self._image_of_generator = a

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.domain().gen(),
            self.image_of_generator())

    def image_of_generator(self):
        return self._image_of_generator

    def __call__(self, a):
        r""" Return the value of this embedding on the element `a`.

        INPUT:

        - ``a`` -- an element of the domain `K` of this embedding

        If `a` is an element of the original model of `K`, we corce it into
        the standard model.

        OUTPUT:

        the element `\phi(a)\in L`, where `\phi:K\to L` is this embedding.

        """
        # this may lead to an infinite loop; is it necessary?
        # a = self(a)
        return self.Domain().as_polynomial(a)(self.image_of_generator())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`.

        """
        assert self.image_of_generator() in psi.domain(), (
            "im_gen = {} is no in {}".format(
                self.image_of_generator(), psi.domain()))
        a = psi(self.image_of_generator())
        return EmbeddingOfFiniteField(self._domain, psi._codomain, a)

    def inverse(self):
        r""" Return the inverse of this embedding of finite fields.

        If ``self`` is not invertible, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_finite_field(4)
            sage: phi = K.hom(K, K.generator()+1)
            sage: phi.inverse()
            the embedding of Finite Field in z2 of size 2^2 into Finite Field
            in z2 of size 2^2, sending z2 to [z2 + 1]

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        assert K.cardinality() == L.cardinality(), (
            "the embedding is not invertible")
        alpha = L.generator()
        f = L.polynomial()
        for beta in K.roots(f):
            if phi(beta) == alpha:
                return L.hom(K, [beta])
        # if we get here, something went wrong
        raise AssertionError()


class EmbeddingOfNumberField(EmbeddingOfStandardFields):
    r""" Return an embedding of a number field into another field.

    INPUT:

    - ``K``, ``L`` -- standard fields, where `K` is a number field
    - ``a`` -- an element of `L`

    Here `K` and `L` must be either Sage fields in standard form, or instances
    of :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

    OUTPUT:

    the unique embedding `\phi:K\to L` sending the standard generator of `K`
    to `a\in L`.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, a):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_field(K)
        assert isinstance(K, StandardNumberField)
        if L in Fields:
            L = standard_field(L)
            a = L(a)
        assert K.polynomial()(a).is_zero()
        self._domain = K
        self._codomain = L
        self._image_of_generator = a

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.Domain().generator(),
            self.image_of_generator())

    def image_of_generator(self):
        return self._image_of_generator

    def __call__(self, a):
        r""" Return the value of this embedding on the element `a`.

        INPUT:

        - ``a`` -- an element of the domain `K` of this embedding

        OUTPUT:

        the element `\phi(a)\in L`, where `\phi:K\to L` is this embedding.

        """
        return self.Domain().as_polynomial(a)(self.image_of_generator())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`.

        """
        assert self.codomain() is psi.domain(), (
            "the codomain of self and the domain of psi must be equal")
        a = psi(self.image_of_generator())
        return EmbeddingOfNumberField(self._domain, psi._codomain, a)

    def inverse(self):
        r""" Return the inverse of this embedding of number fields.

        If ``self`` is not invertible, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^2-2, "a")
            sage: phi = K.hom(K, -K.generator())
            sage: phi.inverse()
            the embedding of Number Field in a with defining polynomial x^2 - 2
            into Number Field in a with defining polynomial x^2 - 2,
            sending a to -a

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        alpha = L.generator()
        f = L.polynomial()
        for beta in K.roots(f):
            if phi(beta) == alpha:
                return L.hom(K, beta)
        # if we get here, phi is not invertible
        raise ValueError("phi is not invertible")


class EmbeddingOfFunctionField(EmbeddingOfStandardFields):
    r""" Return an embedding of a function field into another function field.

    INPUT:

    - ``K``, ``L`` -- function fields
    - ``image_of_gens`` -- a list of elements of `L`
    - ``phi0`` -- an embedding of standard fields

    Here ``image_of_gens`` must contain exactly one element if `K` is a
    rational function field, and exactly two elements otherwise.

    It is assumed that `\phi_0:k\to l` is an embedding of the constant base
    field `k` of `K` into a subfield of `L` (which may not be equal to the
    constant base field).

    OUTPUT:

    the unique embedding `\phi:K\to L` restricting to `\phi_0` on `k` and
    sending the standard generators of `K` to the elements of
    ``image_of_gens``.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, image_of_gens, phi0):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_function_field(K)
        else:
            assert isinstance(K, StandardFunctionField)
        if L in Fields:
            L = standard_function_field(L)
        else:
            assert isinstance(L, StandardFunctionField)
        image_of_gens = [L(a) for a in image_of_gens]
        if isinstance(phi0, EmbeddingOfStandardFields):
            # assert K.constant_base_field().is_subring(phi0.domain())
            # assert phi0.codomain().is_subring(L.standard_model())
            assert phi0.applies_to(K.constant_base_field())
            assert phi0.maps_into(L)
        else:
            assert phi0.domain() is K.constant_base_field()
            assert phi0.codomain().is_subring(L.standard_model())
            phi0 = embedding_of_standard_fields(phi0)

        self._domain = K
        self._codomain = L
        self._embedding_of_constant_base_field = phi0

        if K.is_rational_function_field():
            assert len(image_of_gens) == 1, "K is a rational function field,\
                so image_of_gens must have exactly one element"
            self._image_of_generators = [image_of_gens[0]]
        else:
            f = K.polynomial(bivariate=True).map_coefficients(
                phi0, L.standard_model())
            assert len(image_of_gens) == 2, "K is not a rational function\
                field, so image_of_gens must have exactly two elements"
            x = image_of_gens[0]
            y = image_of_gens[1]
            assert f(x, y).is_zero()
            self._image_of_generators = [x, y]

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.Domain().generators(),
            self.image_of_generators())

    def image_of_generators(self):
        return self._image_of_generators

    def embedding_of_constant_base_field(self):
        return self._embedding_of_constant_base_field

    def __call__(self, f):
        r""" Return the value of this embedding on the element `f`.

        INPUT:

        - ``f`` -- an element of the domain `K` of this embedding

        OUTPUT:

        the element `\phi(f)\in L`, where `\phi:K\to L` is this embedding.

        """
        K = self.Domain()
        L = self.Codomain()
        phi0 = self.embedding_of_constant_base_field()
        if K.is_rational_function_field():
            f = K(f)
            num = f.numerator().map_coefficients(phi0, L.standard_model())
            denom = f.denominator().map_coefficients(phi0,
                                                     L.standard_model())
            x = self.image_of_generators()[0]
            return num(x)/denom(x)
        else:
            num, denom = K.as_rational_function(f)
            num = num.map_coefficients(phi0, L.standard_model())
            denom = denom.map_coefficients(phi0, L.standard_model())
            return num(self.image_of_generators())/denom(
                self.image_of_generators())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of function fields.

        Here `\phi:K\to L` is this embedding. The embedding `\psi` may be
        given as a Sage morphism, or as an instance of
        :class:`EmbeddingOfStandardFields`.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`, as an instance of
        :class:`EmbeddingOfFunctionField`.

        """
        # we don't perform any explicit consistency check; the composition
        # is well defined if the following commands do not produce an error.
        tau0 = self.embedding_of_constant_base_field().post_compose(psi)
        image_of_gens = [psi(a) for a in self.image_of_generators()]
        return EmbeddingOfFunctionField(self.Domain(), psi.codomain(),
                                        image_of_gens, tau0)

    def inverse(self):
        r""" Return the inverse of this embedding of function fields.

        If ``self`` is not invertible, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<a> = QQ[]
            sage: k.<a> = NumberField(a^2+1)
            sage: A.<x,y> = k[]
            sage: F = standard_function_field(x^4+y^4+1)
            sage: x, y = F.generators()
            sage: phi = F.hom(F , [-a*y, a*x])
            sage: phi.inverse()
            the embedding of Function field in y defined by y^4 + x^4 + 1 into
            Function field in y defined by y^4 + x^4 + 1,
            sending [x, y] to [-a*y, a*x]

        """
        return self.inverse_on_subfield(self.codomain())

    def inverse_on_subfield(self, M):
        r""" Return a right inverse to this embedding, defined on a subfield.

        INPUT:

        - ``M`` -- a subfield of `L`, where `\phi_K\to L` is this embedding.


        OUTPUT:

        An embedding `\psi:M\to K` such that `\phi\circ\psi:M\to L`
        is the canonical embedding of the subfield `M\subset L`.

        We actually demand that `M\subset L` is a *natural subfield*. Since
        `L` is a function field, with standard model `k(x)[y\mid f(y)=0]`,
        `M` must be equal to `k`,  `L_0:=k(x)` or `L`.

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        k = L.constant_base_field()
        L0 = L.rational_base_field()
        if M is k:
            # k must be GF(q) or an absolute number field
            if k.is_prime_field():
                return embedding_of_standard_fields(k.hom(K.standard_model()))
            else:
                alpha = k.generator()
                f = k.polynomial()
                for beta in K.roots(f):
                    if phi(beta) == alpha:
                        return k.hom(K, beta)
                # if we get here, the partial inverse does not exist
                raise ValueError("the partial inverse does not exist")
        elif M is L0:
            psi0 = phi.inverse_on_subfield(k)
            if K.is_rational_function_field():
                x = phi(K.generator())
                g = L.as_polynomial(x)
                # we have x = g(y), where L=L0[y].
                # By assumption, x is in L0, so g must be constant
                assert g.degree() == 1, "the partial inverse does not exist"
                beta = -g[0]/g[1]
                psi = L0.hom([beta], base_map=psi0)
                assert psi(x) == K.generator(), "something went wrong!"
                return embedding_of_standard_fields(psi)
            else:
                t = L0.generator()       # we have L0=k(t)
                x = K.generator()        # we have K/k0(x)
                x1 = phi(x)
                f = L.algebraic_relation(x1, t)
                # now f(phi(x), t) = 0
                f_K = f.map_coefficients(psi0, K.standard_model())
                _, T = f_K.parent().gens()
                g = f_K(K.generator(), T).polynomial(T)
                # now g(alpha) = 0 if phi(alpha)=t
                roots_of_g = K.roots(g)
                for alpha in roots_of_g:
                    if phi(alpha) == t:
                        # we define psi:L0-->K st psi(t)=alpha
                        psi = L0.hom(K, alpha, psi0)
                        assert psi(x1) == K.generator(
                        ), "something went wrong!"
                        return embedding_of_standard_fields(psi)
                # if we get here, something went wrong
                raise AssertionError("could not find the correct root of g")
        elif M is L.standard_model():
            psi0 = phi.inverse_on_subfield(L0)
            alpha = L.generator()
            f = L.polynomial().map_coefficients(psi0, K.standard_model())
            roots_of_f = K.roots(f)
            for beta in roots_of_f:
                if phi(beta) == alpha:
                    return L.hom(K, [beta], psi0)
            # if we get here, the partial inverse does not exist
            raise ValueError("the partial inverse does not exist")
        else:
            raise ValueError("M is not a natural subfield of the codomain L")
