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

# -------------------------------------------------------------------------

#                     constructor functions


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


def natural_embedding(K, L):
    r""" Return the natural inclusion of a standard field into an overfield.

    INPUT:

    - ``K``, ``L`` -- standard fields

    It is assumed that `K` is a natural subfield of `L`. If not, an error
    is raised.

    OUTPUT:

    the natural embedding `K\hookrightarrow L`, as an instance of the class
    :class:`NaturalEmbedding`.

    Let `L` be a standard field. Its **natural subfields** are the following:

    - the prime subfield of `L`
    - the field `L` itself
    - if `L` is a function field:

        * the constant base field of `L`
        * the rational base field of `L`

    Of course, these possibilities are *not* mutually exclusive.

    So `K` has to be one of the above fields.

    """
    if not isinstance(K, StandardField):
        K = standard_field(K)
    if not isinstance(L, StandardField):
        L = standard_field(L)
    # the embedding of a natural subfield of a standard fiel is
    # actually done by the correpsonding method of the field itself.
    if L.prime_subfield().is_equal(K):
        return L.embedding_of_prime_subfield()
    elif L.is_equal(K):
        return L.identity()
    elif L.is_function_field() and L.constant_base_field().is_equal(K):
        return L.embedding_of_constant_base_field()
    elif L.is_function_field() and L.rational_base_field().is_equal(K):
        return L.embedding_of_rational_base_field()
    else:
        raise TypeError("K is not a natural subfield of L")


def identity_embedding(K):
    r""" Return the identity embedding of a standard field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the identity morphism `K\to K`, as an instance of the class
    :class:`IdentityEmbedding()`, subclass of
    :class:`EmbeddingOfStandardFields`

    EXAMPLES::

        sage: from mclf import *
        sage: K = standard_field(QQ)
        sage: id_K = identity_embedding(K); id_K
        the identity map on Rational Field
        sage: id_K.Domain()
        Rational Field as a standard field
        sage: id_K(5)
        5
        sage: id_K.inverse()
        the identity map on Rational Field
        sage: x = K.polynomial_generator("x")
        sage: L = standard_number_field(x^2 - 2, "a")
        sage: id_L = identity_embedding(L)
        sage: iota = K.hom(L)
        sage: id_K.post_compose(iota)
        the embedding of Rational Field into Number Field in a with
        defining polynomial x^2 - 2, sending 1 to 1
        sage: id_L.precompose(iota)
        the embedding of Rational Field into Number Field in a with
        defining polynomial x^2 - 2, sending 1 to 1

    """
    if not isinstance(K, StandardField):
        K = standard_field(K)
    # the identity morphism was aleady created with the standard field K;
    # we don't have to do that again
    # not that therefore, the initialization of StandardField *must not*
    # use this function!!
    return K.identity()

# --------------------------------------------------------------------------


class EmbeddingOfStandardFields(SageObject):
    r""" Base class for an embedding `\phi:K\to L` of standard fields.

    For creating an instance of this class one can use the function
    :func:`embedding_of_standard_fields`.

    The actual initialization will be done by the appropriate subclass.

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

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        K = self.Domain()
        L = self.Codomain()
        return K.is_equal(L) and all(self(a) == a for a in K.generators(
            include_constant_base_field=True))

    def is_canonical_embedding(self):
        r""" Return whether this embedding is the natural inclusion of its
        domain as a subfield of its subdomain.

        """
        K = self.Domain()
        L = self.Codomain()
        return K.is_subfield_of(L) and all(self(a) == a for a in K.generators(
            include_constant_base_field=True))

    def is_injective(self):
        r""" Return whether this embedding is injective.

        Since the domain is field, it is automatically injective, so this
        method always returns ``True``.

        """
        return True

    def is_invertible(self):
        r""" Return whether this embedding is invertible, i.e. an isomorphism.

        This is equivalent to :meth:`is_surjective`.

        """
        return self.is_surjective()

    def is_equal(self, psi):
        r""" Return whether this embedding is equal to another one.

        """
        assert isinstance(psi, EmbeddingOfStandardFields)
        phi = self
        if (phi.Domain().is_equal(psi.Domain())
                and phi.Codomain().is_equal(psi.Codomain())):
            gens = phi.Domain().generators(include_constant_base_field=True)
            return all(phi(a) == psi(a) for a in gens)
        else:
            return False

    def is_finite_extension(self):
        r""" Return whether the codomain of this embedding is a finite
        extension of the image.

        """
        K = self.Domain()
        L = self.Codomain()
        if K.is_finite():
            return L.is_finite()
        elif K.is_number_field():
            return L.is_number_field()
        elif K.is_function_field():
            return True
        else:
            raise NotImplementedError()

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

        Here `L` must be an instance of
        :class:`StandardField <mclf.fields.standard_fields.StandardField>`.

        """
        return L.contains_as_subfield(self.Codomain())

    def precompose(self, psi):
        r""" Return the composition of `\psi` with this embedding.

        INPUT:

        - ``psi`` -- an embedding `\psi:M\to K` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\phi\circ\psi:M\to L`.

        """
        return psi.post_compose(self)

    def change_coefficients(self, f, codomain=None):
        r""" Return the base change of a polynomial under this embedding.

        INPUT:

        - ``f`` -- a polynomial over the domain of this embedding
        - ``codomain`` -- a standard field (default: ``None``)

        If ``codomain`` is given, it must be a standard field containing
        the codomain of this embedding as a subfield.

        OUTPUT:

        the polynomial over the codomain, obtained by applying this embedding
        to the coefficients of `f`.

        """
        if codomain is None:
            codomain = self. codomain()
        else:
            assert isinstance(codomain, StandardField)
            codomain = codomain.standard_model()
        return f.map_coefficients(self, codomain)

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

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        """
        raise NotImplementedError()

    def inverse(self):
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


class NaturalEmbedding(EmbeddingOfStandardFields):
    r""" Base class for natural embedding of a subfield of a standard field.

    A standard field `K` has the following **natural subfields**:

    - the prime subfield
    - the field `K` itself
    - if `K` is a function field:

        * the constant base field
        * the rational base field

    If `K_0\subset K` is one of the above, the inclusion morphism
    `K_0\hookrightarrow K` is represented by an instance of the appropriate
    subclass of this base class.

    .. NOTE::

        The initialization is done by the subclass. It is important that these
        initializations are called only once, by the initialization process
        of the standard field `K`, and by no other function.

    """

    def __repr__(self):
        return "the natural embedding of {} into {}".format(self.domain(),
                                                            self.codomain())

    def is_canonical_embedding(self):
        r""" Return whether this embedding is the natural inclusion of its
        domain as a subfield of its subdomain.

        """
        return True

    def __call__(self, a):
        r""" Return the value of this embedding on an element of the domain.

        """
        assert self.Domain().contains_as_subfield(a.parent()), "the element\
            a does not coerce into the domain of this map"
        return self.Codomain()(a)


class IdentityEmbedding(NaturalEmbedding):
    r""" Return the identity embedding of a standard field.

    INPUT:

    ``K`` -- a standard field

    `K` must be given as an instance of :class:`StandardField`

    OUTPUT:

    the identity morphism on `K`, as an instance of the class
    :class:`EmbeddingOfStandardFields`.

    .. NOTE::

        The initialization of this class must be called *only* during
        the initialization of the standard field `K`. At this moment,
        the instance `K` of
        :class:`StandardField <mclf.fields.standard_fields.StandardField>`
        already exist, the identity map is created (with input `K`) and then
        we attach this map to ``K._identity``.

    """

    def __init__(self, K):
        assert isinstance(K, StandardField)
        self._domain = K
        self._codomain = K

    def __repr__(self):
        return "the identity map on {}".format(self.domain())

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        return True

    def is_finite_extension(self):
        r""" Return whether the codomain of this embedding is a finite
        extension of the image.

        """
        return True

    def precompose(self, psi):
        r""" Return the composition of `\psi` with the identity map.

        INPUT:

        - ``psi`` -- an embedding `\psi:M\to K` of standard fields.

        Here `K` is the domain and codomain of this identity map.

        OUTPUT:

        the embedding `\psi\circ\psi:M\to K` itself.

        """
        assert psi.maps_into(self.Domain())
        return psi

    def change_coefficients(self, f):
        r""" Return the base change of a polynomial under this identity map.

        INPUT:

        - ``f`` -- a polynomial over the domain of this identity map.

        OUTPUT:

        the polynomial `f` itself.

        """
        assert self.Domain().contains_as_subfield(f.base_ring())
        return f

    def is_standard_simple_extension(self):
        r""" Return whether this identity map is the standard form of a finite
        simple extension.

        The answer is yes.
        """
        return True

    def __call__(self, a):
        r""" Return the value of this identity map on an element of the domain.

        """
        assert self.Domain().contains_as_subfield(a.parent()), "the element\
            a does not coerce into the domain of this map"
        return self.Domain()(a)

    def post_compose(self, psi):
        assert self.maps_into(psi.Domain())
        return psi

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        """
        return True

    def inverse(self):
        return self

    def finite_extension(self):
        raise NotImplementedError()


class EmbeddingOfPrimeSubfield(NaturalEmbedding):
    r""" Return the embedding of the prime subfield of a standard field.

    INPUT:

    ``K`` -- a standard field

    `K` must be given as an instance of :class:`StandardField`

    OUTPUT:

    the embedding `K_0\hookrightarrow K` of the prime subfield `K_0` of `K`,
    as an instance of the class :class:`EmbeddingOfStandardFields`.

    .. NOTE::

        The initialization of this class must be called *only* by the method
        :meth:`embedding_of_prime_subfield <mclf.fields.standard_fields.\
        StandardField.embedding_of_prime_subfield>` of the standard field `K`.

        this guarantiees that no unneccessary copies of the embdding float
        around.

    """

    def __init__(self, K):
        assert isinstance(K, StandardField)
        from mclf.fields.standard_fields import standard_prime_field
        self._domain = standard_prime_field(K.characteristic())
        self._codomain = K

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        return self.Codomain().is_prime_field()

    def post_compose(self, psi):
        r""" Return the composition of this embedding with another one.

        INPUT:

        - ``\psi`` -- an embedding `\psi:K\to L` of standard fields

        Here `K` is the field of which this is the embedding of the prime
        subfield.

        OUTPUT:

        The embedding of the prime subfield into `L`.

        """
        assert self.maps_into(psi.Domain())
        return psi.Codomain().embedding_of_prime_subfield()

    def precompose(self, psi):
        r""" Return the composition of `\psi` with the identity map.

        INPUT:

        - ``psi`` -- an embedding `\psi:M\to K_0` of standard fields.

        Here `K_0` is the prime subfield being embedded into its overfield.

        OUTPUT:

        this embedding itself (as `\psi` is necessarily the identity map).

        """
        assert psi.maps_into(self.Domain())
        return self

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        """
        return self.Codomain().is_prime_field()

    def inverse(self):
        if self.is_identity():
            return self
        else:
            raise AssertionError("This embedding is not invertibel")

    def finite_extension(self):
        raise NotImplementedError()


class EmbeddingOfConstantBaseField(NaturalEmbedding):
    r""" Return the embedding of the constant base field of a standard
    function field.

    INPUT:

    ``K`` -- a standard function field

    `K` must be given as an instance of :class:`StandardFunctionField \
    <mclf.fields.standard_fields.StandardFunctionField>`.

    OUTPUT:

    the embedding `k\hookrightarrow K` of the constant base field `k` of `K`,
    as an instance of the class :class:`EmbeddingOfStandardFields`.

    .. NOTE::

        The initialization of this class must be called *only* by the method
        :meth:`embedding_of_constant_base_field <mclf.fields.standard_fields.\
        StandardFunctionField.embedding_of_constant_base_field>` of the
        standard function field `K`.

        This guarantees that no unneccessary copies of the embdding float
        around.

    """

    def __init__(self, K):
        from mclf.fields.standard_fields import (standard_prime_field,
                                                 StandardFunctionField)
        assert isinstance(K, StandardFunctionField)
        self._domain = standard_field(
            K.standard_model().constant_base_field())
        self._codomain = K

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        return False

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        """
        return False

    def inverse(self):
        raise AssertionError("This embedding is not invertibel")

    def finite_extension(self):
        raise NotImplementedError()


class EmbeddingOfRationalBaseField(NaturalEmbedding):
    r""" Return the embedding of the rational base field of a standard
    function field.

    INPUT:

    ``K`` -- a standard function field, which is *not* a rational function
             field

    `K` must be given as an instance of :class:`StandardFunctionField \
    <mclf.fields.standard_fields.StandardFunctionField>`.

    OUTPUT:

    the embedding `K_0\hookrightarrow K` of the rational base field `K_0` of
    `K`, as an instance of the class :class:`EmbeddingOfStandardFields`.

    .. NOTE::

        - The initialization of this class must be called *only* by the method
          :meth:`embedding_of_rational_base_field <mclf.fields.standard_fields.\
          StandardFunctionField.embedding_of_rational_base_field>` of the
          standard function field `K`.

          This guarantees that no unneccessary copies of the embdding float
          around.

        - for a rational function field, the embedding of its rational base
          field is simply the identity map; therefore, we make the assumption
          that `K` is not a rational function field.

    """

    def __init__(self, K):
        from mclf.fields.standard_fields import (standard_field,
                                                 StandardFunctionField)
        assert isinstance(K, StandardFunctionField)
        assert not K.is_rational_function_field(), "K must not be a rational \
            function field"
        self._domain = standard_field(
            K.standard_model().base_field())
        self._codomain = K

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        return False

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        """
        return False

    def inverse(self):
        raise AssertionError("This embedding is not invertibel")

    def finite_extension(self):
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

    def inverse(self, check=False):
        r""" Return the inverse of this embedding of finite fields.

        If ``self`` is not invertible, an error is raised - unless ``check``
        is ``True``; then we return ``None``.

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

    def is_surjective(self):
        r""" Return whether this embedding of a finite field is surjective.

        """
        K = self.Domain()
        L = self.Codomain()
        return L.is_finite() and K.cardinality() == L.cardinality()


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

    def inverse(self, check=False):
        r""" Return the inverse of this embedding of number fields.

        If ``self`` is not invertible, an error is raised - unless ``check``
        is ``True``; then we return ``None``.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^2-2, "a")
            sage: a = K.generator()
            sage: phi = K.hom(K, -a)
            sage: phi.inverse()
            the embedding of Number Field in a with defining polynomial x^2 - 2
            into Number Field in a with defining polynomial x^2 - 2,
            sending a to -a

        We can use the method to test whether an embedding is invertible,
        by using the flag ``check``. ::

            sage: L = K.extension(x^2 - a, "b")
            sage: phi = L.embedding_of_base_field()
            sage: phi.inverse(check=True)

        """
        if check and not self.is_invertible():
            return None
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

    def is_surjective(self):
        r""" Return whether this embedding of a number field is surjective.

        """
        K = self.Domain()
        L = self.Codomain()
        return L.is_number_field() and K.degree() == L.degree()


class EmbeddingOfFunctionField(EmbeddingOfStandardFields):
    r""" Return an embedding of a function field into another function field.

    INPUT:

    - ``K``, ``L`` -- function fields
    - ``image_of_gens`` -- a list of elements of `L`
    - ``phi0`` -- an embedding of standard fields

    OUTPUT:

    the unique embedding `\phi:K\to L`  determined by ``image_gens``
    and ``phi0``.

    The list ``image_of_gens`` may have one element `\alpha\in L` or two
    elements `\alpha,\beta\in L`. The embedding `\phi_0:K_0\to L` is defined
    on a certain subfield `K_0\subset K`, and the resulting embedding `\phi`
    is an extension of `\phi_0` to `K`.

    There are three cases:

    1. `K` is a rational function field `k(x)`. In this case `K_0=k` is the
       constant base field of `K` and ``image_of_gens`` must contain exactly one
       element `\alpha`. The embedding `\phi:K\to L` is the unique extension
       of `\phi_0` such that `\phi(x)=\alpha`.

    2. `K` is a finite simple extension of a rational function `k(x)` (its
       *rational base field*), and ``image_of_gens`` contains exactly one
       element `\alpha`. Then `K_0=k(x)` is the rational base field of `K` and
       `\phi` is the unique extension of `\phi_0` sending the generator of
       `K/K_0` to `\alpha`.

    3. `K` is a finite simple extension of its rational base field `k(x)`,
       and ``image_of_gens`` contains exactly two elements `\alpha, \beta`.
       Then `K_0=k` is the constant base field of `K` and
       `\phi` is the unique extension of `\phi_0` sending `x` to `\alpha` and
       the generator of `K/K_0` to `\beta`.

    If such an embedding `\phi:K\to L` does not exist, an error is raised.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: F0 = standard_rational_function_field(k, "x")
        sage: phi0 = EmbeddingOfFunctionField(F0, F0, [-x], k.hom(F0))

    """

    def __init__(self, K, L, image_of_gens, phi0):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_function_field(K)
        else:
            assert isinstance(K, StandardFunctionField)
        if L in Fields:
            from mclf.fields.standard_fields import standard_function_field
            L = standard_function_field(L)
        else:
            assert isinstance(L, StandardFunctionField)
        image_of_gens = [L(a) for a in image_of_gens]

        self._domain = K
        self._codomain = L

        if not isinstance(phi0, EmbeddingOfStandardFields):
            phi0 = embedding_of_standard_fields(phi0)
        assert phi0.maps_into(L)

        k = K.constant_base_field()
        K0 = K.rational_base_field()

        if len(image_of_gens) == 1 and K.is_rational_function_field():
            assert phi0.applies_to(k), "phi0 is not of the right type"
            alpha = image_of_gens[0]
            self._restriction_to_constant_base_field = phi0
            self._image_of_generator = alpha
            self._image_of_generators = [alpha]
            # no need to test

        elif len(image_of_gens) == 1 and not K.is_rational_function_field():
            assert phi0.applies_to(K0)
            alpha = image_of_gens[0]
            self._restriction_to_constant_base_field = phi0
            self._restriction_to_rational_base_field = phi0
            self._image_of_generator = alpha
            self._image_of_generators = image_of_gens
            # test:
            f = phi0.change_coefficients(K.polynomial(), L)
            try:
                f(alpha)
            except TypeError:
                print("K = ", K)
                print("K0 = ", K0)
                print("phi0 = ", phi0)
                print("alpha = ", alpha)
                print("in ", alpha.parent())
                print("image_of_gens = ", image_of_gens)
                print("f = ", f)
                print()
                raise TypeError()
            assert f(alpha).is_zero(), "the embedding does not exist"

        elif len(image_of_gens) == 2:
            alpha = image_of_gens[0]
            beta = image_of_gens[1]
            assert not K.is_rational_function_field(), "wrong type of input"
            assert phi0.applies_to(k), "phi0 is not of the right type"
            self._restriction_to_constant_base_field = phi0
            phi1 = K0.hom(L, alpha, phi0)
            self._restriction_to_rational_base_field = phi1
            self._image_of_generator = beta
            self._image_of_generators = [alpha, beta]
            # test:
            f = phi1.change_coefficients(K.polynomial())
            assert f(beta).is_zero(), "the embedding does not exist"

        else:
            raise TypeError("wrong number of parameters")

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.Domain().generators(),
            self.image_of_generators())

    def image_of_generators(self):
        return self._image_of_generators

    def restriction_to_constant_base_field(self):
        r""" Return the restriction of this embedding of a function field
        to the constant base field.

        """
        return self._restriction_to_constant_base_field

    def restriction_to_rational_base_field(self):
        r""" Return the restriction of this embedding of a function field
        to the rational base field.

        """
        if self.is_rational_function_field():
            return self
        else:
            return self._restriction_to_rational_base_field

    def __call__(self, f):
        r""" Return the value of this embedding on the element `f`.

        INPUT:

        - ``f`` -- an element of the domain `K` of this embedding

        OUTPUT:

        the element `\phi(f)\in L`, where `\phi:K\to L` is this embedding.

        """
        K = self.Domain()
        L = self.Codomain()
        phi0 = self.restriction_to_constant_base_field()
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

    def inverse(self, check=False):
        r""" Return the inverse of this embedding of function fields.

        If ``self`` is not invertible, then an error is raised, unless
        ``check`` is ``True``, and then we return ``None``.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: k = standard_number_field(x^2 + 1, "a")
            sage: a = k.generator()
            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: F = standard_function_field(x^4+y^4+1)
            sage: x, y = F.generators()
            sage: phi = F.hom(F , [-a*y, a*x])
            sage: phi.inverse()
            the embedding of Function field in y defined by y^4 + x^4 + 1 into
            Function field in y defined by y^4 + x^4 + 1,
            sending [x, y] to [-a*y, a*x]

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        L0 = L.prime_subfield()
        psi0 = L0.hom(K)          # there is a unique map!
        if K.is_prime_field():
            return psi0

        # we lift psi0 step by step
        subfields_of_L = L.natural_subfields()[1:]
        for L1 in subfields_of_L:
            if L1.is_rational_function_field():
                # L1 is the rational base field of L and L0 is the
                # constant base field
                assert L0.is_equal(L.constant_base_field())
                psi = phi.lift_right_inverse_to_rational_base_field(psi0)
            else:
                # L1/L0 is finite, alpha is a generator with minpoly f
                psi = phi.lift_right_inverse_to_finite_simple_extension(
                    psi0, L0, L1)
            if psi is None:
                # there is no right inverse
                if check:
                    return None
                else:
                    raise AssertionError("phi is not invertible")
            else:
                L0 = L1
                psi0 = psi
        # if we get here, psi is the inverse of phi
        assert psi.post_compose(phi).is_identity()
        return psi

    def lift_right_inverse_to_rational_base_field(self, psi0):
        r""" Return a lift of a right inverse of this embedding from the
        constant base field to the rational base field.

        INPUT:

        - ``psi0`` -- an embedding `\psi_0:L_0\to K`, from the constant base
                      field `L_0` of the codomain `L` of this embedding
                      `\phi:K\to L` to the domain `K`

        It is assumed that `\psi_0` is a right inverse of `\phi`, i.e. the
        composition `\phi\circ\psi_0:L_0\to L` is the canonical embedding.

        OUTPUT:

        A lift `\psi:L_1\to K` of `\psi_0` the the rational base field
        `L_1` of `L`, which is also a right inverse of `\phi`.

        If no such lift exist, we return ``None``.

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        L0 = L.constant_base_field()
        L1 = L.rational_base_field()
        t = L1.generator()
        x = K.generators()[0]
        x1 = phi(x)
        f = L.algebraic_relation(x1, t)
        f_K = psi0.change_coefficients(f)
        # we have f(phi(x), t) = 0
        # if there is beta in K such that phi(beta) = t, then we would have
        # f_K(x, beta) = 0; this leaves only finitely many possibilities
        # for beta
        _, T = f_K.parent().gens()
        g = f_K(x, T).univariate_polynomial()
        for beta in K.roots(g):
            if phi(beta) == t:
                psi = L1.hom(K, beta, psi0)
                assert psi.post_compose(phi).is_equal(L1.embedding())
                return psi
        # if we get here, the right inverse psi does not exist
        return None

    def lift_right_inverse_to_finite_simple_extension(self, psi0, L0, L1):
        r""" Return a lift of a right inverse of this embedding along a finite
        simple extension of subfields.

        INPUT:

        - ``psi0`` -- an embedding `\psi_0:L_0\to K`, from the constant base
                      field `L_0` of the codomain `L` of this embedding
                      `\phi:K\to L` to the domain `K`,
        - ``L0`` -- the domain of `\psi_0`, as a natural subfield of `L`,
        - ``L1`` -- the natural subfield of `L` above `L_0` such that
                    `L_1/L_0` is a finite simple extension,

        It is assumed that `\psi_0` is a right inverse of `\phi`, i.e. the
        composition `\phi\circ\psi_0:L_0\to L` is the canonical embedding.

        OUTPUT:

        A lift `\psi:L_1\to K` of `\psi_0` from `L_0` to the rational base
        field `L_1` of `L`, which is also a right inverse of `\phi`.

        If no such lift exist, we return ``None``.

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        alpha = L(L1.generator())
        f = L1.polynomial()
        f_K = psi0.change_coefficients(f)
        for beta in K.roots(f_K):
            if phi(beta) == alpha:
                psi1 = L1.hom(K, beta, psi0)
                assert psi1.post_compose(phi).is_equal(L1.embedding())
                return psi1
        # if we get here, there is no right inverse
        return None

    def inverse_on_subfield(self, M, check=False):
        r""" Return a right inverse to this embedding, defined on a subfield.

        INPUT:

        - ``M`` -- a subfield of `L`, where `\phi_K\to L` is this embedding.
        - ``check`` -- a boolean (default: ``False``)


        OUTPUT:

        An embedding `\psi:M\to K` such that `\phi\circ\psi:M\to L`
        is the canonical embedding of the subfield `M\subset L`.

        We actually demand that `M\subset L` is a *natural subfield*. Since
        `L` is a function field, with standard model `k(x)[y\mid f(y)=0]`,
        `M` must be equal to `k`,  `L_0:=k(x)` or `L`.

        If there is no right inverse `\psi` then an error is raise - unless
        ``check`` is ``True``; then we return ``None``.

        """
        phi = self
        K = phi.Domain()
        L = phi.Codomain()
        k = L.constant_base_field()
        L0 = L.rational_base_field()
        from mclf.fields.standard_subfields import (StandardSubfield,
                                                    standard_subfield)
        if not isinstance(M, StandardSubfield):
            M = standard_subfield(M, L)

        if M.is_equal(k):
            # M is the constant base field k of L
            # k must be GF(q) or an absolute number field
            if k.is_prime_field():
                return k.inclusion(K)
            else:
                alpha = k.generator()
                f = k.polynomial()
                for beta in K.roots(f):
                    if phi(beta) == alpha:
                        return k.hom(K, beta)
                # if we get here, the partial inverse does not exist
                if check:
                    # if we return None we signal that the map is not
                    # invertible
                    return None
                else:
                    raise ValueError("the partial inverse does not exist")
        elif M.is_equal(L0):
            # M is the rational base field L0 of L
            psi0 = phi.inverse_on_subfield(k, check)
            if K.is_rational_function_field():
                x = phi(K.generator())
                # warning: this does not make sense if L is also a rational
                # function field
                g = L.as_polynomial(x)
                # we have x = g(y), where L=L0[y].
                # By assumption, x is in L0, so g must be constant
                if not g.degree() == 1:
                    if check:
                        return None
                    else:
                        raise AssertionError(
                            "the partial inverse does not exist")
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
                if check:
                    return None
                else:
                    raise AssertionError("the inverse does not exist")
        elif M is L.standard_model():
            psi0 = phi.inverse_on_subfield(L0, check)
            alpha = L.generator()
            f = L.polynomial().map_coefficients(psi0, K.standard_model())
            roots_of_f = K.roots(f)
            for beta in roots_of_f:
                if phi(beta) == alpha:
                    return L.hom(K, [beta], psi0)
            # if we get here, the partial inverse does not exist
            if check:
                return None
            else:
                raise ValueError("the partial inverse does not exist")
        else:
            raise ValueError("M is not a natural subfield of the codomain L")

    def is_surjective(self):
        r""" Return whether this embedding of function fields is surjective.

        """
        if self.is_canonical_embedding():
            return self.Domain().is_equal(self.Codomain())
        else:
            # for the moment, we know of no better way that trying to
            # compute the inverse
            inverse = self.inverse()
            return inverse is not None
