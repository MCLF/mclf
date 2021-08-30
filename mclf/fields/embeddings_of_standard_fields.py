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

    phi(a)


Subclasses, initialization and inheritance
------------------------------------------

The base class :class:`EmbeddingOfStandardFields` can not be initialized
directly. Almost all general methods are already implemented at this level,
except for:

- :meth:`__call__ <EmbeddingOfStandardFields.__call__>`,
- :meth:`post_compose <EmbeddingOfStandardFields.post_compose>`,
- :meth:`is_surjective <EmbeddingOfStandardFields.is_surjective>`,
- :meth:`inverse <EmbeddingOfStandardFields.inverse>`.

The following three subclasses are adapted to the type of the *domain* of the
embedding:

- :class:`EmbeddingOfFiniteField`
- :class:`EmbeddingOfNumberField`
- :class:`EmbeddingOfFunctionField`

Furthermore, we have a subclass :class:`NaturalEmbedding` whose instances
represent the natural embedding of a subfield into its overfield. It has the
following subclasses:

- :class:`IdentityEmbedding`
- :class:`EmbeddingOfPrimeSubfield`
- :class:`EmbeddingOfConstantBaseField`
- :class:`EmbeddingOfRationalBaseField`



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
                                         StandardNumberField)
from mclf.fields.standard_function_fields import StandardFunctionField

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
        of size 2^6, sending z2 to z6^3 + z6^2 + z6 + 1


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

    The actual initialization and the following methods have to be implemented
    by the appropriate subclass:

    - :meth:`__call__ <EmbeddingOfStandardFields.__call__>`,
    - :meth:`post_compose <EmbeddingOfStandardFields.post_compose>`,
    - :meth:`is_surjective <EmbeddingOfStandardFields.is_surjective>`,
    - :meth:`inverse <EmbeddingOfStandardFields.inverse>`.

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

    def sage_morphism(self):
        r""" Return the sage morphism of this embedding.

        """
        if not hasattr(self, "_sage_morphism"):
            raise NotImplementedError()
        return self._sage_morphism

    def is_identity(self):
        r""" Return whether this embedding is the identity on its domain.

        """
        K = self.Domain()
        L = self.Codomain()
        return K.is_equal(L) and all(self(a) == a
                                     for a in K.absolute_generators())

    def is_canonical_embedding(self):
        r""" Return whether this embedding is the natural inclusion of its
        domain as a subfield of its subdomain.

        """
        K = self.Domain()
        L = self.Codomain()
        return K.is_subfield_of(L) and all(self(a) == a
                                           for a in K.absolute_generators())

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
            gens = phi.Domain().absolute_generators()
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

        EXAMPLES::

            sage: from mclf import *
            sage: K0.<x> = FunctionField(QQ)
            sage: R.<y> = K0[]
            sage: K1.<y> = K0.extension(y^2-x^3)
            sage: R.<z> = K1[]
            sage: K2.<z> = K1.extension(z^2+y+x)
            sage: S.<T> = K2[]
            sage: f = T^2 + x*T + y
            sage: K = standard_field(K2)
            sage: phi = K.hom(K, -K.generator())
            sage: phi.change_coefficients(f)
            T^2 + x*T - z^2 - x

        """
        assert self.applies_to(f.base_ring()), ("{} does not apply to the \
            base ring of {0}, which is {}".format(self, f, f.base_ring()))
        if codomain is None:
            return f.map_coefficients(self, self.codomain())
        else:
            assert isinstance(codomain, StandardField)
            try:
                f = f.map_coefficients(self, self.codomain())
            except TypeError:
                print("f = ", f)
                print("in ", f.parent())
                print("self = ", self)
                raise AssertionError()
            return codomain.change_coefficients(f)

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
                and M.base_field() == K)

    # the following methods have to be implemented by the appropriate subclass

    def __call__(self):
        r""" Evaluate this embedding on an element of the domain.

        This method must be implemented by the every terminal subclass.
        """
        raise NotImplementedError()

    def post_compose(self, psi):
        r""" Return the composition of this embedding, followed by an another
        embedding:

        This method must be implemented by the every terminal subclass.
        """
        raise NotImplementedError()

    def is_surjective(self):
        r""" Return whether this embedding is surjective.

        This method must be implemented by the every terminal subclass.
        """
        raise NotImplementedError()

    def inverse(self):
        r""" Return the inverse of this embedding.

        If it is not invertible, an error is raised.

        This method must be implemented by the every terminal subclass.
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

    def is_surjective(self):
        r""" Return whether this natural embedding is surjective.

        A natural embedding is surjective (and hence an isomorhism) if and only
        if domain and codoamin are equal.

        """
        return self.Domain().is_equal(self.Codomain())

    def inverse(self):
        r""" Return the inverse of this natural embedding.

        If no inverse exist, an error is raised.

        A natural embedding is invertibel if and only if it is the identity,
        and then the inverse is the embedding itself.

        """
        assert self.is_invertible(), "this natural embedding is not invertible"
        return self

    def post_compose(self, phi):
        r""" Return the composition of this natural embedding with the
        embedding `\phi`.

        """
        try:
            assert self.maps_into(phi.Domain()), "compositon is not well defined"
        except AssertionError:
            print("self.Codomain() = ", self.Codomain())
            print("phi.Domain() = ", phi.Domain())
            assert self.Codomain().is_equal(phi.Domain())
        return self.Domain().hom(phi.Domain()).post_compose(phi)


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
        from mclf.fields.standard_fields import identity_map
        self._sage_morphism = identity_map(K.standard_model())

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
        K0 = standard_prime_field(K.characteristic())
        self._domain = K0
        self._codomain = K
        self._sage_morphism = K0.standard_model().hom(K.standard_model())

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
        return self.Domain().hom(phi.Domain()).post_compose(phi)

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
        from mclf.fields.standard_fields import standard_prime_field
        from mclf.fields.standard_function_fields import StandardFunctionField
        assert isinstance(K, StandardFunctionField)
        k = standard_field(K.standard_model().constant_base_field())
        self._domain = k
        self._codomain = K
        self._sage_morphism = k.standard_model().hom(K.standard_model())

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
        from mclf.fields.standard_fields import standard_field
        from mclf.fields.standard_function_fields import StandardFunctionField
        assert isinstance(K, StandardFunctionField)
        assert not K.is_rational_function_field(), "K must not be a rational \
            function field"
        K0 = standard_field(K.standard_model().base_field())
        self._domain = K0
        self._codomain = K
        self._sage_morphism = K0.standard_model().hom(K.standard_model())

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
        else:
            assert isinstance(K, StandardFiniteField)
        if L in Fields:
            L = standard_field(L)
        else:
            assert isinstance(L, StandardField)

        a = L(a)
        assert K.polynomial()(a).is_zero()
        self._domain = K
        self._codomain = L
        self._image_of_generator = a
        from mclf.fields.standard_fields import homomorphism_on_standard_field
        self._sage_morphism = homomorphism_on_standard_field(
            K.standard_model(), L.standard_model(), a)

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
        return self.Domain().as_polynomial(a)(self.image_of_generator())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`.

        """
        assert self.maps_into(psi.Domain())
        a = psi(self.image_of_generator())
        return EmbeddingOfFiniteField(self.Domain(), psi.Codomain(), a)

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
            in z2 of size 2^2, sending z2 to z2 + 1

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
                return L.hom(K, beta)
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
        from mclf.fields.standard_fields import homomorphism_on_standard_field
        self._sage_morphism = homomorphism_on_standard_field(
            K.standard_model(), L.standard_model(), a)

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

    The list ``image_of_gens`` may have between one to three elements. The
    embedding `\phi_0:K_0\to L` is defined on a certain subfield `K_0\subset K`,
    and the resulting embedding `\phi` is an extension of `\phi_0` to `K`.

    The subfield `K_0` must be the unique natural subfield of `K` such that
    the number of natural generators of `K/K_0` is equal to the number of
    elements of ``image_of_gens``. There are the following possibilities for
    `K_0` and the generators:

    1. `K_0` is the prime field of `K`, and it is a *proper* subfield of the
       constant base field `k` of `K`. Then there are either 2 or 3 generators,
       namely `a, x` or `a, x, y`. Here `a` is the absolute generator of `k`,
       `x` is the generator of the rational base field `k(x)`, and `y` is the
       generator of `K/k(x)` (if `K` is not equal to `k(x)`.
    2. `K_0=k` is the constant base field. Then there are either one or two
       generators, namely `x`, or `x, y`.
    3. `K_0=k(x)` is the rational base field, which is not equal to `K` itself.
       Then there is exactly one generators `y` of `K/K_0`.

    The embedding `\phi:K\to L` is determined as the unique extension of
    `\phi_0` which sends the generators of `K/K_0` to the elements of
    ``image_of_gens``.

    If such an embedding `\phi:K\to L` does not exist, an error is raised.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(4)
        sage: a = k.generator()
        sage: F0 = standard_rational_function_field(k, "x")
        sage: x = F0.generator()
        sage: y = F0.polynomial_generator("y")
        sage: F = F0.extension(y^2 + y + x + a)
        sage: y = F.generator()
        sage: EmbeddingOfFunctionField(F, F, [x + 1, y + a], k.hom(F0))
        the embedding of Function field in y defined by y^2 + y + x + z2
        into Function field in y defined by y^2 + y + x + z2,
        sending [x, y] to [x + 1, y + z2]

        sage: EmbeddingOfFunctionField(F, F, [a + 1, x + 1, y], k.prime_subfield().hom(F))
        the embedding of Function field in y defined by y^2 + y + x + z2
        into Function field in y defined by y^2 + y + x + z2,
        sending [x, y] to [x + 1, y]

    """

    def __init__(self, K, L, image_of_gens, phi0):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_function_field(K)
        else:
            assert isinstance(K, StandardFunctionField)
        if L in Fields:
            from mclf.fields.standard_function_fields import standard_function_field
            L = standard_function_field(L)
        else:
            assert isinstance(L, StandardFunctionField)
        image_of_gens = [L(a) for a in image_of_gens]

        self._domain = K
        self._codomain = L

        if not isinstance(phi0, EmbeddingOfStandardFields):
            phi0 = embedding_of_standard_fields(phi0)
        assert phi0.maps_into(L)

        k0 = K.prime_subfield()
        k = K.constant_base_field()
        K0 = K.rational_base_field()

        if len(image_of_gens) == 1 and K.is_rational_function_field():
            assert phi0.applies_to(k), "phi0 is not of the right type"
            x = image_of_gens[0]
            self._restriction_to_constant_base_field = phi0
            self._image_of_generator = x
            self._image_of_generators = [x]
            # no need to test

        elif len(image_of_gens) == 1 and not K.is_rational_function_field():
            assert phi0.applies_to(K0)
            y = image_of_gens[0]
            self._restriction_to_constant_base_field = phi0
            self._restriction_to_rational_base_field = phi0
            self._image_of_generator = y
            self._image_of_generators = [L(phi0(K0.generator())), y]
            # test:
            f = phi0.change_coefficients(K.polynomial(), L)
            assert f(y).is_zero(), "the embedding does not exist"
            f = phi0.change_coefficients(K.bivariate_polynomial(), L)
            assert f(self.image_of_generators()).is_zero()

        elif len(image_of_gens) == 2:
            if K.is_rational_function_field():
                a = image_of_gens[0]
                x = image_of_gens[1]
                assert not k.is_prime_field(), "wrong number of parameters"
                phi0 = k.hom(L, a)
                self._restriction_to_constant_base_field = phi0
                self._image_of_generator = x
                self._image_of_generators = [x]
                # no need to test
            else:
                x = image_of_gens[0]
                y = image_of_gens[1]
                assert phi0.applies_to(k), "phi0 is not of the right type"
                self._restriction_to_constant_base_field = phi0
                phi1 = K0.hom(L, x, phi0)
                self._restriction_to_rational_base_field = phi1
                self._image_of_generator = y
                self._image_of_generators = [x, y]
                # test:
                f = phi1.change_coefficients(K.polynomial())
                assert f(y).is_zero(), "the embedding does not exist"
        elif len(image_of_gens) == 3:
            assert (not K.is_rational_function_field()
                    and not k.is_prime_field()), "wrong number of parameters"
            a = image_of_gens[0]
            x = image_of_gens[1]
            y = image_of_gens[2]
            phi0 = k.hom(L, a)
            phi1 = K0.hom(L, x, phi0)
            self._restriction_to_constant_base_field = phi0
            self._restriction_to_rational_base_field = phi1
            self._image_of_generator = y
            self._image_of_generators = [x, y]
            # test:
            f = phi1.change_coefficients(K.polynomial())
            assert f(y).is_zero(), "the embedding does not exist"
        else:
            raise TypeError("wrong number of parameters")

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.Domain().generators(),
            self.image_of_generators())

    def sage_morphism(self):
        r"""

        OUTPUT:

        the underlying sage morphism between the standard models of the domain
        and the codomain of this embedding.


        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(9)
            sage: phi0 = k.hom(k, k.generator()^3)
            sage: K1 = standard_rational_function_field(k, "x")
            sage: x = K1.generator()
            sage: phi1 = K1.hom(K1, -x)
            sage: y = K1.polynomial_generator("y")
            sage: K = K1.extension(y^3 - x)
            sage: y = K.generator()
            sage: phi = K.relative_hom(K, -y, phi1)
            sage: psi = phi.sage_morphism()
            sage: phi.is_equal(embedding_of_standard_fields(psi))
            True

        """
        from mclf.fields.standard_fields import homomorphism_on_standard_field
        if not hasattr(self, "_sage_morphism"):
            K = self.domain()
            L = self.codomain()
            phi0 = self.restriction_to_constant_base_field().sage_morphism()
            if self.Domain().is_rational_function_field():
                phi = homomorphism_on_standard_field(K, L,
                                                     self._image_of_generator,
                                                     phi0)
            else:
                K1 = K.base_field()
                phi1 = self.restriction_to_rational_base_field().sage_morphism()
                phi = homomorphism_on_standard_field(K, L,
                                                     self._image_of_generator,
                                                     phi1)
            self._sage_morphism = phi
        return self._sage_morphism

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
        if self.Domain().is_rational_function_field():
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
            num = phi0.change_coefficients(f.numerator(), L)
            denom = phi0.change_coefficients(f.denominator(), L)
            x = self.image_of_generators()[0]
            return num(x)/denom(x)
        else:
            num, denom = K.as_rational_function(f)
            num = phi0.change_coefficients(num, L)
            denom = phi0.change_coefficients(denom, L)
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

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(4)
            sage: phi0 = k.hom(k, k.generator()+1)
            sage: K = standard_rational_function_field(k, "x")
            sage: x = K.generator()
            sage: L = standard_rational_function_field(k, "y")
            sage: y = L.generator()
            sage: phi = K.hom(L, y^2 + 1, phi0)
            sage: psi = L.hom(K, x - 1)
            sage: phi.post_compose(psi)
            the embedding of Rational function field in x over Finite Field
            in z2 of size 2^2 into Rational function field in x over Finite
            Field in z2 of size 2^2, sending [x] to [x^2]

            sage: psi.post_compose(phi)
            the embedding of Rational function field in y over Finite Field
            in z2 of size 2^2 into Rational function field in y over Finite
            Field in z2 of size 2^2, sending [y] to [y^2]

        """
        K = self.Domain()
        M = psi.Codomain()
        if not isinstance(psi, EmbeddingOfFunctionField):
            psi = embedding_of_function_field(psi)
        # we don't perform any explicit consistency check; the composition
        # is well defined if the following commands do not produce an error.
        tau0 = K.embedding_of_constant_base_field().post_compose(
            self).post_compose(psi)
        image_of_gens = [psi(a) for a in self.image_of_generators()]
        return EmbeddingOfFunctionField(K, psi.codomain(),
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
                # what are domain and codomain of psi? it should be a map from
                # L1 to K
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
        try:
            assert psi.post_compose(phi).is_identity()
        except AssertionError:
            print("psi = ", psi)
            print("in ", psi.parent())
            print()
            print("phi = ", phi)
            print("in ", phi.parent())
            raise AssertionError()
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
        g = f_K(x, T).univariate_polynomial().change_variable_name("S")
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
        f_K = psi0.change_coefficients(f).change_variable_name("S")
        for beta in K.roots(f_K):
            if phi(beta) == alpha:
                psi1 = L1.hom(K, beta, psi0)
                # assert psi1.post_compose(phi).is_equal(L1.embedding())
                return psi1
        # if we get here, there is no right inverse
        return None

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
            return inverse is not None
            return inverse is not None
