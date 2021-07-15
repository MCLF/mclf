# -*- coding: utf-8 -*-
r"""
Standard fields and standard field extensions
=============================================

We call a field `K` a *standard field* if `K` is of one of the following types:

1. `K` is a *finite field*,
2. `K` is a *number field* (i.e. a finite extension of \mathbb{Q}),
3. `K` is a *function field*, i.e. `K` is a finitely generated extension of
   transcendence degree one of a subfield `k`, which is itself either a finite
   field or a number field.

In the following, all fields are assume to be standard.

An extension `L/K` of standard fields is of one of the following two types:

a. `L/K` is a finite, simple extension. i.e. `L\cong K[x]/(f)` for an
   irreducible polynomial `f` over `K`, or
b. `L/K` is a function field; more precisely, `K` is either finite or a number
   field, and there exists an element `x\in L`, transcendental over `K`, such
   that `L/K(x)` is finite and separable. By (a), we can write
   `L\cong K(x)[y]/(G)`, where `G` is a monic, irreducible and separable
   polynomial over `K(x)`.

A field extension of this form is then called a *standard field extension*.

One problem is that is that in Sage standard fields and their extensions
sometimes do not occur in their standard form, which makes it hard to deal with
them in a systematic way. To solve this problem, we create a class
:class:`StandardFiniteFieldExtension`, with two subclasses
:class:`StandardFiniteFieldExtension` and :class:`StandardFunctionField`.
An objects is determined by a standard field extension `L/K`, which may be given
in any form. The main feature of the object is an internal representation of the
extension `L/K` in standard form.


EXAMPLES::

    sage: from mclf import *
    sage: k0 = GF(2); k1 = GF(4)
    sage: k1_k0 = standard_field_extension(k1, k0)
    sage: k1_k0
    Finite Field in z2 of size 2^2, as finite extension of Finite Field of size 2

The base field and the extension field of a standard extensions can be accessed
via the methods :meth:`domain` and :meth:`codomain`.::

    sage: k1_k0.domain()
    Finite Field of size 2
    sage: k1_k0.codomain()
    Finite Field in z2 of size 2^2

We can check the degree and the transcendence degree of a standard extension.::

    sage: k1_k0.degree()
    2
    sage: k1_k0.transcendence_degree()
    0

A finite standard extension has a generator and a polynomial; these define the
standard model of the extension.::

    sage: k1_k0.generator()
    z2
    sage: k1_k0.polynomial()
    z2^2 + z2 + 1

We can compose standard extensions, and compute subextensions with given
generators.::

    sage: k2 = GF(16)
    sage: k2_k1 = standard_field_extension(k2, k1)
    sage: k2_k0 = k1_k0.superextension(k2_k1)
    sage: k2_k0

    sage: k2_k0.subextension(k1.gen())

We can also compute the base change of an extension with respect to another one.::

    sage: k2_k0.base_change(k1_k0)


A standard extension can also be defined via an injective field homomorphism.::

    sage: K.<x> = FunctionField(k0)
    sage: phi = K.hom([x^2+x])
    sage: K_K = standard_field_extension(phi)
    sage: K_K

    sage: K_K.generator()

    sage: K_K.polynomial()


"""

from sage.all import SageObject, lcm, ZZ, Infinity
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


def standard_field_extension(*args):
    r""" Return the standard field extension determined by the input.

    INPUT:

    - ``args`` -- data determining a standard field extension `L/K`

    OUTPUT: a Sage object representing the field extension `L/K`.

    The arguments may be

    - a field `L`,
    - an injective field morphism `\phi:L\to K`,
    - a pair `(L, K)`, where `L` is a field and `K` a subfield of `L`,
    - a triple `(L, K, [t_1,\ldots,t_r])`, where `L` is a field, `K` a subfield
      of `L`, and `t_1,\ldots,t_r` is a list of elements of `L`.

    Here the fields `K` and `L` are assumed to be standard fields, but may be
    given in any form (e.g. as fraction field of a polynomial ring etc.).

    In the first three cases, the extension is `L/K` case (where we choose for
    `K` the prime subfield of `L` in the first case). In the last case, the
    field extension is `L/K(t_1,\ldots,t_r)`.

    """
    from sage.categories.rings import Rings
    if len(args) == 1 and args[0] in Rings:
        L = args[0]
        K = L.prime_subfield()
        phi = K.hom(L)
        generators = None
        is_canonical_embedding = True
    elif len(args) == 1:
        phi = args[0]
        assert phi.is_injective(), "phi must be injective"
        K = phi.domain()
        L = phi.codomain()
        generators = None
        if K.is_subring(L):
            if phi == K.hom(L):
                is_canonical_embedding = True
            else:
                is_canonical_embedding = False
        else:
            K.register_embedding(phi)
            is_canonical_embedding = True

    elif len(args) == 2:
        L, K = args
        phi = K.hom(L)  # if K is not a subfield of L, an error is raised
        generators = None
        is_canonical_embedding = True

    elif len(args) == 3:
        L, K, generators = args
        phi = K.hom(L)
        generators = [L(t) for t in generators]
        is_canonical_embedding = True

    else:
        raise NotImplementedError()

    assert is_standard_field(K), "the domain of phi must be a standard field"
    assert is_standard_field(L), "the codomain of phi must be a standard field"

    if generators is None:
        if is_finite_extension(phi):
            return StandardFiniteFieldExtension(phi)
        else:
            return StandardFunctionField(phi)
    else:
        raise NotImplementedError()


def is_standard_field(K):
    r""" Return whether `K` is a standard field.

    INPUT:

    - ``K`` -- a field

    OUTPUT:

    Whether `K` is a standard field; this means that `K` is of one of the
    following types:

    1. `K` is a finite field
    2. `K` is a number field
    3. `K` is a function field, and the constant base field is either finite or
       a number field

    """
    from sage.categories.number_fields import NumberFields
    from sage.categories.function_fields import FunctionFields
    assert K.is_field(), "K must be a field"
    if K.is_finite() or K in NumberFields:
        return True
    elif K in FunctionFields:
        k = K.constant_base_field()
        return k.is_finite() or k in NumberFields


def is_finite_extension(phi):
    r""" Return whether an extension of standard fields is finite.

    INPUT:

    - ``phi`` -- an embedding `K\to L` of a standard field into another

    OUTPUT:

    whether `L/K` is a finite extension.

    Since `L` and `K` are finite fields, it follows easily that `L/K` is finite
    unless `L` is a function field and `K` is not.

    """
    from sage.categories.function_fields import FunctionFields
    return phi.domain() in FunctionFields or not phi.codomain() in FunctionFields


class StandardFieldExtension(SageObject):
    r""" Base class for a generic standard field extension.

    An object of this class should be created with the function
    :func:`standard_field_extension`. The returned object will belong to one of
    the two subclasses :class:`StandardFiniteFieldExtension` or
    :class:`StandardFunctionField`.

    """

    def domain(self):
        r""" Return the domain of this field extension, i.e. the base field.
        """
        return self._domain

    def codomain(self):
        r""" Return the codomain of this field extension, i.e. the extension field.
        """
        return self._codomain

    def embedding(self):
        r""" Return the embedding morphism from the base field to the extension field.
        """
        return self._embedding

    def has_standard_form(self):
        r""" Return whether the codomain is in standard form, as an extension
        of the domain.

        """
        return self._has_standard_form

    def standard_model(self):
        r""" Return the standard model of this field extension.

        """
        return self._standard_model

    def to_standard_model(self):
        r""" Return the isomorphism from the codomain to its standard model.

        """
        return self._to_standard_model

    def from_standard_model(self):
        r""" Return the isomorphism to the codomain, from its standard model.

        """
        return self._from_standard_model

    def subextension(self, generators, var_name="t"):
        r""" Return the subextension generated by ``generators``.

        Let `L/K` be this field extension.

        INPUT:

        - ``generators`` -- a list of elements of `L`
        - ``var_name`` -- string (default: "t")

        OUTPUT:

        the pair of field extensions `(M/K, L/M)`, where `M:=K(t_1,\ldots,t_r)`
        is the subfield generated over `K` by the elements `t_1,\ldots,t_r`

        """
        K = self.domain()
        L = self.codomain()
        M = K
        phi = self.embedding()
        if len(generators) > 1:
            raise NotImplementedError("subfield with multiple generators not yet implemented")
        for i, t in enumerate(generators):
            t = L(t)
            if _is_algebraic(t, M):
                M = M.extension(_minimal_polynomial(t, M), var_name+str(i+1))
            else:
                from sage.rings.function_field.constructor import FunctionField
                M = FunctionField(M, var_name+str(i+1))
            phi = M.hom(t, phi)
        return StandardFieldExtension((M, K)), StandardFieldExtension(phi)

    def is_finite(self):
        r""" Return whether this field extension is finite.

        This must be implemented by the subclass.
        """
        raise NotImplementedError()

    def generators(self):
        r""" Return a list of generators of this field extension.

        """
        pass

    def transcendence_degree(self):
        r""" Return the transcendence degree of this field extension.

        This must be implemented by the subclass.
        """
        raise NotImplementedError()

    def degree(self):
        r""" Return the degree of this field extension.

        This must be implemented by the subclass.
        """
        raise NotImplementedError()

    def is_transcendential(self, t):
        r""" Return whether this element if transcendental over the base field.


        """
        raise NotImplementedError()

    def minimal_polynomial(self, t):
        r""" Return the minimal polynomial of this element over the base field.

        INPUT:

        - `t` -- an element of the extension field `L`,
                 which is algebraic over the base field `K`

        OUTPUT:

        The minimal polynomial of `t` over `K`.

        This must be implemented by the subclass.
        """
        raise NotImplementedError()

    def restriction_of_valuation(self, w):
        r""" Compute the restriction of a valuation from the codomain to the
        domain of this field extension.

        INPUT:

        - ``w`` -- a valuation on the codomain `L` of this extension

        OUTPUT:

        the restriction `v:=w|_K` to the domain `K` of this extension.

        This method must be implemented by the appropriate subclass.

        .. NOTE::

            It is not clear if this method is very useful. The algorithm for
            computing the restriction depends more on the type of the fields `K`
            and `L`, and on the nature of the valuation, and not so much on the
            type of the extension `L/K`. Therefore, these algorithms should rather
            by implemented by the appropriate subclasses of :class:`ValuedField`.

        """
        raise NotImplementedError()


# ----------------------------------------------------------------------------

class StandardFiniteFieldExtension(StandardFieldExtension):
    r""" A finite extension of standard fields.

    INPUT:

    - ``phi`` -- an embedding `\phi:K\to L` of standard fields, such that
      `L/K` is a finite extension

    OUTPUT:

    An object representing the finite extension `L/K`. One of its features is
    that the extension `L/K` has an internal representation as a simple extension
    of a standard model of the base field `K`,

    .. MATH::

        L_1 = K1(\alpha)/K_1 \cong L/K.


    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(GF(2))
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x^3 - 1)
        sage: phi = K.hom([y], L)
        sage: standard_field_extension(phi)

    """

    def __init__(self, phi):
        self._embedding = phi
        self._domain = phi.domain()
        self._codomain = phi.codomain()
        if is_standard_finite_field_extension(phi):
            self._has_standard_form = True
        else:
            self._has_standard_form = False
            M, to_standard_model, from_standard_model = standard_model_of_finite_extension(phi)
            self._standard_model = M
            self._to_standard_model = to_standard_model
            self._from_standard_model = from_standard_model

    def __repr__(self):
        return "{}, as finite extension of {}".format(self.codomain(), self.domain())

    def is_finite(self):
        r""" Return whether this field extension is finite.

        """
        return True

    def generator(self):
        r""" Return a generator corresponding to the standard model of this extension.
        """
        return self._generator

    def polynomial(self):
        r""" Return the polynomial corresponding to the standard model of this extension.
        """
        return self._polynomial

    def transcendence_degree(self):
        r""" Return the transcendence degree of this field extension.

        """
        return ZZ(0)

    def degree(self):
        r""" Return the degree of this field extension.

        """
        return self.polynomial().degree()

    def is_transcendential(self, t):
        r""" Return whether this element if transcendental over the base field.

        """
        return False

    def minimal_polynomial(self, t):
        r""" Return the minimal polynomial of this element over the base field.

        INPUT:

        - `t` -- an element of the extension field `L`

        OUTPUT:

        The minimal polynomial of `t` over the base field `K`.

        """
        t = self.to_standard_model()(t)
        K = self.domain()
        A = matrix_of_extension_element(t, K)
        return A.characteristic_polynomial().factor()[0][0]

    def norm(self, a):
        r""" Return the norm of an element under this finite field extension.

        INPUT:

        - ``a`` -- an element of the codomain `L` of this finite field extension

        OUTPUT:

        the norm of `a` with respect to this finite field extension `L/K`; it
        is an element of the domain `K`.

        """
        # we work in the standard model of L, which has K as a subfield
        a = self.to_standard_model()(a)
        K = self.domain()
        A = matrix_of_extension_element(a, K)
        return A.determinant()

    def restriction_of_valuation(self, w):
        r""" Compute the restriction of a valuation from the codomain to the
        domain of this field extension.

        INPUT:

        - ``w`` -- a valuation on the codomain `L` of this extension

        OUTPUT:

        the restriction `v:=w|_K` to the domain `K` of this extension.

        This method must be implemented by the appropriate subclass.

        .. NOTE::

            It is not clear if this method is very useful. The algorithm for
            computing the restriction depends more on the type of the fields `K`
            and `L`, and on the nature of the valuation, and not so much on the
            type of the extension `L/K`. Therefore, these algorithms should rather
            by implemented by the appropriate subclasses of :class:`ValuedField`.

        """
        raise NotImplementedError()


def is_standard_finite_field_extension(phi):
    r""" Return whether `\phi` is a standard finite field extension.

    """
    if phi.domain() is phi.codomain() and phi._is_coercion:
        return True
    else:
        return phi.domain() is phi.codomain().base_field() and phi._is_coercion


class StandardFunctionField(StandardFieldExtension):
    r""" A function field over a finite field or a number field.

    INPUT:

    - ``phi`` -- an embedding `\phi:K\to L` of standard fields, such that
      `L/K` is of transcendence degree one

    OUTPUT:

    An object representing the finite extension `L/K` as a function field.
    One of its features is that the extension `L/K` has an internal representation
    as the composition of a rational function field `K(x)/K` and a finite,
    simple and separable extension `L/K(x)`.

    """

    def __init__(self, phi):


        self._domain = phi.domain()
        self._codomain = phi.codomain()
        self._embedding = phi
        F, to_standard_model, from_standard_model = standard_model_of_function_field(phi)
        self._standard_model = F
        self._to_standard_model = to_standard_model
        self._from_standard_model = from_standard_model

    def _repr_(self):

        return "{}, with field of constants {}".format(self.codomain(), self.domain())

    def is_finite(self):
        r""" Return whether this field extension is finite.

        """
        return False

    def generator(self):
        r""" Return the generator corresponding to the standard model of this
        function field.

        """
        return self._generator

    def transcendence_degree(self):
        r""" Return the transcendence degree of this field extension.

        """
        return ZZ(1)

    def degree(self):
        r""" Return the degree of this field extension.

        """
        return Infinity

    def is_transcendential(self, t):
        r""" Return whether this element if transcendental over the base field.


        """
        raise NotImplementedError()

    def minimal_polynomial(self, t):
        r""" Return the minimal polynomial of this element over the base field.

        INPUT:

        - `t` -- an element of the extension field `L`,
                 which is algebraic over the base field `K`

        OUTPUT:

        The minimal polynomial of `t` over `K`.

        """
        raise NotImplementedError()

    def restriction_of_valuation(self, w):
        r""" Compute the restriction of a valuation from the codomain to the
        domain of this field extension.

        INPUT:

        - ``w`` -- a valuation on the codomain `L` of this extension

        OUTPUT:

        the restriction `v:=w|_K` to the domain `K` of this extension.

        This method must be implemented by the appropriate subclass.

        .. NOTE::

            It is not clear if this method is very useful. The algorithm for
            computing the restriction depends more on the type of the fields `K`
            and `L`, and on the nature of the valuation, and not so much on the
            type of the extension `L/K`. Therefore, these algorithms should rather
            by implemented by the appropriate subclasses of :class:`ValuedField`.

        """
        raise NotImplementedError()


# ----------------------------------------------------------------------------

#                       helper functions


def standard_model_of_extension(phi, is_canonical_embedding=False):
    r""" Return the standard model of a field extension.

    INPUT:

    - ``phi`` -- an embedding of fields `\phi:K\to L`
    - ``is_canonical_embedding`` -- a boolean (default: ``True``)

    It is assumed that `K` and `L` are standard fields. If ``is_canonical_embedding``
    is ``True`` (the default) then it is assumed that `K` is a subfield of `L`
    and `\phi` is the canonical inclusion.

    OUTPUT:

    a tripel `(M, s, t)`, where `M` is a standard extension of `K`,
    `s:L\to M` is a `K`-linear isomorphism, and `t:M\to L` is the inverse of `s`.

    Recall that the extension `M/K` is *standard* if either `M/K` is finite and
    simple (i.e.\ generated by one element), or `M` is a finite simple extension
    of a rational function field `K(t)`.


    """
    if is_finite_extension(phi):
        return standard_model_of_finite_extension(phi)
    else:
        return standard_model_of_function_field(phi)


def standard_model_of_finite_extension(phi):
    r""" Return the standard model of a finite field extension.

    INPUT:

    - ``phi`` -- an embedding of fields `\phi:K\to L` which makes `L` a finite
                 extension of `K`

    It is assumed that `K` and `L` are standard fields.

    OUTPUT:

    a tripel `(M, s, t)`, where `M` is a finite simple field extension of `K`,
    `s:L\to M` is a `K`-linear isomorphism, and `t:M\to L` is the inverse of `s`.


    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(QQ)
        sage: k.<zeta> = CyclotomicField(5)
        sage: L.<y> = FunctionField(k)
        sage: phi = K.hom([y^2+y + zeta])
        sage: standard_model_of_finite_extension(phi)
        (Function field in T defined by T^8 + 4*T^7 + (-4*x + 5)*T^6 + (-12*x + 1)*T^5 + (6*x^2 - 9*x - 1)*T^4
         + (12*x^2 + 2*x + 1)*T^3 + (-4*x^3 + 3*x^2 + x)*T^2 + (-4*x^3 - 3*x^2 - 2*x - 1)*T + x^4 + x^3 + x^2 +
         x + 1,
         Function Field morphism:
           From: Rational function field in y over Cyclotomic Field of order 5 and degree 4
           To:   Function field in T defined by T^8 + 4*T^7 + (-4*x + 5)*T^6 + (-12*x + 1)*T^5 + (6*x^2 - 9*x -
         1)*T^4 + (12*x^2 + 2*x + 1)*T^3 + (-4*x^3 + 3*x^2 + x)*T^2 + (-4*x^3 - 3*x^2 - 2*x - 1)*T + x^4 + x^3
         + x^2 + x + 1
            Defn: y |--> T
               zeta |--> T,
         Function Field morphism:
           From: Function field in T defined by T^8 + 4*T^7 + (-4*x + 5)*T^6 + (-12*x + 1)*T^5 + (6*x^2 - 9*x -
         1)*T^4 + (12*x^2 + 2*x + 1)*T^3 + (-4*x^3 + 3*x^2 + x)*T^2 + (-4*x^3 - 3*x^2 - 2*x - 1)*T + x^4 + x^3
         + x^2 + x + 1
           To:   Rational function field in y over Cyclotomic Field of order 5 and degree 4
           Defn: T |--> y
                 T |--> zeta
                 x |--> y^2 + y + zeta)

    The following caused an error in a previous version. The fix is not very
    satisfying, though. The introduction of the new variable a1 is quite
    superfluous.::

        sage: R.<a> = QQ[]
        sage: K.<a> = NumberField(a^2-2)
        sage: F.<x> = FunctionField(K)
        sage: phi = F.hom([x])
        sage: standard_model_of_finite_extension(phi)
        (Function field in a1 defined by a1 - x,
         Function Field morphism:
           From: Rational function field in x over Number Field in a with defining polynomial a^2 - 2
           To:   Function field in a1 defined by a1 - x
           Defn: x |--> x
                 a |--> a,
         Function Field morphism:
           From: Function field in a1 defined by a1 - x
           To:   Rational function field in x over Number Field in a with defining polynomial a^2 - 2
           Defn: a1 |--> x
                 a1 |--> a
                  x |--> x)

    """

    from sage.categories.number_fields import NumberFields
    from sage.all import FiniteField
    K = phi.domain()
    L = phi.codomain()
    # we construct a simple finite extension M/K isomorphic to L/K
    # if K, L are finite or number fields, M should be in standard form, i.e.
    # M=GF(q) or M an absolute number field; then the embedding K\to M may
    # not be the canonical embedding
    if K.is_finite():
        # exception:
        # in this case we want M to be in standard form M=GF(q)
        # the standard form of a finite field is as GF(q)
        q = L.cardinality()
        M = FiniteField(q)
        L_to_M = embedding_into_finite_field(L, M)
        a = M.gen()
        f = a.minpoly()
        for b, _ in f.roots(L):
            if L_to_M(b) == a:
                M_to_L = M.hom([b], L)
                return M, L_to_M, M_to_L
        # if we get here, something went wrong
        raise AssertionError()
    elif isinstance(K, NumberFields):
        raise NotImplementedError()
    else:
        # now K and L are function fields
        if L.base() is K and phi._is_coercion:
            # take M:=L
            id_L = identity_map(L)
            return L, id_L, id_L
        else:
            # phi is not assumed to be the standard embedding
            k, k_to_K, k_to_L = common_subfield(phi)
            # k is a subfield of L!
            L0 = k
            M = K
            M_to_L = phi
            L0_to_M = k_to_K
            while L0 is not L:
                L1 = first_subextension(L0, L)
                M, iota, M_to_L, L1_to_M = extend_embedding(M_to_L, K, L0, L1, L0_to_M)
                L0 = L1
                L0_to_M = L1_to_M
            return M, L0_to_M, M_to_L


def first_subextension(K0, K):
    r""" Return the smallest nontrivial subextension of K/K_0.

    INPUT:

    - ``K0``, ``K`` -- fields, where `K/K_0` is a finitely generated, nontrivial
                       extension

    OUTPUT:

    a subfield `K_1` of `K`, where `K_1/K_0` the smallest nontrivial subextension
    of `K/K_0` in the internal representation.

    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(GF(2))
        sage: first_subextension(GF(2), K)
        Rational function field in x over Finite Field of size 2
        sage: R.<t> = QQ[]
        sage: K.<alpha> = NumberField(t^2+t+1)
        sage: L.<beta> = K.extension(t^3 + alpha)
        sage: first_subextension(QQ, L)
        Number Field in alpha with defining polynomial t^2 + t + 1

    """
    assert K0.is_subring(K)
    assert K is not K0
    if K.base_field() is K0:
        return K
    elif hasattr(K, "rational_function_field") and K.rational_function_field() is K:
        if K.constant_base_field() is K0:
            return K
        else:
            return first_subextension(K0, K.constant_base_field())
    else:
        return first_subextension(K0, K.base_field())


def embedding_into_finite_field(K, L):
    r""" Return an embedding of a finite field into another.

    INPUT:

    - ``K``, ``L`` -- finite fields

    We assume that there exists an embedding of `K` into `L`.

    OUTPUT:

    an embedding `\phi:K\to L`. If `K` has a coerce map into `L`, it is returned.
    Otherwise, an arbitrary embeddding is computed. If not such embedding exists,
    an error is raised.

    EXAMPLES::

        sage: from mclf import *
        sage: k0 = GF(4)
        sage: R.<t> = k0[]
        sage: k1.<a> = k0.extension(t^2+t+k0.gen())
        sage: k1
        Univariate Quotient Polynomial Ring in a over Finite Field in z2 of size 2^2 with modulus a^2 + a + z2
        sage: embedding_into_finite_field(k0, k1)
        Coercion map:
          From: Finite Field in z2 of size 2^2
          To:   Univariate Quotient Polynomial Ring in a over Finite Field in z2 of size 2^2 with modulus a^2 +
         a + z2
        sage: k2 = GF(16)
        sage: embedding_into_finite_field(k1, k2)
        Ring morphism:
          From: Univariate Quotient Polynomial Ring in a over Finite Field in z2 of size 2^2 with modulus a^2 +
         a + z2
          To:   Finite Field in z4 of size 2^4
          Defn: a |--> z4
                with map of base ring

    """
    if K.is_subring(L):
        return K.hom(L)
    q = K.cardinality()
    q_n = L.cardinality()
    assert q_n.is_power_of(q), "there is no embedding of K into L"
    K0 = K.base_ring()
    phi0 = embedding_into_finite_field(K0, L)
    a = K.gen()
    f = a.minpoly()
    b = f.roots(L)[0][0]
    return K.hom([b], L, phi0)


def standard_model_of_function_field(phi):
    r""" Return the standard model of a function field.

    INPUT:

    - ``phi`` -- a field embedding `\phi:K\to L`, where `K` and `L` are standard
                 fields and `L/K` has transcendence degree one

    OUTPUT:

    a tripel `(F, t, s)`, where

    - `F` is a function field in standard form, with constant base field `K`
    - `t:L\to F` is a `K`-linear isomorphism,
    - `s:F\to L` is the inverse of `t` (so `s` restricted to `K` is equal to `\phi`)

    ALGORITHM:

    The standard model of `L/K` is constructed in several steps:

    1. We find a common subfield `k` of `K` and `L`. Note that `K/k`
       is finite and `L/k` is a function field.
    2. Find the standard representation `F_0/k` of `L/k`.
    3. Compute the base change `F_1/K` of `F_0/k` with respect to `K/k`.

    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2-x)
        sage: S.<z> = L[]
        sage: M.<z> = L.extension(z^3-y)
        sage: phi = QQ.hom(M)
        sage: standard_model_of_function_field(phi)
        (Function field in z defined by z^6 - x,
         Function Field morphism:
           From: Function field in z defined by z^3 - y
           To:   Function field in z defined by z^6 - x
           Defn: z |--> z
                 y |--> z^3
                 x |--> x,
         Function Field morphism:
           From: Function field in z defined by z^6 - x
           To:   Function field in z defined by z^3 - y
           Defn: z |--> z)

        sage: R.<y> = K[]
        sage: L.<y> = K.extension(x^2+y^2)
        sage: A.<t> = QQ[]
        sage: k.<i> = QQ.extension(t^2+1)
        sage: phi = k.hom([x/y], L)
        sage: standard_model_of_function_field(phi)
        (Function field in y defined by y + i*x,
         Composite map:
           From: Function field in y defined by y^2 + x^2
           To:   Function field in y defined by y + i*x
           Defn:   Function Field endomorphism of Function field in y defined by y^2 + x^2
                   Defn: y |--> y
                 then
                   Function Field morphism:
                   From: Function field in y defined by y^2 + x^2
                   To:   Function field in y defined by y + i*x
                   Defn: y |--> -i*x
                         x |--> x
                         ,
         Composite map:
           From: Function field in y defined by y + i*x
           To:   Function field in y defined by y^2 + x^2
           Defn:   Function Field morphism:
                   From: Function field in y defined by y + i*x
                   To:   Function field in y defined by y^2 + x^2
                   Defn: y |--> y
                         x |--> x
                         i |--> -1/x*y
                 then
                   Function Field endomorphism of Function field in y defined by y^2 + x^2
                   Defn: y |--> y)

    """
    K = phi.domain()
    L = phi.codomain()
    if hasattr(L, "constant_base_field") and L.constant_base_field() is K:
        if is_standard_function_field(L):
            # we do nothing
            return L, L.hom(L.gen()), L.hom(L.gen())
        elif is_separable_over_rational_function_field(L):
            # use the inbuild function "simple_model"
            F, F_to_L, L_to_F = L.simple_model()
            return F, L_to_F, F_to_L
        else:
            # we have to find a separable generator
            pass
    else:
        # we follow the Algorithm explained above:
        # 1. find a common subfield k
        k, k_to_K, k_to_L = common_subfield(phi)
        # 2. compute the standard model F0/k of L/k
        F0, L_to_F0, F0_to_L = standard_model_of_function_field(k_to_L)
        # 3. compute the base change F1/K of F0/k wrt K/k
        # since we do have a section s:K->F0, F0 and F1 are isomorphic
        s = phi.post_compose(L_to_F0)
        F1, F0_to_F1, F1_to_F0 = base_change_of_standard_function_field(F0, k_to_K, s)
        L_to_F1 = L_to_F0.post_compose(F0_to_F1)
        F1_to_L = F1_to_F0.post_compose(F0_to_L)
        return F1, L_to_F1, F1_to_L


def is_standard_function_field(F):
    r""" Return whether `F` is a standard function field.

    INPUT:

    - ``F`` -- a function field, with a constant base field `k`

    OUTPUT:

    whether `F/k` is in standard form, i.e. `F` is a separable, monogetic
    extension of the rationa field field over `k`.

    """
    return F.rational_function_field() is F.base_field() and (
        F.rational_function_field() is F or F.is_separable())


def is_separable_over_rational_function_field(F):
    r""" Return whether F is a separable extension of the rational function field.

    INPUT:

    - ``F`` -- a function field

    So `F` is a finite extension of a rational function field `k(x)`

    OUTPUT:

    whether the extension `F/k(x)` is separable.

    """
    from sage.rings.function_field.function_field import RationalFunctionField
    if isinstance(F, RationalFunctionField):
        return True
    else:
        return (F.is_separable()
                and is_separable_over_rational_function_field(F.base_field()))


def common_subfield(phi):
    r""" Return a common subfield of the domain and the codomain of a field embedding.

    INPUT:

    - ``phi`` -- an embedding of fields `\phi:K\to L`

    It is assumed that `K` and `L` are standard fields.

    OUTPUT:

    a tripel `(k, s, t)`, where `k` is a subfield of `L`, `s:k\to K` is an
    embedding and `t:k\to L` is the natural inclusion.

    For the moment, we choose for `k` the common prime field of `K` and `L`. But
    it would be better to try to find the largest common subfield instead.

    """
    K = phi.domain()
    L = phi.codomain()
    k = L.prime_subfield()
    return k, k.hom(K), k.hom(L)


def base_change_of_standard_function_field(F, phi, u=None):
    r""" Return the base change of the standard function field `F` wrt `\phi`.

    INPUT:

    - ``F`` -- a standard function field
    - ``phi`` -- an embedding `\phi:k\to K`
    - ``u`` -- a `k`-linear embedding `u:K\to F`, or ``None`` (default: ``None``)

    It is assumed that `k` is the constant base field of `F` and that `K/k`
    is finite.

    OUTPUT:

    (if `u` is not given) a pair `(F_K,s)`, where `F_K/K` is a standard function
    field and `s:F\to F_K` is an embedding which identifies `F_K/K` with the
    base change of `F/k` to `K`,

    or

    (if `u` is given) a tripel `(F_K,s, t)`, where `F_K/K` is a standard function
    field, `s:F\to F_K` is an isomorphism which identifies `F_K/K` with the
    base change of `F/k` to `K`, and `t` is the inverse of `s`.

    """
    k = phi.domain()
    K = phi.codomain()
    assert k is F.constant_base_field(), "the domain of phi has to be the constant base field of F"
    F0 = F.base_field()
    f = F.polynomial()
    # f should be an irreducible polynomial over F0
    F0_K = FunctionField(K, F0.variable_name())
    psi = F0.hom([F0_K.gen()], phi)
    f_K = f.map_coefficients(psi, F0_K)
    if u is None:
        g = f_K.factor()[0][0]
        F_K = F0_K.extension(g, F.variable_name())
        return F_K, F.hom([F_K.gen()], psi)
    else:
        ut = F0_K.hom([F(F0.gen())], u)
        for g, _ in f_K.factor():
            if g.map_coefficients(ut, F)(F.gen()).is_zero():
                F_K = F0_K.extension(g, F.variable_name())
                F_to_F_K = F.hom([F_K.gen()], psi)
                F_K_to_F = F_K.hom([F.gen()], ut)
                return F_K, F_to_F_K, F_K_to_F
        # if we get here, something was wrong
        raise AssertionError()


def identity_map(K):
    r""" Return the identity map for a standard field `K`.

    """
    from sage.categories.homset import Hom
    return Hom(K, K).identity()


def extend_embedding(phi, k, L0, L1, psi0):
    r""" Return an extension of the embedding `\phi` one step.

    INPUT:

    - ``phi`` -- a field embedding `phi:K\to L`
    - ``k`` -- a subfield of `K` such that `K/k` is a standard extension.
    - ``L_0``, ``L_1`` -- subfields of `L` such that `L_1/L_0` is a simple extension
    - ``psi0`` -- an embedding `\psi_0:L_0\to K` which is a right inverse of `\phi`

    OUTPUT:

    a tupel `(K_1, \iota, \phi_1, \psi_1)`, where

    - `K_1/k` is a standard extension
    - `\iota:K\to K_1` is a `k`-linear embedding
    - `\phi_1:K_1\to L` is an extension of `\phi`, i.e. `\phi_1\circ\iota=\phi`
    - \psi_1:L_1\to K_1` is an extension of `\psi_0`.

    Moreover, the extension `\psi_1` is a right inverse of `\phi_1`, i.e.
    `\phi_1\circ\psi_1` is the identity on `L_1`.


    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(2)
        sage: K.<x> = FunctionField(k)
        sage: phi = K.hom([x^2+x], K)
        sage: K1, iota, phi1, psi1 = extend_embedding(phi, k, k, K, k.hom(K))
        sage: K1
        Function field in T defined by T^2 + T + x
        sage: phi1(x)
        x^2 + x
        sage: phi1(K1.gen())
        x

    """
    K = phi.domain()
    L = phi.codomain()

    if is_finite_simple_extension(L1, L0):
        alpha = L1.gen()
        f = L1.polynomial()
        assert f(alpha).is_zero()
        for g, _ in f.map_coefficients(psi0, K).factor():
            if g.map_coefficients(phi, L)(alpha).is_zero():
                # K1, iota, beta = extend_standard_extension(K, k, g)
                # K1/k is a standard extension, iota:K->K1 is an embedding,
                # beta in K1 is a zero of g generating K1/K

                # define K1, iota and phi1
                K2 = K.extension(g, L1.variable_name()+"1")
                phi2 = K2.hom([alpha], phi)
                k_to_K2 = k.hom(K2)
                K1, K2_to_K1, K1_to_K2 = standard_model_of_extension(
                    k_to_K2, is_canonical_embedding=True)
                phi1 = K1_to_K2.post_compose(phi2)
                iota = K.hom(K2).post_compose(K2_to_K1)
                # we also need a root of g generating K1/K
                beta = K2_to_K1(K2.gen())

                # for defn of psi1 we have the problem that the method "hom" requires
                # different input, depending on the type of field.
                # Using try/except is a somewhat dirty but pragmatic solution
                try:
                    psi1 = L1.hom([beta], K1, psi0)
                except TypeError:
                    psi1 = L1.hom([beta], K1)
                return K1, iota, phi1, psi1
        # if we get here, something went wrong
        raise AssertionError()

    elif is_rational_function_field(L1, L0):
        # then K/k must also be a function field
        t = L1.gen()
        x = K.rational_function_field().gen()
        f = algebraic_relation(L, phi(x), t)
        r, s = f.parent().gens()
        # f is an irreducible bivariate polynomial over L0 such that f(phi(x),t)=0
        assert f(phi(x), t).is_zero()
        # we substitute r:=x and consider f as an univariate polynomial in s over K
        f = f.map_coefficients(psi0, K)
        _, s = f.parent().gens()
        f = f(x, s).polynomial(s).change_ring(K)
        try:
            factorization = f.factor()
        except AssertionError:
            print("f = ", f)
            print(f.parent())
            print(f.parent().base_ring())
            print(f.parent().base_ring().base_ring())
            raise AssertionError("This polynomial f can't be factored.")
        for g, _ in factorization:
            if g.map_coefficients(phi, L)(t).is_zero():
                K1, iota, beta = extend_standard_extension(K, k, g)
                phi1 = K1.hom([t], phi)
                psi1 = L1.hom([beta], psi0)
                return K1, iota, phi1, psi1
        # if we get here, something went wrong
        raise AssertionError()

    else:
        raise NotImplementedError()


def is_finite_simple_extension(L, K):
    r""" Return whether `L/K` is a finite simple extension of fields.

    """
    return L.base_field() is K and hasattr(L, "polynomial")


def is_rational_function_field(L, K):
    r""" Return whether `L` is a rational function field over K.

    """
    return L.rational_function_field() is L and L.constant_base_field() is K


def extend_standard_extension(K, k, g):
    r""" Return a finite extension of a standard extension.

    INPUT:

    - ``K`` -- a field
    - ``k`` -- a subfield of `K` such that `K/k` is a standard extension
    - ``g`` -- an irreducible polynomial over `K`

    OUTPUT:

    a tupel `(K_1,\iota, \beta)`, where

    - `K_1/k` is a standard extension,
    - `\iota:K\to K_1` is an embedding,
    - `\beta\in K_1` is such that `K_1=\iota(K)[\beta]` and `g^\iota(\beta)=0`.


    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K.<theta> = NumberField(x^3 + x + 1)
        sage: g = x^2 + theta*x + 1
        sage: g.factor()
        x^2 + theta*x + 1
        sage: extend_standard_extension(K, QQ, g)
        (Number Field in theta with defining polynomial T^6 + 4*T^4 - T^3 + 4*T^2 + 1,
         Ring morphism:
           From: Number Field in theta with defining polynomial x^3 + x + 1
           To:   Number Field in theta with defining polynomial T^6 + 4*T^4 - T^3 + 4*T^2 + 1
           Defn: theta |--> theta^5 + 4*theta^3 - theta^2 + 3*theta,
         theta)

    """
    phi = k.hom(K)
    if is_finite_extension(phi):
        # K/k should be simple
        assert K.base_field() is k
        if K is k:
            L = k.extension(g, "T")
            return L, k.hom(L), L.gen()
        h = K.polynomial()
        beta = K.gen()
        assert h(beta).is_zero()
        K1 = K.extension(g, "T1")
        gamma = K1.primitive_element()
        f = minimal_polynomial(gamma, k)
        L = k.extension(f, K.variable_name())
        for beta_L, _ in h.roots(L):
            try:
                iota = K.hom([beta_L], k.hom(L))
            except:
                iota = K.hom([beta_L], L)
            g_L = g.map_coefficients(iota, L)
            roots = g_L.roots()
            if len(roots) > 0:
                return L, iota, roots[0][0]
        # if we get here, something went wrong
        raise AssertionError()
    else:
        assert is_standard_function_field(K)
        # K/k is a function field, so K1 should be a finite simple extension
        # of the rational subfield K0 = k(x)
        K0 = K.rational_function_field()
        return extend_standard_extension(K, K0, g)


def algebraic_relation(K, x, y):
    r""" Return an algebraic relation between `x` and `y`.

    INPUT:

    - ``K`` -- a function field, with constant base field `k`
    - ``x,y`` -- elements of `K`

    OUTPUT:

    an irreducible bivariate polynomial `f` over `k` such that `f(x,y)=0`.

    EXAMPLES::

        sage: from mclf import *
        sage: K0.<x> = FunctionField(GF(2))
        sage: R.<y> = K0[]
        sage: K.<y> = K0.extension(y^2+x^3+1)
        sage: algebraic_relation(K, x, y)
        x^3 + y^2 + 1
        sage: S.<z> = K[]
        sage: L.<z> = K.extension(z^2+z+x+y)
        sage: algebraic_relation(L, z+1, y)
        x^6 + x^5 + x^4*y + x^4 + x^2*y^2 + x^3 + x^2*y + x*y^2 + y^3 + y^2 + 1

    """
    K0 = K.rational_function_field()
    k = K0.constant_base_field()
    f = minimal_polynomial(x, K0)
    g = minimal_polynomial(y, K0)
    A = PolynomialRing(k, "X, Y, T")
    X, Y, T = A.gens()
    F = bivariate_equation(f)(T, X)
    G = bivariate_equation(g)(T, Y)
    B = PolynomialRing(k, "x, y")
    X, Y = B.gens()
    h = F.resultant(G, T)(X, Y, 0).radical()
    assert len(h.factor()) == 1, "h should be irreducible!?"
    assert h(x, y).is_zero()
    return h


def bivariate_equation(f):
    r"""

    INPUT:

    - ``f`` -- an univariate polynomial over a rational function field `K=k(t)`

    OUTPUT:

    The bivariate polynomial `F\in k[t, x]` obtained from `f` by clearing the
    denominators of the coefficients of `f`.


    EXAMPLES::

        sage: from mclf import *
        sage: K.<t> = FunctionField(QQ)
        sage: R.<x> = K[]
        sage: bivariate_equation(x^3/t + (t+1)*x + t*(t-2))
        t^3 + t^2*x + x^3 - 2*t^2 + t*x

    """
    R = f.parent()
    K = R.base_ring()
    k = K.constant_base_field()
    A = PolynomialRing(k, [K.variable_name(), R.variable_name()])
    t, x = A.gens()
    d = lcm([f[i].denominator() for i in range(f.degree() + 1)])
    f = d*f
    F = sum(f[i].numerator()(t)*x**i for i in range(f.degree() + 1))
    return F


def minimal_polynomial(alpha, K):
    r""" Return the minimal polynomial of `\alpha` over the field `K`.

    INPUT:

    - ``alpha`` -- an elemenent of a field `L`
    - ``K`` -- a subfield of `L` over which `alpha` is algebraic

    OUTPUT: the minimal polynomial of `\alpha` over `K`.

    """
    L = alpha.parent()
    assert K.is_subring(L), "K must be a subfield of L"
    if K == L:
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        A = PolynomialRing(K, 'T')
        return A.gen() - alpha
    elif L.base_ring() == K:
        return alpha.minpoly('T')
    else:
        A = matrix_of_extension_element(alpha, K)
        f = A.minimal_polynomial('T')
        assert f(alpha) == 0, "Error!"
        return f


def matrix_of_extension_element(alpha, K):
    r""" Return the matrix corresponding to this element of the field extension.

    """
    L = alpha.parent()
    M = L.base_ring()
    if M == K:
        return alpha.matrix()
    assert K.is_subring(M), "K must be a subring of M"
    A = alpha.matrix()
    n = A.nrows()
    D = {}
    for i in range(n):
        for j in range(n):
            D[(i, j)] = matrix_of_extension_element(A[i, j], K)
    m = D[(0, 0)].nrows()
    N = n*m
    from sage.matrix.constructor import matrix
    B = matrix(K, N, N)
    for i in range(n):
        for j in range(n):
            for k in range(m):
                for ell in range(m):
                    B[i*m+k, j*m+ell] = D[(i, j)][k, ell]
    return B


# --------------------------------------------------------------------------

#                     old stuff, but maybe still useful


def _is_subfield(L, K):
    r""" Return whether `K` is a subfield of `L`.

    Test recursively if `L=K` or if `K` is a subfield of the base field of `L`.

    """
    if L == K:
        return True
    elif hasattr(L, "base_field"):
        M = L.base_field()
        if M == L:
            # L should be a rational function field
            return _is_subfield(L.constant_base_field(), K)
        else:
            # L should be a finite extension of its base_field
            return _is_subfield(M, K)
    else:
        raise NotImplementedError()



def _subfield_of_function_field(F, t):
    r""" Return a new presentation of the function field F as finite extension
    of given subfield.

    INPUT:

    - ``F`` -- a function field
    - ``t`` -- a transcendential element of `F`

    Let `K` denote the constant base field of `F`.

    OUTPUT: a pair `(\phi,\psi)` of inverse isomorphisms of function fields

    .. MATH::

        \phi: F_1\to F, \quad \psi=\phi^{-1}:F\to F_1,

    where `F_1=K(t,z)` is a function field with base field the rational function
    field `K(t)` and the isomorphism `\phi` sends `t\in F_1` to the given element
    `t\in F`.

    """
    from sage.rings.function_field.constructor import FunctionField
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    K = F.constant_base_field()
    F0 = F.base_field()
    if F == F0:
        # F is a rational function field
        F0 = FunctionField(K, "t")
        t1 = F0.gen()
        R = PolynomialRing(F0, ["z"])
        g = R(t.numerator())
        h = R(t.denominator())
        f = g - t1*h
        F1 = F0.extension(f)
        z1 = F1.gen()
        phi0 = F0.hom(t)
        phi = F1.hom(F.gen(), phi0)
        psi = F.hom(z1)
        return phi, psi
    else:
        # F is a finite simple extension of the rational function field F0
        A = PolynomialRing(K, ["X", "Y", "T", "Z"])
        X, Y, T, Z = A.gens()

        # construction equation between generators of F
        x = F0.gen()
        y = F.gen()
        f = F.polynomial()
        assert f(y) == 0
        from sage.arith.functions import lcm
        h = lcm([c.denominator() for c in f])
        f = h*f
        g1 = sum([f[i].numerator()(X)*Y**i for i in range(f.degree()+1)])
        assert g1(x, y, T, Z) == 0

        # construct relation between x, y and t
        t_coeffs = t.list()
        h = lcm([c.denominator() for c in t_coeffs])
        t_coeffs = [(h*c).numerator() for c in t_coeffs]
        g2 = h(X)*T - sum(t_coeffs[i](X)*Y**i for i in range(len(t_coeffs)))
        assert g2(x, y, t, Z) == 0

        # construct relation between x, y and z:=x+y
        z = x + y
        g3 = Z - X - Y
        assert g3(x, y, T, z) == 0

        # find the relation between t and z
        J = A.ideal(g1, g2, g3)
        G = J.elimination_ideal([X, Y]).gens()[0]
        for g, _ in G.factor():
            if g(X, Y, t, z) == 0:
                break
        else:
            raise ValueError("We did not find a good factor of G")
        assert len(g.factor()) == 1

        # construct the function field F1
        F0 = FunctionField(K, "t")
        t1 = F0.gen()
        R = PolynomialRing(F0, "z")
        z1 = R.gen()
        g = g(0, 0, t1, Z).univariate_polynomial()(z1).monic()
        F1 = F0.extension(g)
        z1 = F1.gen()

        # wrote x,y as functions of t,z
        R = PolynomialRing(F1, ["X"])
        X = R.gen()
        G1 = g1(X, z1 - X, t1, z1)
        G2 = g2(X, z1 - X, t1, z1)
        G3 = G1.gcd(G2)
        assert G3.degree() == 1
        x1 = - G3[0]
        y1 = z1 - x1
        assert g1(x1, y1, T, Z) == 0

        # construct the morphism phi:F1-->F
        phi0 = F0.hom(t)
        phi = F1.hom(z, phi0)

        # construct the inverse morphism psi:F-->F1
        psi0 = F.base_field().hom(x1)
        psi = F.hom(y1, psi0)

        assert phi(psi(x)) == x
        assert phi(psi(y)) == y
        assert psi(phi(t1)) == t1
        assert psi(phi(z1)) == z1

        return phi, psi


def _new_presentation_of_function_field(F, K, t, generators=None):
    r""" Return a new presentation of the function field F with given base field.

    INPUT:

    - ``F`` -- a function field, with constant base field `L`
    - ``K`` -- a subfield of `L`
    - ``t`` -- a transcendential element of `F`


    OUTPUT:

    A tripel `(F_1,\phi,\psi)`, where `F_1` is a function field with constant
    base field `K`, and

    .. MATH::

        \phi: F_1\to F, \quad \psi=\phi^{-1}:F\to F_1,

    are mutually inverse `K`-isomorphism such that `\phi` sends the generators
    of the base field of `F_1` (a rational function field over `K`) to `t`.

    """
    L = F.constant_base_field()
    assert K.is_subring(L), "K must be a subfield of the constant base field of F"
    F0 = F.base_field()

    if F == F0 and K == L:
        # F is a rational function field over K; this case is much simpler
        F0 = FunctionField(K, "t")
        t1 = F0.gen()
        R = PolynomialRing(F0, ["z"])
        g = R(t.numerator())
        h = R(t.denominator())
        f = g - t1*h
        F1 = F0.extension(f)
        z1 = F1.gen()
        phi0 = F0.hom(t)
        phi = F1.hom(F.gen(), phi0)
        psi = F.hom(z1)
        return (F1, phi, psi)
    elif K == L:
        return _new_presentation_of_function_field_same_base_field(F, t)
    else:
        # the general case;
        # we reduce to the case where K=L
        F1, phi1, psi1 = _make_constant_base_field_smaller(F, K)
        # now F1 is a function field over K, with two generators,
        # phi1:F1 -- > F is a K-isomorphism and psi1 its inverse
        t1 = psi1(t)
        F2, phi2, psi2 = _new_presentation_of_function_field_same_base_field(F1, t1)
        return F2, phi1.pre_compose(phi2), psi2.pre_compose(psi1)


def _new_presentation_of_function_field_same_base_field(F, t):

    # F is a finite simple extension of the rational function field F0 over K
    K = F.constant_base_field()
    F0 = F.base_field()
    assert not F0 == F

    A = PolynomialRing(K, ["X", "Y", "T", "Z"])
    X, Y, T, Z = A.gens()

    # construction equation between generators of F
    x = F0.gen()
    y = F.gen()
    f = F.polynomial()
    assert f(y) == 0
    h = lcm([c.denominator() for c in f])
    f = h*f
    g1 = sum([f[i].numerator()(X)*Y**i for i in range(f.degree()+1)])
    assert g1(x, y, T, Z) == 0

    # construct relation between x, y and t
    t_coeffs = t.list()
    h = lcm([c.denominator() for c in t_coeffs])
    t_coeffs = [(h*c).numerator() for c in t_coeffs]
    g2 = h(X)*T - sum(t_coeffs[i](X)*Y**i for i in range(len(t_coeffs)))
    assert g2(x, y, t, Z) == 0

    # construct relation between x, y and z:=x+y
    z = x + y
    g3 = Z - X - Y
    assert g3(x, y, T, z) == 0

    # find the relation between t and z
    J = A.ideal(g1, g2, g3)
    G = J.elimination_ideal([X, Y]).gens()[0]
    for g, _ in G.factor():
        if g(X, Y, t, z) == 0:
            break
    else:
        raise ValueError("We did not find a good factor of G")
    assert len(g.factor()) == 1

    # construct the function field F1
    F0 = FunctionField(K, "t")
    t1 = F0.gen()
    R = PolynomialRing(F0, "z")
    z1 = R.gen()
    g = g(0, 0, t1, Z).univariate_polynomial()(z1).monic()
    F1 = F0.extension(g)
    z1 = F1.gen()

    # wrote x,y as functions of t,z
    R = PolynomialRing(F1, ["X"])
    X = R.gen()
    G1 = g1(X, z1 - X, t1, z1)
    G2 = g2(X, z1 - X, t1, z1)
    G3 = G1.gcd(G2)
    assert G3.degree() == 1
    x1 = - G3[0]
    y1 = z1 - x1
    assert g1(x1, y1, T, Z) == 0

    # construct the morphism phi:F1-->F
    phi0 = F0.hom(t)
    phi = F1.hom(z, phi0)

    # construct the inverse morphism psi:F-->F1
    psi0 = F.base_field().hom(x1)
    psi = F.hom(y1, psi0)

    assert phi(psi(x)) == x
    assert phi(psi(y)) == y
    assert psi(phi(t1)) == t1
    assert psi(phi(z1)) == z1

    return phi, psi


def _make_constant_base_field_smaller(F, K):
    r""" Return an isomorphic function field with smaller constant base field.

    INPUT:

    - ``F`` -- a function field
    - ``K`` -- a subfield of the constant base field `L` of `F`

    We assume that `L/K` is a finite simple extension.

    OUTPUT:

    A triple `(F_1, \phi, \psi)`, where `F_1` is a function field with constant
    base field `K`, `\phi:F_1\to F` is a `K`-isomorphism and `\psi` is the inverse
    of `\phi`.

    """
    F0 = F.base_field()
    assert not F0 == F, "F must be a proper extension of its base field."
    L = F0.constant_base_field()
    assert F0.base_field() == F0, "F must be a *simple* extension of its base field"
    assert K.is_subring(L), "K must be a subfield of the constant base field of F"
    f = L.polynomial()
    alpha = L.gen()
    assert f(alpha) == 0
    x = F0.gen()
    y = F.gen()
    g = F.polynomial()
    assert g(y) == 0

    A = PolynomialRing(K, ["U", "X", "Y", "Z"])
    U, X, Y, Z = A.gens()
    G1 = f(U)
    assert G1(alpha, X, Y, Z) == 0

    # a helper function
    def make_polynomial_in_UX(h):
        # h is a poynomial in L[x]; we turn it into a polynomial in U and X
        return h.map_coefficients(lambda c: c.polynomial()(U), A)(X)

    h = lcm(c.denominator() for c in g)
    g = h*g
    G2 = sum(make_polynomial_in_UX(g[i].numerator())*Y**i for i in range(g.degree()+1))
    assert G2(alpha, x, y, Z) == 0

    z = y + alpha
    G3 = Z - Y - U
    assert G3(alpha, X, y, z) == 0

    J = A.ideal(G1, G2, G3)
    G = J.elimination_ideal([U, Y]).gens()[0]
    for g, _ in G.factor():
        if g(U, x, Y, z) == 0:
            break
    else:
        raise ValueError("We did not find a good factor of G")
    assert len(g.factor()) == 1

    # construct the function field F1
    F0 = FunctionField(K, "x")
    x1 = F0.gen()
    R = PolynomialRing(F0, "z")
    z1 = R.gen()
    g = g(0, x1, 0, Z).univariate_polynomial()(z1).monic()
    F1 = F0.extension(g)
    z1 = F1.gen()

    # write alpha, y as functions of x, z
    R = PolynomialRing(F1, ["Y"])
    Y = R.gen()
    g1 = G1(z1-Y, x1, Y, z1)
    g2 = G2(z1-Y, x1, Y, z1)
    g3 = g1.gcd(g2)
    assert g3.degree() == 1
    y1 = - g3[0]
    alpha1 = z1 - y1
    assert f(alpha1) == 0

    # construct the morphism phi:F1-->F
    phi0 = F0.hom(x)
    phi = F1.hom(z, phi0)

    # construct the inverse morphism psi:F-->F1
    psi0 = L.hom([alpha1], F1)
    psi1 = F.base_field().hom(F1(x1), base_morphism=psi0)
    psi = F.hom(y1, psi1)

    assert phi(psi(x)) == x
    assert phi(psi(y)) == y
    assert psi(F(phi(alpha1))) == alpha1
    assert psi(F(phi(z1))) == z1

    return phi, psi


def _make_subfield(L, K, generators, var_name="t"):
    r""" Return the subfield of L generated over K by ``generators``.

    INPUT:

    - ``L`` -- a field
    - ``K`` -- a subfield of `L`
    - ``generators`` -- a list of elements of `L`
    - ``var_name`` -- a string (default: "t")

    OUTPUT: an injective field homorphisms, mapping its domain `M` onto the
    subfield `K(t_1,\ldots,t_r)` of `L`, generated over `K` by the elements
    `t_1,\ldots,t_r`.

    """
    M = K
    phi = K.hom(L)
    for i, t in enumerate(generators):
        t = L(t)
        if _is_algebraic(t, M):
            M = M.extension(_minimal_polynomial(t, M), var_name+str(i+1))
        else:
            from sage.rings.function_field.constructor import FunctionField
            M = FunctionField(M, var_name+str(i+1))
        phi = M.hom(t, phi)
    return phi
