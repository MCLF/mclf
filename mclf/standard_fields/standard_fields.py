# -*- coding: utf-8 -*-
r"""
Standard fields
===============

We call a field `K` a *standard field* if `K` is of one of the following types:

1. `K` is a *finite field*,
2. `K` is a *number field* (i.e. a finite extension of \mathbb{Q}),
3. `K` is a *function field*, i.e. `K` is a finitely generated extension of
   transcendence degree one of a subfield `k`, which is itself either a finite
   field or a number field.

Basically all calculations done in this project involve calculations with such
standard fields.

One problem is that is that in Sage standard fields sometimes do not occur in
a any kind of standard form, which makes it hard to deal with
them in a systematic way. For instance, a number field may be represented as
an absolute number field, or as a tower of relative number fields.

To solve this problem, we create a class
:class:`StandardField`. An object of this class represents a standard field `K`,
which may be given in any form which provides internal access to a standard model
of `K`.


EXAMPLES::


"""

from sage.all import SageObject, lcm
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


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

    EXAMPLES::

        sage: from mclf import *
        sage: is_standard_field(QQ)
        True
        sage: is_standard_field(RR)
        False

    """
    from sage.categories.number_fields import NumberFields
    from sage.categories.function_fields import FunctionFields
    assert K.is_field(), "K must be a field"
    if K.is_finite() or K in NumberFields:
        return True
    elif K in FunctionFields:
        k = K.constant_base_field()
        return k.is_finite() or k in NumberFields
    else:
        return False


def standard_field(K):
    r""" Return the standard form of this field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the object representing `K` and its normal model.

    EXAMPLES::

        sage: from mclf import *
        sage: standard_field(QQ)
        Rational Field as a standard field

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+x+1)
        sage: L.<b> = K.extension(x^3+a*x+1)
        sage: LL = standard_field(L)
        sage: LL.underlying_field()
        Number Field in b with defining polynomial x^3 + a*x + 1 over its base field
        sage: LL.standard_model()
        Number Field in b with defining polynomial x^6 - x^4 + 2*x^3 + x^2 - x + 1
        sage: LL.to_standard_model()(b)
        b

        sage: k0 = GF(2)
        sage: K0.<x> = FunctionField(k0)
        sage: R.<y> = K0[]
        sage: K.<y> = K0.extension(y^2+y+x^3+1)
        sage: S.<z> = K[]
        sage: L.<z> = K.extension(z^3 +y*z - x^2)
        sage: F = standard_field(L); F
        Function field in z defined by z^3 + y*z + x^2, as a standard field
        sage: F.standard_model()
        Function field in z defined by z^6 + z^4 + (x^3 + 1)*z^2 + x^2*z + x^4
        sage: F.to_standard_model()(y)
        1/x^2*z^5 + 1/x^2*z^3 + z^2 + ((x^3 + 1)/x^2)*z + 1

    """
    from sage.categories.fields import Fields
    from sage.categories.number_fields import NumberFields
    assert K in Fields, "K must be a field"
    if K.is_finite():
        return StandardFiniteField(K)
    elif K in NumberFields:
        return StandardNumberField(K)
    else:
        return standard_function_field(K)


def standard_function_field(K, constant_base_field=None):
    r""" Return the standard model of this function field.

    INPUT:

    - ``K`` -- a function field
    - ``k`` -- a subfield of `K`, or ``None`` (default: ``None``)

    The subfield `k` may be given either as a field with a natural
    coercion into `K`, or as an embedding of fields `\phi:k\to K`.

    OUTPUT:

    the object representing the function field `K/k` and its normal model.

    .. NOTE::

        At the moment, a standard model may be an extension of `k(x)` of degree
        one; in this case, it would be better to replace it with `k(x)` itself.


    EXAMPLES:

        sage: from mclf import *
        sage: k0 = GF(2)
        sage: R.<t> = k0[]
        sage: k.<a> = k0.extension(t^2+t+1)
        sage: F0.<x> = FunctionField(k0)
        sage: S.<y> = F0[]
        sage: F.<y> = F0.extension(y^2+y+1)
        sage: phi = k.hom([y], F)
        sage: F = standard_function_field(F, phi); F
        Function field in y defined by y^2 + y + 1, as a standard field

    The standard model of `F` is a simple extension of `k(x)` of degree one.::

        sage: F.standard_model()
        Function field in y defined by y + a

    Actually, the standard model should be `k(x)``!

    """

    from sage.categories.fields import Fields
    from sage.categories.number_fields import NumberFields
    assert K in Fields, "K must be a field"
    if constant_base_field in Fields:
        k = constant_base_field
        phi = k.hom(K)
    elif hasattr(constant_base_field, "domain"):
        assert constant_base_field.codomain() is K, "K must be the codomain of phi"
        phi = constant_base_field
        k = phi.domain()
    elif constant_base_field is None:
        k = K.constant_base_field()
        phi = k.hom(K)
    else:
        raise ValueError("the constant base field if of the wrong type")
    assert k.is_finite() or k in NumberFields, "k must be a finite or a number field"
    return StandardFunctionField(phi)


class StandardField(SageObject):

    def underlying_field(self):
        return self._underlying_field

    def standard_model(self):
        return self._standard_model

    def to_standard_model(self):
        return self._to_standard_model

    def from_standard_model(self):
        return self._from_standard_model

    def __call__(self, a):
        r""" coerce an element into this field.

        """
        return self.underlying_field()(a)


class StandardFiniteField(StandardField):

    def __init__(self, K):
        from sage.categories.fields import Fields
        assert K in Fields, "K must be a field"
        assert K.is_finite(), "K must be a finite field"
        self._underlying_field = K
        # compute the normal form of K
        # for the moment, we pretend all finite fields are in standard form
        self._standard_model = K
        self._to_standard_model = identity_map(K)
        self._from_standard_model = identity_map(K)

    def _repr_(self):
        return "{} as a standard field".format(self.underlying_field())


class StandardNumberField(StandardField):

    def __init__(self, K):
        from sage.categories.number_fields import NumberFields
        assert K in NumberFields, "K must be a number field"
        self._underlying_field = K
        # compute the normal form of K
        if K.is_absolute():
            self._standard_model = K
            self._to_standard_model = identity_map(K)
            self._from_standard_model = identity_map(K)
        else:
            Ka = K.absolute_field(K.variable_name())
            Ka_to_K, K_to_Ka = Ka.structure()
            self._standard_model = Ka
            self._to_standard_model = K_to_Ka
            self._from_standard_model = Ka_to_K

    def _repr_(self):
        return "{} as a standard field".format(self.underlying_field())


class StandardFunctionField(StandardField):
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

        self._underlying_field = phi.codomain()
        self._constant_base_field = phi.domain()
        self._embedding_of_constant_base_field = phi
        F, to_standard_model, from_standard_model = standard_model_of_function_field(phi)
        self._standard_model = F
        self._to_standard_model = to_standard_model
        self._from_standard_model = from_standard_model

    def _repr_(self):

        return "{}, as a standard field".format(self.underlying_field())

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


# ----------------------------------------------------------------------------

#                       helper functions


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
            raise NotImplementedError("standard model of inseparable function field not yet implemented")
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
    from mclf.standard_fields.finite_field_extensions import is_finite_extension
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
