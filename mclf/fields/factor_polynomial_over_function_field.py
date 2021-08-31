# -*- coding: utf-8 -*-
"""
         Factoring univariate polynomials over functions fields
         ======================================================

We implement our own algorithm for factoring univariate polynomials over
nonrational function fields. Actually, this is a slight adaption of an
experimental implementation in Sage by Julian Rüth, see
`here <https://github.com/saraedum/sage/blob/experimental/src/sage/rings/\
function_field/function_field.py#L1717>`_.

In contrast to Julian's implementation, we do not assume that the polynomial
to be factored is square-free. This makes the algorithm slightly more
complicated and probably a bit slower; the reason for making this adaption is
that square-free decomposition of polynomials is also not implemented over
nonrational function fields.

Unfortunately, the performance is very bad. The reason probably has nothing to
do with our implementation; it rather seems to be that
computing gcd's for polynomials over function fields can be very costly, due to
coefficient explosion.

To improve this, we could implement our own method
:meth:`_xgcd_univariate_polynomial` for standardfunction fields, using e.g.
the algorithms described in

    *Algorithms for Polynomial GCD Computation over Algebraic Function Fields*,
    M. van Hoeij, M. Monogan

Or we could implement our own interface to Singular or Macaulay.

"""

from sage.arith.all import lcm, gcd


def factor_polynomial_over_function_field(K, f):
    r"""
    Factor the polynomial f over the function field K.

    INPUT:

    - ``K`` -- a function field, in standard form
    - ``f`` -- a nonzero univariate polynomial over ``K``

    OUTPUT: the complete factorization of ``f``

    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + y+ x^3 + 1)
        sage: S.<T> = F[]
        sage: f = T^2 + T + x^3 + 1
        sage: factor_polynomial_over_function_field(F, f)
        (T + y) * (T + y + 1)

        sage: g = T^2 + y*T + x + 1
        sage: f = norm_of_polynomial(g)*T^2; f
        T^6 + T^5 + (x^3 + 1)*T^4 + (x + 1)*T^3 + (x^2 + 1)*T^2

        sage: factor_polynomial_over_function_field(F, f)
        T^2 * (T^2 + y*T + x + 1) * (T^2 + (y + 1)*T + x + 1)

        sage: f = T + x
        sage: factor_polynomial_over_function_field(F, f)

        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + x^3 + 1)
        sage: S.<T> = F[]
        sage: f = (T^2 + x^3 + 1)^2
        sage: factor_polynomial_over_function_field(F, f)
        (T + y)^4

        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^8 + y + x^3 + 1)
        sage: S.<T> = F[]
        sage: f = F.polynomial()(T)
        sage: factor_polynomial_over_function_field(F, f)
        (T + y) * (T + y + 1) * (T^3 + y*T^2 + (y^2 + 1)*T + y^3 + y + 1)
        * (T^3 + (y + 1)*T^2 + y^2*T + y^3 + y^2 + 1)

    """
    from sage.structure.factorization import Factorization
    from sage.all import prod
    f = f.change_ring(K)
    print("factoring f = ", f)
    print("over ", K)
    print()

    if K is K.rational_function_field():
        # this case is well implemented
        return f.factor()

    if not K.is_separable():
        L, from_L, to_L = K.separable_model(names=('a', 'b'))
        F = factor_polynomial_over_function_field(L, f.map_coefficients(to_L))
        assert F.unit() == 1
        return Factorization([(h.map_coefficients(from_L), e) for h, e in F])

    K0 = K.base()
    assert K0 is K0.rational_function_field(), "K must be a simple extension \
        of its rational base field"
    element_of_K0 = element_iterator(K0)
    factorization = []
    T = f.parent().gen()
    alpha = K.gen()
    r = f
    counter = 0
    while r.degree() > 0:
        if counter > 10:
            raise AssertionError("this doesn't seem to work: f = {} in {}".format(f, f.parent()))
        else:
            counter += 1
        t = next(element_of_K0)
        print("t = ", t)
        g = r(T + t*alpha)
        print("g = ", g)
        g, factors = some_factors(g)
        print("factor = ", factors)
        print("new g = ", g)
        print()
        factorization += [(h(T - t*alpha), e) for h, e in factors]
        r = g(T - t*alpha)
    ret = Factorization(factorization, r[0])
    assert prod(ret) == f, "factorization not found: f = {} in {} \
        gives {}".format(f, f.parent(), ret)
    return ret


def some_factors(f):
    r""" Helper function

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: x, y = k.polynomial_generators(["x", "y"])
        sage: F = standard_function_field(y^2 + y + x^3)
        sage: x, y = F.generators()
        sage: T = F.polynomial_generator("T")
        sage: f = (T + x + y)*(T^2 + y)
        sage: some_factors(f)
        (1, [(T + y + x, 1), (T^2 + y, 1)])

        sage: f = T^3 + T + x^3
        sage: some_factors(f)
        (T^3 + T + x^3, [])

    """
    K = f.base_ring()
    K0 = K.base()
    g = norm_of_polynomial(f)
    print("norm of f = ", g)
    print()
    h = g.change_ring(K) // f
    print("h = ", h)
    print()
    if h.gcd(f).is_one():
        G = g.factor()
        print("g factors as ", G)
        print()
        factors_of_f = []
        for r, e in G:
            print("(r, e) = ", r, e)
            s = f.gcd(r)
            print("s = ", s)
            if h.gcd(s).is_one():
                # s is a prime factor of f
                print("is an irreducible factor!")
                factors_of_f.append((s, e))
                f = f // s**e
            else:
                print("is not irreducible")
            print()
    else:
        factors_of_f = []
    return f, factors_of_f


def norm_of_polynomial(f):
    r""" Return the norm of this polynomial relative to the extension of
    the coefficient field over its base field.

    """
    from sage.all import PolynomialRing
    K = f.base_ring()
    K0 = K.base()
    alpha = K.gen()
    A = alpha.matrix()
    R = PolynomialRing(K0, f.variable_name())
    T = R.gen()
    B = R.zero()
    for i in range(f.degree() + 1):
        B += f[i]._x(A)*T**i
    return B.det()


def element_iterator(K):
    r""" Return an iterator which produces an infinite sequence of distinct
    element of the field `K`.

    """
    assert not K.is_finite()
    if K.characteristic() == 0:
        a = K.one()
        while True:
            yield a
            a += 1
    else:
        # K must be a rational function field
        x = K.gen()
        k = K.constant_base_field()
        assert k.is_finite()
        i = 0
        while True:
            for a in k:
                if not (a+1).is_zero():
                    yield (a+1)*x**i
            i += 1


def roots_of_polynomial_over_function_field(K, f):
    r""" Return the set of roots of a polynomial over a function field.

    """
    roots = []
    for g, _ in factor_polynomial_over_function_field(K, f):
        if g.degree() == 1:
            roots.append(-g[0])
    assert all(f(a).is_zero() for a in roots), "something went wrong"
    return roots


# -------------------------------------------------------------------------

#                       the old code

def factor_polynomial_over_function_field_old(K, f):
    r"""
    Factor the polynomial f over the function field K.

    INPUT:

    - ``K`` -- a global function field
    - ``f`` -- a nonzero univariate polynomial over ``K``

    OUTPUT: the complete factorization of ``f``

    """
    f = f.change_ring(K)
    if K is K.rational_function_field():
        return f.factor()

    K0 = K.rational_function_field()
    k = K0.constant_base_field()
    old_name = f.variable_name()
    if (K.variable_name() == old_name
            or K0.variable_name() == old_name
            or hasattr(k, "variable_name") and k.variable_name() == old_name):
        # replace x with x1 to make the variable names distinct
        f = f.change_variable_name(old_name + "1")
    F, d = to_trivariate_polynomial(K, f)
    R = F.parent()
    G = R(defining_polynomial(K))
    factorization = []
    g = f
    J = R.ideal(F, G)
    for Q, P in J.primary_decomposition_complete():
        prime_factor = prime_factor_from_prime_ideal(K, P)
        if prime_factor.degree() > 0:
            e = 0
            while True:
                q, r = g.quo_rem(prime_factor)
                if r == 0:
                    g = q
                    e += 1
                else:
                    break
            factorization.append((prime_factor, e))
    assert g.degree() == 0, "f did not factor properly"
    from sage.structure.factorization import Factorization
    ret = Factorization(factorization, g[0])
    return ret


def defining_polynomial(K):
    r"""
    Return the defining polynomial of K, as a bivariate polynomial.

    INPUT:

    - ``K`` -- a function field, given as an extension of a rational function field

    OUTPUT: a bivariate polynomial `g` over the constant base field `k` of K
    such that `K` is the fraction field of `k[y, x]/(g)`. Here `x` is the
    generator of the rational function field `K_0` from which `K` was created,
    and `y` is the generator of `K`.

    """
    return K.base_field()._to_bivariate_polynomial(K.polynomial())[0]


def to_bivariate_polynomial(K, a):
    r"""
    Convert ``a`` from an element of ``K`` to a bivariate polynomial and a denominator.

    INPUT:

    - ``K`` -- a function field, given as a finite extension of a rational function field.
    - ``a`` -- an element of ``K``

    OUTPUT:

    - a bivariate polynomial F
    - a univariate polynomial d

    such that `a = F(y, x)/d(x)`.

    """
    v = a.list()
    denom = lcm([c.denominator() for c in v])
    S = denom.parent()
    y, x = S.base_ring()['%s,%s' % (K.variable_name(),
                                    K.base_field().variable_name())].gens()
    phi = S.hom([x])
    F, d = sum([phi((denom * v[i]).numerator())
               * y**i for i in range(len(v))]), denom
    return F, d


def to_trivariate_polynomial(K, f):
    r"""
    Convert ``f`` from a univariate polynomial over K into a trivariate
    polynomial and a denominator.

    INPUT:

    - ``K`` -- a function field
    - ``f`` -- univariate polynomial over K

    OUTPUT:

    - trivariate polynomial F, denominator d

    Here `F` is a polynomial in `k[x, y, z]` and d a polynomial in `k[x]`.

    """
    v = [to_bivariate_polynomial(K, c) for c in f.list()]
    denom = lcm([b for a, b in v])
    S = denom.parent()
    k = S.base_ring()
    z, y, x = k['%s,%s,%s' % (f.parent().variable_name(), K.variable_name(),
                K.base_field().variable_name())].gens()
    F = z.parent().zero()
    for i in range(len(v)):
        a, b = v[i]
        F += (denom(x) * a(y, x) / b(x)).numerator() * z**i
    d = denom(x)
    return F, d


def prime_factor_from_prime_ideal(K, P):
    r"""
    Return the univariate polynomial over K corresponding to the prime ideal P.

    INPUT:

    - ``K`` -- a function field
    - ``P`` -- a prime ideal of a multivariate polynomial ring

    OUTPUT: a monic irreducible polynomial `f` over `K`.
    We assume that `P` is a prime ideal of `k[z, y, x]` and that
    `K = k(y, x | g(y,x) = 0)`. Then `f` is a generator of the ideal generated
    by `P` in `K[z]`.

    """
    R = P.ring()
    S = K['%s' % R.variable_names()[0]]
    z = S.gen()
    y = K.gen()
    x = K.base_field().gen()
    generators = [f(z, y, x) for f in P.gens()]
    return S(gcd(generators)).monic()
