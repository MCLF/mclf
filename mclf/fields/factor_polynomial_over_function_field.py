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

The performance is not great, but suffices for the moment. There is certainly
a lot of room for improvements.

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
        T + x

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
        g = r(T + t*alpha)
        g, factors = some_factors(g)
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
    from mclf.fields.gcds_of_polynomials_over_function_fields import (
        gcd_of_univariate_polynomials)
    K = f.base_ring()
    K0 = K.base()
    g = norm_of_polynomial(f)
    h = g.change_ring(K) // f
    if gcd_of_univariate_polynomials(K, h, f).is_one():
        G = g.factor()
        factors_of_f = []
        for r, e in G:
            s = gcd_of_univariate_polynomials(K, f, r)
            if gcd_of_univariate_polynomials(K, h, s).is_one():
                # s is a prime factor of f
                factors_of_f.append((s, e))
                f = f // s**e
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
