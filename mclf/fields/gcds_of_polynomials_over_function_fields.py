# -*- coding: utf-8 -*-
"""
Computing gcds of univariate polynomials over function fields
=============================================================



"""


def gcd_of_univariate_polynomials(F, f, g):
    r""" Return the gcd of the polynomial `f` ad `g`.

    INPUT:

    - ``F`` a function field in standard form
    - ``f``, ``g`` -- univariate polynomials over `F`

    OUTPUT:

    The monic gcd `h` of `f` and `g`; or zero if both `f` and `g` are zero.

    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(4)
        sage: a = k.gen()
        sage: F.<x> = FunctionField(k)
        sage: R.<T> = F[]
        sage: r = T^2 + T/x + a
        sage: s = T^3 +x*T^2 + a
        sage: gcd_of_univariate_polynomials(F, r, s)

        sage: f = r^8*s
        sage: g = r*s^6
        sage: gcd_of_univariate_polynomials(F, f, g)
        T^5 + ((x^2 + 1)/x)*T^4 + (z2 + 1)*T^3 + (z2*x + z2)*T^2 + z2/x*T + z2 + 1

This computation takes roughly 52 ms; if you use the inbuilt method of the
rational function field `F` instead, it takes about 15 s.

    """
    f = f.change_ring(F)
    g = g.change_ring(F)
    S = f.parent()
    zero = S.zero()
    one = S.one()

    if g.is_zero():
        if f.is_zero():
            return zero
        else:
            return f.monic()
    elif f.is_zero():
        return g.monic()

    if F is F.rational_function_field():
        # we just replace the rational function field F by the fraction field
        # K of the polynomial ring R of F
        # the field K has an implementation of the subresultant algorithm
        # which is reasonably good in many cases
        K = F._ring.fraction_field()
        ft = f.change_ring(K)
        gt = g.change_ring(K)
        return (ft.gcd(gt)).change_ring(F)

    else:
        # we use our own version of the subresultant algorithm
        raise NotImplementedError()


def xgcd_of_univariate_polynomials(F, f, g):
    r""" Return an extended gcd of `f` and `g`.

    INPUT:

    - ``F`` -- a function field in standard form
    - ``f``, ``g`` -- univariate polynomials over `F`

    OUTPUT:

    A tuple `(h, u, v)` of polynomials such that `h` is the gcd of `f` and `g`
    (monic or zero), and `u,v` are polynomials such that

    .. MATH::

        h = u\cdot f + v\cdot g.


    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(4)
        sage: a = k.gen()
        sage: F.<x> = FunctionField(k)
        sage: R.<T> = F[]
        sage: r = T^2 + T/x + a
        sage: s = T^3 +x*T^2 + a
        sage: xgcd_of_univariate_polynomials(F, r, s)

        sage: f = r^7*s
        sage: g = r*s^5
        sage: h, u, v = xgcd_of_univariate_polynomials(F, f, g); h
        T^5 + ((x^2 + 1)/x)*T^4 + (z2 + 1)*T^3 + (z2*x + z2)*T^2 + z2/x*T + z2 + 1

    """
    f = f.change_ring(F)
    g = g.change_ring(F)
    S = f.parent()
    zero = S.zero()
    one = S.one()

    if F is F.rational_function_field():
        if g.is_zero():
            if f.is_zero():
                return zero, zero, zero
            else:
                c = 1/f.leading_coefficient()
                return (f.monic(), S(c), zero)
        elif f.is_zero():
            c = 1/g.leading_coefficient()
            return (g.monic(), zero, S(c))

        # the following algorithm is very bad and should be replaced by a
        # variant o the subresultant algorithm
        ft, denom_f = primitive_associate(f)
        gt, denom_g = primitive_associate(g)

        r0 = ft
        r1 = gt
        u = one
        v = zero
        u1 = zero
        v1 = one

        while True:
            c, q, r = pseudo_quo_rem(r0, r1)
            if not r.is_zero():
                r0, r1, u, v, u1, v1 = r1, r, u1, v1, c*u - q*u1, c*v - q*v1
            else:
                break
        # now r1 = u1*ft+ v1*gt is associate to the gcd of f and g
        assert r1 == u1*ft + v1*gt
        c = 1/r1.leading_coefficient()
        return c*r1, c*u1, c*v1

    else:
        raise NotImplementedError()


def primitive_associate(f):
    r""" Return the primitive associate of a polynomial over a rational
    function field.

    INPUT:

    - ``f`` -- a nonzero univariate polynomial over a rational function field `F`.

    OUTPUT:

    The pair `(\tilde{f}, d)`, where `\tilde{f} = d\cdot f` is the primitive
    associate of `f` over the polynomial subring `R` of `F`, and `d\in R`.

    The *primitive associate* of a polynomial `f=a_0+a_1T+\ldots+a_nT^n`
    over `F=k(x)` is the unique constant multiple of `f`,
    `\tilde{f} = c\cdot f`, such that

    - `\tilde{f}=c\cdot f` has coefficients in the subring `R:=k[x]`,
    -  `\tilde{f}` is primitive, i.e. the gcd of its coefficients is one,
    - the leading coefficent of `\tilde{f}` is normalized (wrt `x`).

    """
    from sage.all import gcd, lcm, PolynomialRing
    assert not f.is_zero()
    n = f.degree()
    F = f.base_ring()
    assert F is F.rational_function_field()
    R = F._ring
    nums = [f[i].numerator() for i in range(n + 1)]
    denoms = [f[i].denominator() for i in range(n + 1)]
    c = gcd(nums)
    d = lcm(denoms)
    S = PolynomialRing(R, f.variable_name())
    return S([d*nums[i]//denoms[i]//c for i in range(n + 1)]), d//c


def pseudo_quo_rem(f, g):
    r""" Return the pseudo-quotient and -remainder of the euclidean division
    of `f` and `g`.

    INPUT:

    ``f``, ``g`` -- two poynomials over unique factorization domain `R`.

    It is assumed that `g\neq 0`.

    OUTPUT:

    A triple `(c, q, r)`, where `c\in R` and `q,r` are polynomials such that

    - `c\cdot f = q\cdot g + r`,
    - `\deg(r)<\deg(g)`, or `r=0`.


    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(2)
        sage: R.<x> = k[]
        sage: S.<T> = R[]
        sage: f = T^5 + x*T + x^2 + 1
        sage: g = x*T^4 + T + 1
        sage: pseudo_quo_rem(f, g)
        (x^2, x*T, x*T^2 + (x^3 + x^2)*T + x^4 + x^2)

    """
    S = f.parent()
    R = S.base_ring()
    if g.is_zero():
        raise ZeroDivisionError()
    if f.is_zero():
        return R.one(), S.one(), S.zero()
    if f.degree() < g.degree():
        return R.one(), S.zero(), f
    d = f.degree() - g.degree() + 1
    c = g.leading_coefficient()**d
    q, r = (c*f).quo_rem(g)
    return (c, q, r)
