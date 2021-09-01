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
        1

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
        # we use our own version of the subresultant algorithm:
        # we follow Cohen, Algorithmus 3.3.1, with the modification suggested
        # by van Hoeij und Monagan
        A = numerator_of_polynomial(f)
        B = numerator_of_polynomial(g)
        # A, B have coefficients in the standard order of F
        B = quasi_inverse(B.leading_coefficient())*B
        # now the leading coefficient of B lies in the ufd R0
        R0 = B.base_ring().base()
        g = R0.one()
        h = R0.one()
        while True:
            delta = A.degree() - B.degree()
            _, R = A.pseudo_quo_rem(B)
            if R.is_zero():
                return B.change_ring(F).monic()
            elif R.degree() == 0:
                return f.parent().one()
            A, B = B, R // (g*h**delta)
            B = quasi_inverse(B.leading_coefficient())*B
            g, h = A.leading_coefficient(), g**delta // h**(delta-1)


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
        sage: h, u, v = xgcd_of_univariate_polynomials(F, r, s); h
        1

        sage: f = r^9*s
        sage: g = r*s^7
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

        ft = numerator_of_polynomial(f)
        gt = numerator_of_polynomial(g)
        ht, ut, vt = xgcd_of_polynomials_over_ufd(ft, gt)
        c = 1/ht.leading_coefficient()
        return c*ht, c*ut, c*vt

    else:
        raise NotImplementedError()


def xgcd_of_polynomials_over_ufd(A, B, algorithm="primitive"):
    r""" Return an extended gcd of two polynomials over a UFD.

    INPUT:

    - ``A``, ``B`` -- polynomials over a UFD `R`
    - ``algorihtm`` -- a string, which must be either "primitive", or
      "subresultant" (default: "primitive")

    OUTPUT:

    a triple `(D, U, V)` of polynomials over `R` such that

    .. MATH::

        D = U\cdot A + V\cdot B,

    and where `D` is the gcd of `A` and `B` in the polynomial ring over the
    fraction field of `R`, up to a constant.


    ALGORITHM:

    Depending on the value of ``algorithm``, we use a version of the
    *primitive PRS algorithm*, or the *subresultant PRS algorithm*.
    See Algorithm 3.2.10, Algorithm 3.3.1 and Exercise 5 in

        H. Cohen,
        *A course in computational algebraic number theory*.


    EXAMPLES::

        sage: from mclf import *
        sage: S.<T> = ZZ[]
        sage: A = 3*T + 5
        sage: B = T^2 + 2*T + 1
        sage: xgcd_of_polynomials_over_ufd(A, B)
        (4, -3*T - 1, 9)

        sage: A = 2*T^3 + T + 3
        sage: B = T^2 + 5*T + 1
        sage: xgcd_of_polynomials_over_ufd(A, B)
        (-615, -49*T - 232, 98*T^2 - 26*T + 81)

        sage: A = (3*T - 2)*(T^2 - 1)^5
        sage: B = (3*T - 2)*(T + 3)^8
        sage: D, U, V = xgcd_of_polynomials_over_ufd(A, B)
        sage: D.content()
        268435456

        sage: D/D.content()
        3*T - 2

    If we use the subresultant PRS algorithm instead, we get much larger
    content of `D`; still this algorithm is asymtotically faster. ::

        sage: D, U, V = xgcd_of_polynomials_over_ufd(A, B, algorithm="subresultant")
        sage: D.content()
        171656720039827348768084927085154524240805888

    The algorithm applies to polynomials over any UFD `R`, in which the
    computation of the gcd is available. For instance, if `R` is a polynomial
    over a finite field, the performance is very similar to the case
    `R=\mathbb{Z}`. ::

        sage: R.<x> = GF(4)[]
        sage: a = GF(4).gen()
        sage: S.<T> = R[]
        sage: A = (x*T + a)*(T^2 + a*T + x)^10
        sage: B = (x*T + a)*(T^3 + a*T + x)^7
        sage: D, U, V = xgcd_of_polynomials_over_ufd(A, B)
        sage: D.content_ideal().gen()
        x^48 + (z2 + 1)*x^32

        sage: D/_
        x*T + Z2

    """
    S = A.parent()
    R = A.base_ring()
    zero = S.zero()
    one = S.one()

    if A.is_zero():
        if B.is_zero():
            return zero, zero, zero
        else:
            return B, zero, one
    else:
        if B.is_zero():
            return A, one, zero

    if A.degree() < B.degree():
        D, V, U = xgcd_of_polynomials_over_ufd(B, A)
        return D, U, V

    R0, R1 = A, B
    U0, U1 = one, zero
    V0, V1 = zero, one
    alpha, beta = R.base().one(), R.base().one()
    g, h = R.base().one(), R.base().one()

    while not R1.is_zero():
        delta = R0.degree() - R1.degree()
        alpha = R1.leading_coefficient()**(delta + 1)
        if algorithm == "subresultant":
            beta = g * h**delta
        Q, R = R0.pseudo_quo_rem(R1)
        assert alpha*R0 == Q*R1 + R
        U0, U1 = U1, (alpha*U0 - Q*U1)
        V0, V1 = V1, (alpha*V0 - Q*V1)
        if algorithm == "primitive":
            beta = (R.content_ideal() + U1.content_ideal()).gen()
        else:
            assert S(beta).divides(R), "alpha = {}, beta = {}, R = {}".format(alpha, beta, R)
        U1 = U1 // beta
        V1 = V1 // beta
        R0, R1 = R1, R // beta
        if algorithm == "subresultant":
            g = R0.leading_coefficient()
            h = g**delta * h**(1 - delta)
        assert R1 == U1*A + V1*B

    return R0, U0, V0
    # assert B.divides(R0 - U0*A)
    # V0 = (R0 - U0*A) // B
    # assert R0 == U0*A + V0*B
    # return R0, U0, V0


def standard_order(F):
    r""" Return the standard order of a standard function field.

    INPUT:

    - ``F`` -- a standard function field

    OUTPUT:

    the standard order `R` of `F`;

    if `F=k(x)`` is a rational function field then `R=k[x]` is the polynomial
    ring in the standard generator of `F`; if `F/F_0` is a finite simple
    extension of its rational base field, then `R=R_0[y]`, where `R_0` is the
    standard order of `F_0` and `y` is the standard generator of `F/F_0`.

    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: standard_order(F0)
        Univariate Polynomial Ring in x over Finite Field of size 2 (using GF2X)

        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + y + x^3)
        sage: standard_order(F)
        Univariate Quotient Polynomial Ring in y over Univariate Polynomial Ring
        in x over Finite Field of size 2 (using GF2X) with modulus y^2 + y + x^3

    """
    if F is F.rational_function_field():
        return F._ring
    else:
        if not hasattr(F, "_standard_order"):
            F0 = F.base()
            R0 = F0._ring
            G = numerator_of_polynomial(F.polynomial())
            R = R0.extension(G, F.variable_name())
            F._standard_order = R
            # we also have to define a "map" from F to R
            F._to_standard_order = lambda f: R([R0(c) for c in f.list()])
        return F._standard_order


def numerator_of_ff_element(a):
    r""" Return the numerator of an element of a function field.

    """
    F = a.parent()
    if F is F.rational_function_field():
        return a.numerator()
    else:
        R = standard_order(F)
        return F._to_standard_order(denominator_of_ff_element(a)*a)


def denominator_of_ff_element(a):
    r""" Return the denominator of an element of a function field.

    INPUT:

    - ``a`` -- an element of a function field `F`

    OUTPUT:

    the *denominator* of `a`; this is a minimal element `c` of the base order
    `R_0` of `F` such that `c\cdot a` lies in the standard order `R` of `F`.

    Since the base order `R_0=k[x]` is a polynomial ring over a field, we
    obtain a unique output by demanding that `c` is monic.

    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + x^3 +1)
        sage: a = y/x + 1/(x+1)
        sage: denominator_of_ff_element(a)
        x^2 + x
        sage: b = numerator_of_ff_element(a); b
        (x + 1)*y + x

        sage: b.parent()
        Univariate Quotient Polynomial Ring in y over Univariate Polynomial Ring
        in x over Finite Field of size 2 (using GF2X) with modulus y^2 + x^3 + 1

    """
    from sage.all import lcm
    F = a.parent()
    if F is F.rational_function_field():
        return a.denominator()
    else:
        a = a.list()
        return lcm(a[i].denominator() for i in range(F.degree()))


def numerator_of_polynomial(f):
    r""" Return the numerator of a polynomial over a function field.

    INPUT:

    - ``f`` -- a univariate polynomial over a standard function field `F`

    OUTPUT:

    the polynomial `\tilde{f}=d\cdot f` with coefficients in the standard
    order `R` of `F`, where `d` is the *denominator* of `f`.

    The denominator `d` of `f` is an element of the standard order `R_0` of
    the rational base field `F_0=k(x)` of `F`, which is 'minimal' with the
    property that `d\cdot f` has coefficients in `R`. As `R_0=k[x]` is a
    UFD and `R` a free `R_0`-module, this determines `d` uniquely up to unit.
    We obtain a unique output by demanding that `d` is normalized as polynomial
    in `k`.

    """
    from sage.all import PolynomialRing
    F = f.base_ring()
    R = standard_order(F)
    S = PolynomialRing(R, f.variable_name())
    ft = denominator_of_polynomial(f)*f
    return S([numerator_of_ff_element(ft[i]) for i in range(ft.degree() + 1)])


def denominator_of_polynomial(f):
    r""" Return the denominator of a polynomial over a function field.

    INPUT:

    - ``f`` -- a univariate polynomial over a standard function field `F`

    OUTPUT:

    the *denominator* of `f`.

    The denominator `d` of `f` is an element of the standard order `R_0` of
    the rational base field `F_0=k(x)` of `F`, which is 'minimal' with the
    property that `d\cdot f` has coefficients in `R`. As `R_0=k[x]` is a
    UFD and `R` a free `R_0`-module, this determines `d` uniquely up to unit.
    We obtain a unique output by demanding that `d` is normalized as polynomial
    in `k`.

    EXAMLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + x^3 + 1)
        sage: S.<T> = F[]
        sage: f = x*T^2 + T/y + 1/x
        sage: d = denominator_of_polynomial(f); d
        x^4 + x

        sage: d*f
        (x^5 + x^2)*T^2 + x*y*T + x^3 + 1

        sage: ft = numerator_of_polynomial(f); ft
        (x^5 + x^2)*T^2 + x*y*T + x^3 + 1

        sage: ft.parent()
        Univariate Polynomial Ring in T over Univariate Quotient Polynomial Ring
        in y over Univariate Polynomial Ring in x over Finite Field of size 2
        (using GF2X) with modulus y^2 + x^3 + 1

    """
    from sage.all import lcm
    F = f.base_ring()
    R = standard_order(F)
    R0 = R.base()
    return lcm(denominator_of_ff_element(f[i]) for i in range(f.degree() + 1))


def quasi_inverse(a):
    r""" Return a quasi-inverse of an integral element of a function field.

    INPUT:

        - ``a`` -- a nonzero element of the standard order `R` of a
          nonrational function field `F`

    OUTPUT:

    a *quasi-inverse* of `a`; this is an element `b` of `R` such that
    `c:=a\cdot b` lies in the base ring `R_0=k[x]` (the standard order of the
    rational base field of `F`), and such that `c` is of minimal degree among
    such element.

    """
    if a.is_zero():
        raise ZeroDivisionError()
    R = a.parent()
    A = a.polynomial()
    B = R.modulus()
    R, S, T = xgcd_of_polynomials_over_ufd(A, B)
    # we have R = S*A + T*B
    assert R.degree() == 0
    U = S.gcd(T)  # Sage's implementation uses the subresultant alg
    return (S // U)(R.gen())


# ----------------------------------------------------------------------------

#  probably not needed any more


def primitive_part(f):
    r""" Return the primitive part of a polynomial over a rational
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

    ``f``, ``g`` -- two poynomials over an integral domain `R`

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
