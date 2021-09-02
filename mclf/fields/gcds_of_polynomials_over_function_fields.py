# -*- coding: utf-8 -*-
"""
Computing gcds of univariate polynomials over function fields
=============================================================

To compute the gcd of two univariate polynomials over any field one can use
the standard euclidean algorithm. However, if the base field is not a finite
field, then the basic variant of the euclidean algorithm is very inefficient
because of coefficient explosion.

If the base field `K` is the fraction field of a euclidean domain `R` which
itself has an efficient method for computing the gcd (e.g. if
`K = \mathbb{Q}` or `K = k(x)` for a finite field `k`) then there exist
very good variants of Euclid's algorithm, e.g. the subresultant PRS algorithm.
See e.g. [Cohen_CCANT]_, Chapter 3.2-3.2.

Unfortunately, Sage uses only the basic variant of Euclid's algorithm for
polynomials over function fields, which is useless except for polynomials of
very small degree. In this module we therefore implement our own algorithm, but
this is work in progress.

If `K=k(x)` is a rational function field there is an easy trick: we simply
replace `K` by the fraction field of the polynomial ring `k[x]`; the latter
has an inbuild implementation of the subresultant PRS algorithm, which is
reasonably fast if `k` is a finite field.

If `K` is a nonrational function field, we assume it's in standard form, so
`K` is a finite simple extension of a ratioanl function field `K_0=k(x)`. For
this case we implement a variant of the *primitive PRS algorithm* suggested by
van Hoeij and Monogan, see [vanHoeijMonogan]_.

To further improve the performance withut too much work we could use reduction
at a random place of the function field to implement a very fast test for two
polynomials to be relatively prime, as suggested at the end of Section 3.6.2
of [Cohen_CCANT]_.

REFERENCES:

.. [Cohen_CCANT] \H. Cohen, *A course in computational algebraic number theory*.

.. [vanHoeijMonogan] \M. van Hoeij, \M. Monogan, *Algorithms for Polynomial GCD
                     Computation over Algebraic Function Fields*.



"""


def gcd_of_univariate_polynomials(F, f, g):
    r""" Return the gcd of the polynomial `f` and `g`.

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

    For nonrational function fields the only inbuild method for computing the
    gcd of univariate polynomials is the standard (monic) euclidean algorithm.
    It is unusable except for very samll examples, due to coefficient swell.
    Our own implementation is much better, but certainly not optimal. ::

        sage: F = F.extension(T^2 + x^3 + 1, "y")
        sage: S.<T> = F[]
        sage: y = F.gen()
        sage: r = y*T^2 + T + x
        sage: s = T^2 + T + x^2 + 1
        sage: gcd_of_univariate_polynomials(F, r, s)
        1

        sage: gcd_of_univariate_polynomials(F, r*s^5, r*(s^5 + x))
        T^2 + ((1/(x^3 + 1))*y)*T + (x/(x^3 + 1))*y

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
        # we use the algorithm described on p 303 of van Hoeij and Monogan
        # (a modification of the primitive PRS algorithm)
        if f.degree() < g.degree():
            f, g = g, f
        A = primitive_part(f)
        B = primitive_part(g)
        while not B.is_zero():
            # by our definition, the leading coefficient of the primitive part
            # is a polynomial in x
            _, R = A.pseudo_quo_rem(B)
            A, B = B, primitive_part(R)
        return A.monic()


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
    See Algorithm 3.2.10, Algorithm 3.3.1 and Exercise 5 in [Cohen_CCANT]_.


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
        D, V, U = xgcd_of_polynomials_over_ufd(B, A, algorithm)
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
            beta = (U1.content_ideal() + V1.content_ideal()).gen()
        else:
            assert S(beta).divides(R), "alpha = {}, beta = {}, R = {}".format(alpha, beta, R)
        U1 = U1 // beta
        V1 = V1 // beta
        R0, R1 = R1, R // beta
        if algorithm == "subresultant":
            g = R0.leading_coefficient()
            h = g**delta * h**(1 - delta)
        assert R1 == U1*A + V1*B, "A = {}, \n B = {}".format(A, B)

    return R0, U0, V0


def denominator_of_ff_element(f):
    r""" Return the denominator of an element of a function field.

    INPUT:

    - ``f`` -- an element of a function field `F`

    OUTPUT:

    the *denominator* of `f`.

    If `F = k(x)` is a rational function field, then the internal representation
    is `f=g/h`, where `g, h` are (uniquely determined) polynomials in `x` and
    `h` is monic. Then `h` is the denominator of `f`.

    If `F` is a standard nonrational function field, i.e. a finite simple
    extension `F/F_0` of a rational function field `F_0`, then the internal
    representation of `f` is as a polynomial over `F_0`, say
    `f = f_0 + f_1y + \ldots + f_ny^n`. In this case the denominator of `f`
    is defined as the monic lcm of the denominators of the coefficients `f_i`.

    So in both cases the output of this method is a univariate polynomial over
    the constant base field of `F`; it is not an element of `F` but can be
    coerced into `F`.


    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + x^3 +1)
        sage: f = y/x + 1/(x+1)
        sage: g = denominator_of_ff_element(f); g
        x^2 + x

        sage: g.parent()
        Univariate Polynomial Ring in x over Finite Field of size 2 (using GF2X)

        sage: h = numerator_of_ff_element(f); h
        (x + 1)*y + x

        sage: h.parent()
        Function field in y defined by y^2 + x^3 + 1

    """
    from sage.all import lcm
    F = f.parent()
    if F is F.rational_function_field():
        return f.denominator()
    else:
        f = f._x
        return lcm(f[i].denominator() for i in range(f.degree() + 1))


def numerator_of_ff_element(f):
    r""" Return the numerator of an element of a function field.

    INPUT:

    - ``f`` -- an element of a function field `F`

    OUTPUT:

    the *numerator* of `f`, which is defined as `d(f)\cdot f`, where
    `d(f)` is the *denominator* of `f`.

    If `F = k(x)` is a rational function field, then the internal representation
    is `f=g/h`, where `g, h` are (uniquely determined) polynomials in `x` and
    `h` is monic. Then `g` is the numerator and `h` the denominator of `f`.

    If `F` is a standard nonrational function field, i.e. a finite simple
    extension `F/F_0` of a rational function field `F_0`, then the internal
    representation of `f` is as a polynomial over `F_0`, say
    `f = f_0 + f_1y + \ldots + f_ny^n`. In this case the denominator of `f`
    is defined as the monic lcm of the denominators of the coefficients `f_i`.
    It follows that the numerator of `f` has an internal representation as
    a polynomial whose coefficients are polynomials in the generator of `F_0`.

    .. NOTE::

        If `f` lies in a rational function field, then the output of this method
        is an element of a polynomial ring, whcih is not a field. In contrast,
        if `f` lies in a nonrational function field `F` then the output of this
        method is an elemet of the function field `F`.

        The rational for this distinction is that in the case of a nonrational
        function field there is no reasonable implementation of the subring
        in which the numerator lives.

    """
    F = f.parent()
    if F is F.rational_function_field():
        return f.numerator()
    else:
        return denominator_of_ff_element(f)*f


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


def numerator_of_polynomial(f):
    r""" Return the numerator of a polynomial over a function field.

    INPUT:

    - ``f`` -- a univariate polynomial over a standard function field `F`

    OUTPUT:

    the polynomial `\tilde{f}=d(f)\cdot f`, where `d(f)` is the *denominator*
    of `f`.

    The denominator `d=d(f)` of `f` is an integral element of `F` such that the
    *numerator* `\tilde{f}=d\cdot f` of `f` is of the form

    .. MATH::

        \tilde{f} = f_0 + f_1\cdot T + \ldots + f_n\cdot T^n,

    where each coefficient is an integral element of `f` and moreover the
    leading coefficient `{\rm lc}(\tilde{f})=f_n` lies in the rational base field
    `F_0 = k(x)` of `F`.

    Here an element of `F` is called *integral* if its denominator is equal to
    `1`. Note that this implies that the leading coefficient `f_n` is a
    polynomial in `x`. All coefficients `f_i` of `\tilde{f}` have an internal
    representation as polynomials over `F_0` whose coefficients are actually
    polynomials in `x`.`

    .. NOTE::

        If `F=k(x)` is a rtional function field then the output of this method
        is a polynomial over the polynomial ring `k[x]`.

        If `F/F_0` is a nonrational function field with rational base field
        `F_0=k(x)` then the output is a polynomial over `F` whose coefficients
        are integral in the sense that their denominator is equal to one.

        The rational for this distinction is that the polynomial ring `k[x]`
        has a very good implementation, but the same cannot be said about
        the subring of integral elements of `F` in the nonrational case.

    """
    from sage.all import PolynomialRing
    F = f.base_ring()
    if F is F.rational_function_field():
        R = F._ring
        S = PolynomialRing(R, f.variable_name())
        f = denominator_of_polynomial(f)*f
        return S([f[i].numerator() for i in range(f.degree() + 1)])
    else:
        return denominator_of_polynomial(f)*f


def primitive_part(f, is_integral=False):
    r""" Return the principal part of a polynomial over a function field.

    INPUT:

    - ``f`` -- a nonzero univariate polynomial over a standard function field `F`.
    - ``is_integral`` -- a boolean (default: "False")

    OUTPUT:

    The *primitive part* `\tilde{f}` of `f`, defined as follows.

    If `F=k(x)` is a rational function field, then `\tilde{f}` is the unique
    associate of `f` with coefficients in `k[x]`, such that the gcd of all
    coefficients is one, and such that the leading coefficient is normalized.

    If `F/F_0` is nonrational, a finite simple extension of its rational base
    field `F_0=k(x)`, then we have to modify this definition a bit because
    we do not have any natural order of `F` which is guaranteed to be a UFD.
    Instead, we define `\tilde{f}` as the unique associate of `f` with the
    following properties:

    - the coefficients of `f` are all *integral* in the sense that their
      denominators are all one,
    - we cannot divide `\tilde{f}` by a nonunit in `R_0=k[x]` without loosing
      the first property,
    - the leading coefficient of `f` is a monic element of `R_0=k[x]`.


    If ``is_integral`` is ``True`` then we assume that the first of the above
    conditions already hold for `f`.


    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + y + x^3)
        sage: S.<T> = F[]
        sage: principal_part(T^2/y + x*T + 1)
        T^2 + x*y*T + y

    """
    from sage.all import gcd
    if f.is_zero():
        return f
    F = f.base_ring()
    if not is_integral:
        f = numerator_of_polynomial(f)
    if F is F.rational_function_field():
        c = gcd(f[i].numerator() for i in range(f.degree() + 1))
        return f/c
    else:
        c = quasi_inverse(f.leading_coefficient())
        f = c*f
        a = f.leading_coefficient()
        for i in range(f.degree()):
            if a.is_unit():
                break
            b = gcd(f[i]._x.list())
            # gcd of the coefficients of f[i] as polynomial in y
            c = c.gcd(b)
        return f/a


def quasi_inverse(a):
    r""" Return a quasi-inverse of an integral element of a function field.

    INPUT:

        - ``a`` -- a nonzero integral element of a nonrational function field `F`

    OUTPUT:

    a *quasi-inverse* of `a`; this is an integral element `b` of `R` such that
    `c:=a\cdot b` lies in the base ring `R_0=k[x]` (the standard order of the
    rational base field of `F`), and such that `c` is of minimal degree among
    such element.

    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(GF(2))
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + y + x^3 + x)
        sage: quasi_inverse(y)
        y + 1
    """
    from sage.all import PolynomialRing
    if a.is_zero():
        raise ZeroDivisionError()
    F = a.parent()
    F0 = F.rational_function_field()
    R0 = F0._ring
    R = PolynomialRing(R0, F.variable_name())
    A = a._x
    assert denominator_of_polynomial(A) == 1, "a is not integral"
    A = R(A)
    B = R(primitive_part(F.polynomial()))
    D, U, V = xgcd_of_polynomials_over_ufd(A, B)
    # we have D = U*A + V*B
    assert D.degree() == 0
    C = U.gcd(V)  # Sage's implementation uses the subresultant alg
    b = (U // C)(F.gen())
    return b
