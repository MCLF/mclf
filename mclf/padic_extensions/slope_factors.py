r"""
Slope factors
=============

Factoring polynomials over `p`-adic fields according to the slopes
------------------------------------------------------------------

Let `K` be a field which is complete with respect to a discrete valuation `v_K`.
Let `\pi` denote a uniformizer for `v_K`, and let `f`\in K[x]` be a monic
polynomial which is integral with respect to `v_K`. Then there exists a
unique factorization of `f` into monic and integral polynomials

.. MATH::

        f = f_1\cdot \ldots \cdot f_r,

such that each `f_i` has a Newton polygon with exactly one slope `s_i`, and
`s_1 < s_2 < \ldots <s_r`. The `s_i` are exactly the slopes of the Newton polygon
of `f`, and the degree of `f_i` is equal to the lenght of the segment with
slope `s_i`.

We call the factorization just described the **slope factorization** of `f`,
and the factors `f_i` the **slope factors** of `f`.

In this module we realize a function ``slope_factor(f, vK, N)`` which computes
the slope factorization, up to a given **relative** precision `N`. This means
that our result is a list of monic polynomials `g_i` with slope `s_i` which agree
with the true slope factors `f_i` up to relative and coefficientwise
v_K`-adic precision ``precision``. In particular, it follows that

.. MATH::

      v_K( f - \prod_i g_i) > ``precision``.

The algorithm is based on a straightforward application of Hensel's Lemma. To
make sure we get the relative precision right, we first scale the polynomial
`f` for each of its slope `s` in such a way that the segment of the Newton
polygon with slope `s` is moved to a segment of slope `0` with ordinate `0`.

"""

from mac_lane import GaussValuation
from sage.geometry.newton_polygon import NewtonPolygon
from sage.rings.integer_ring import IntegerRing
ZZ = IntegerRing()


def slope_factors(f, vK, precision, reduce_function, slope_bound=0):
    r"""
    Return the slope factorizaton of a polynomial over a discretely valued field.

    INPUT:

    - ``f`` -- a monic polynomial over a field `K`
    - ``vK`` -- a discrete valuation on `K` such that `f` for which `f` is integral
    - ``precision`` -- a positive integer
    - ``reduce_function`` -- a function which takes as input an element of `K`
      and returns a simpler approximation; the approximation is with relative
      precision ``precsion``
    - ``slope_bound`` -- a rational number (default: `0`)

    OUTPUT: a dictionary ``F`` whose keys are the pairwise distinct slopes `s_i`
    of the Newton polygon of `f` and the corresponding value is a monic and integral
    polynomial whose Newton polygon has exactly one slope `s_i`, and

    .. MATH::

            v_K( f - \prod_i f_i ) > N,

    where `N` is ``precision`` plus the valuation of the first nonzero
    coefficient of `f`.

    If ``slope_bound`` is given, then only those factors with slope < ``slope_bound``
    are computed.

    """
    vK = vK.scale(1/vK(vK.uniformizer()))
    assert not f.is_constant(), "f must be nonconstant"
    assert f.is_monic(), "f must be monic"
    NP = NewtonPolygon([(i,vK(f[i])) for i in range(f.degree()+1)])
    slopes = NP.slopes(False)
    vertices = NP.vertices()
    assert all( s <= 0 for s in slopes), "f must be integral"
    pi = vK.uniformizer()
    F = {}
    for i in range(len(slopes)):
        s = slopes[i]
        if s < slope_bound:
            g = factor_with_slope(f, vK, s, precision, reduce_function)
            F[s] = g
    return F


def factor_with_slope(f, vK, s, precision, reduce_function):
    r"""
    Return the factor with slope `s`.

    INPUT:

    - ``f`` -- a monic polynomial over a field `K`
    - ``vK`` -- a discrete valuation on `K` such that `f` for which `f` is integral
    - ``s`` -- a nonpositive **integer**
    - ``precision`` -- a positive integer

    OUTPUT: a monic and integral polynomial `g` which approximates the factor
    of `f` with slope `s`. We assume that `s` is a slope of `f` (hence `g`)
    will be nonconstant. The precision of the approximation is such that the
    relative precision of the coefficients of `g` is at least ``precision``.

    """
    vK = vK.scale(1/vK(vK.uniformizer()))
    R = f.parent()
    x = R.gen()
    pi = vK.uniformizer()
    v0 = GaussValuation(R, vK)
    f1 = f(pi**ZZ(-s)*x)
    f2 = reduce_function(f1 * pi**(-v0(f1)))
    g = factor_with_slope_zero(f2, vK, precision, reduce_function)
    g = reduce_function(g)
    return g(pi**ZZ(s)*x).monic()


def factor_with_slope_zero(f, vK, N, reduce_function):
    r"""
    Return the factor of `f` with slope zero.

    INPUT:

    - ``f`` -- a nonconstant polynomial over a field `K` (not necessarily monic)
        whose reduction to the residue field of `v_K` is nonconstant.
    - ``vK`` -- a normalized discrete valuation on `K` for which `f` is integral
    - ``N`` -- a positive integer

    OUTPUT: a pair `(f_1,f_2)` of polynomials such that `f_1` has slope zero,
    `f_2` has only nonzero slopes, and

    .. MATH::

            v_K( f - f_1\cdot f_2 ) > N.

    """
    R = f.parent()
    x = R.gen()
    pi = vK.uniformizer()
    v0 = GaussValuation(R, vK)
    Kb = vK.residue_field()
    fb = f.map_coefficients(lambda c: vK.reduce(c), Kb)
    k = min([i for i in range(fb.degree()+1) if fb[i] != 0])
    gb = fb.shift(-k).monic()
    g = R([vK.lift(gb[i]) for i in range(gb.degree()+1)])
    print "g = ", g
    q, r0 = f.quo_rem(g)
    qb = q.map_coefficients(lambda c:vK.reduce(c), Kb)
    assert qb != 0
    m = v0(r0)
    r = r0*pi**(-m)

    while m <= N:
        # we have f = q*g + pi^m*r
        rb = r.map_coefficients(lambda c:vK.reduce(c), Kb)
        ab, bb = pol_linear_combination(rb, qb, gb)
        # now  rb = ab*qb + bb*gb and deg(ab) < deg(gb)
        a =  R([vK.lift(ab[i]) for i in range(ab.degree()+1)])
        b =  R([vK.lift(bb[i]) for i in range(bb.degree()+1)])
        r0 = r - (a*q + b*g + pi**m*a*b)
        g = g + pi**m*a
        q = q + pi**m*b
        r = r0*pi**(-1)
        m = m + 1
    return g


def pol_linear_combination(f, g, h):
    r"""
    Write ``f`` as ``f = a*g + b*h`` with ``deg(a) < deg(h).

    INPUT:

    - ``f``, ``g``, ``h`` -- polynomials over a field k

    We assume that `g` and `h` are relatively prime.

    OUTPUT: a pair `(a, b)` of polynomials such that

    .. MATH::

            f = a\cdot g + b\cdot h

    and such that `deg(a) < deg(h)`.

    """
    R = f.parent()
    d, A, B = g.xgcd(h)
    # now 1 = d = A*g + B*h
    C, a = (f*A).quo_rem(h)
    b = B*f + C*g
    return a, b
