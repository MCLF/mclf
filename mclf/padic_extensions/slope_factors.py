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
the slope factorization, up to a given precision `N`.

"""

from mac_lane import GaussValuation
from sage.geometry.newton_polygon import NewtonPolygon
from sage.rings.integer_ring import IntegerRing
ZZ = IntegerRing()


def slope_factors(f, vK, precision, slope_bound=0):
    r"""
    Return the slope factorizaton of a polynomial over a discretely valued field.

    INPUT:

    - ``f`` -- a monic polynomial over a field `K`
    - ``vK`` -- a discrete valuation on `K` such that `f` for which `f` is integral
    - ``precision`` -- a positive integer
    - ``slope_bound``

    OUTPUT: a dictionary ``F`` whose keys are the pairwise distinct slopes `s_i`
    of the Newton polygon of `f` and the corresponding value is a monic and integral
    polynomial whose Newton polygon has exactly one slope `s_i`, and

    .. MATH::

            v_K( f - \prod_i f_i ) > N,

    where `N` is ``precision`` plus the valuation of the first nonzero
    coefficient of `f`.

    If ``slope_bound`` is given, then only those factors with slope < ``slope_bound``
    are computed.

    TODO:

    It would be enough if the relative `p`-adic precision of the coefficients of
    of the `f_i` we as givne by ``precision``. This is a weaker condition
    than above, and it may allow for a faster computation.

    """
    vK = vK.scale(1/vK(vK.uniformizer()))
    assert not f.is_constant(), "f must be nonconstant"
    assert f.is_monic(), "f must be monic"
    NP = NewtonPolygon([(i,vK(f[i])) for i in range(f.degree()+1)])
    slopes = NP.slopes(False)
    vertices = NP.vertices()
    assert all( s <= 0 for s in slopes), "f must be integral"
    # assert vertices[1][1] < N, "precision is too small to see the first slope"
    pi = vK.uniformizer()
    f_1, f_2 = first_slope_factor(f, vK, precision)
    # now f_1 is the factor with the first slope, and f_2 is the product of
    # the remaining factors
    if f_2.is_constant() or slopes[1] >= slope_bound:
        return {slopes[0]:f_1}
    else:
        F = slope_factors(f_2, vK, precision, slope_bound)
        F[slopes[0]] = f_1
        return F


def first_slope_factor(f, vK, precision):
    r"""
    Return the factor corresponding to the first slope.

    INPUT:

    - ``f`` -- a monic polynomial over a field `K`
    - ``vK`` -- a discrete valuation on `K` such that `f` for which `f` is integral
    - ``precision`` -- a positive integer

    OUTPUT: a pair `(f_1, f_2)`, where `f_1` is the first slope factor of `f`,
    and `f_2` is the product of the remaining factors.

    """
    vK = vK.scale(1/vK(vK.uniformizer()))
    R = f.parent()
    v0 = GaussValuation(R, vK)
    NP = NewtonPolygon([(i,vK(f[i])) for i in range(f.degree()+1)])
    slopes = NP.slopes(False)
    vertices = NP.vertices()
    if len(slopes) == 1:
        return f, f.parent().one()

    # now has at least two slopes
    k = vertices[1][0]
    mu = vertices[1][1]
    # the kth coefficients of f has valuation mu, and represents the second
    # vertex of the Newton polygon; it follows that we can factor f = f_1*f_2
    # where f_1 has degree k, and the constant term of f_2 has valuation mu
    s = slopes[1]
    pi = vK.uniformizer()
    x = f.parent().gen()
    g = f(pi**ZZ(-s)*x)
    nu = v0(g)
    g = g*pi**(-nu)
    assert vK(g[k]) == 0
    N = max(vK(g[i]) for i in range(g.degree()+1)) + precision
    g1, g2 = factor_with_positive_slope(g, vK, N)
    f1 = g1(pi**(ZZ(s))*x).monic()
    NP1 = NewtonPolygon([(i, vK(f1[i])) for i in range(f1.degree()+1)])
    assert len(NP1.slopes(False)) == 1
    assert NP1.slopes(False)[0] == slopes[0]
    f2 = g2(pi**(ZZ(s))*x).monic()
    assert f.degree() == f1.degree() + f2.degree()
    return f1, f2


def factor_with_positive_slope(f, vK, N):
    r"""
    Return the factorization into a factor with positive slopes and the rest.

    INPUT:

    - ``f`` -- a nonconstant polynomial over a field `K` (not necessarily monic)
        whose reduction to the residue field of `v_K` is nonzero
    - ``vK`` -- a discrete valuation on `K` for which `f` is integral
    - ``N`` -- a positive integer

    OUTPUT: a pair `(f_1,f_2)` of polynomials such that `f_1` has only strictly
    negative slopes, `f_2` has only nonnegative slopes, and

    .. MATH::

            v_K( f - f_1\cdot f_2 ) > N.

    """
    R = f.parent()
    x = R.gen()
    m = vK(f.leading_coefficient())
    assert m < N, "not enough precision: N = %s but m = %s"%(N,m)
    pi = vK.uniformizer()
    e = 1/vK(pi)
    vK = vK.scale(e)
    v0 = GaussValuation(R, vK)
    # we make sure that vK(pi) = 1
    # but now the precision gets a factor e
    Kb = vK.residue_field()
    fb = f.map_coefficients(lambda c: vK.reduce(c), Kb)
    k = min([i for i in range(fb.degree()+1) if fb[i] != 0])
    if k == 0:
        return R.one(), f
    f1b = fb.parent().gen()**k
    f2b = fb.shift(-k)
    assert fb == f1b*f2b
    f1 = x**k
    f2 = R([vK.lift(f2b[i]) for i in range(f2b.degree()+1)])
    d0 = 0
    while True:
        Delta = f - f1*f2
        d = v0(Delta)
        # we check that we have made progress:
        assert d > d0
        if d*e > N:
            return f1, f2
        else:
            d0 = d
            delta = (Delta*pi**(-d)).map_coefficients(lambda c:vK.reduce(c), Kb)
            g1b, g2b =  x_to_k_presentation(delta, f2b, k)
            # now  delta = g1b*f2b + g2b*x^k
            g1 =  R([vK.lift(g1b[i]) for i in range(g1b.degree()+1)])
            g2 =  R([vK.lift(g2b[i]) for i in range(g2b.degree()+1)])
            f1 = f1 + pi**d*g1
            f2 = f2 + pi**d*g2


def x_to_k_presentation(f, g, k):
    r"""
    Write ``f`` as ``f = a*g + b*x^k``.

    INPUT:

    - ``f``, ``g`` -- polynomials over a field k; the constant term of ``g``
      does not vanish
    - ``k`` -- a positive integer

    OUTPUT: a pair `(a, b)` of polynomials such that

    .. MATH::

            f = a\cdot g + b\cdot x^k.

    """
    R = f.parent()
    assert g in R, "f and must lie in the same polynomial ring"
    c = g[0]
    assert c != 0, "the constant coefficnet of g must be nonzero"
    x = R.gen()
    b = f
    a = R.zero()
    l = min([i for i in range(f.degree()+1) if f[i] != 0])
    while l < k:
        # x^(l-1) divides b, but not x^l
        a = a + (b[l]/c)*x**l
        b = f - a*g
        l = l + 1
    assert (x**k).divides(b)
    return a, b.shift(-k)
