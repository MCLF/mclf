r"""
Semistable reduction of superelliptic curves of degree `p`


Let `K` be a field of characteritic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`. For the time being, we
assume that `K` is a number field.

Let `f\in K[x]` be a polynomial over `K` which is not a `p`th power and whose
radical has degree at least three. We consider the smooth projective  curve
`Y` over `K` defined generically by the equation

.. MATH::

           Y: y^p = f(x).

Our goal is to compute the semistable reduction of `Y` and to extract
nontrivial arithmetic information on `Y` from this.

More precisely, ...




AUTHORS:

- Stefan Wewers (2017-07-29): initial version


EXAMPLES::

<Lots and lots of examples>


TO DO:

- more doctests


"""

#*****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.structure.sage_object import SageObject
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.function_field.constructor import FunctionField
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import Infinity
from sage.functions.other import floor
from mac_lane import *
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.affinoid_domain import *




class Superp(SageObject):
    r"""
    Return the superelliptic curve of degree ``p`` defined by ``f``,
    relative to the `p`-adic valuation ``vK``.

    A "superelliptic curve" `Y` over a field `K` is a smooth projective curve
    over `K` defined generically by an equation of the form

    .. MATH::
              y^n = f(x),

    where `f` is a nonconstant polynomial over `K` in `x`.

    - the gcd of `n` and the multiplicities of the irreducible factors of `f`  is one,
    - the exponent `n` is invertible in `K`.

    We call `n` the "degree" of the superelliptic curve `Y`. Formulated more
    geometrically, a superelliptic curve of degree `n` is a smooth projective
    curve together with a cyclic cover `Y\to X:=\mathbb{P}_K^1` of degree `n`.

    Here we assume that the degree is a prime `p`. Moreover, we fix a `p`-adic
    valuation `v_K` on `K` (i.e. a discrete valuation with residue
    characteristic `p`). Note that this implies that `K` has characteristic zero.

    The goal is to compute the semistable reduction of `Y` relative to `v_K`,
    and some arithmetic invariants associated to it (for instance the "exponent
    of conductor" of `Y` with respect to `v_K`). The method to compute the
    semistable reduction in this particular case is explained in detail in

    - [We17] S. Wewers, Semistable reduction of superelliptic curves of degree p, \
      preprint, 2017.

    INPUT:

    - ``f`` -- a nonconstant poylnomial over a field `K`
    - ``vK`` -- a discrete valuation on `K`
    - ``p`` -- a prime number

    Here the residue characteristic of ``vK`` must be equal to the prime ``p``.
    Moreover, ``f`` must be monic, integral with respect to ``vK`` and
    of degree prime to ``p``.

    OUTPUT: the object representing the superelliptic curve

    .. MATH::

           Y: y^p = f(x).

    EXAMPLES:

    ::

        sage: K = QQ
        sage: vK = pAdicValuation(K, 3)
        sage: R.<x> = K[]
        sage: f = x^4 + x^2 + 1
        sage: Y = Superp(f, vK, 3)
        sage: Y
        The superelliptic curve Y: y^3 = x^4 + x^2 + 1 over Rational Field with 3-adic valuation
        sage: U_et = Y.compute_etale_locus()
        sage: U_et
        Affinoid with 3 components:
        Elementary affinoid defined by
        v(x) >= 3/4
        Elementary affinoid defined by
        v(x + 7) >= 5/4
        Elementary affinoid defined by
        v(x + 2) >= 5/4

    .. NOTES::

    For the time being, we need to make the following additional assumptions
    on `f`:

    - `f` must be monic, integral with respect to `v_K` and of degree \
      prime to `p`

    This restriction is preliminary and will be removed in a future version.
    Note that a superelliptic curve of degree `p` can be written in the required
    form if and only if the map `Y\to X` has a `K`-rational branch point.

    """

    def __init__(self, f, vK, p):

        R = f.parent()
        assert R.base_ring() is vK.domain(), "the domain of vK must be the base field of f"
        assert p == vK.residue_field().characteristic(), "the exponent p must be the residue characteristic of vK"
        assert f.is_monic(), "f must be monic"
        self._f = f
        self._vK = vK
        self._p = p
        FX = FunctionField(vK.domain(), names=R.variable_names())
        S = PolynomialRing(FX, 'T')
        T = S.gen()
        FY = FX.extension(T**p-FX(f), 'y')
        self._FX = FX
        self._FY = FY
        X = BerkovichLine(FX, vK)
        self._X = X

    def __repr__(self):

        return "The superelliptic curve Y: y^%s = %s over %s with %s"%(self._p,
                        self._f, self._vK.domain(), self._vK)

    def compute_etale_locus(self):
        r"""
        Return the etale locus of the cover `Y\to X`.

        The superelliptic curve `Y` is, by definition, a cyclic cover

        .. MATH::

                   \phi: Y \to X

        of degree `p` of the projective line `X` over the base field `K`.
        We consider `X` and `Y` as analytic spaces over the completion of `K`
        at the base valuation `v_K`. Let

        .. MATH::

              \bar{\phi}: \bar{Y} \to \bar{X}

        denote the *semistable reduction* of the cover `Y\to X`.
        The **etale locus** is an affinoid subdomain `X^{et}` of `X`
        consisting of those points which specialize to a point on `\bar{X}`
        above which the map `\bar{\phi}` is etale.

        While the affinoid `X^{et}` is determined by the semistable reduction
        of the cover `\phi`, conversely `X^{et}` contains a lot of information
        on the semistable reduction. The main result of

        - [We17]: Semistable reduction of superelliptic curves of degree p, \
          preprint, 2017

        gives an explicit description of the affinoid `X^{et}` as a union
        of rational domains defined by rational functions which can be
        easily computed in terms of the polynomial `f` defining `Y`.

        EXAMPLES:

        ::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = pAdicValuation(K, 2)
            sage: R.<x> = K[]
            sage: f = x^3 + x^2 + 1
            sage: Y = Superp(f, vK, 2)
            sage: Y
            The superelliptic curve Y: y^2 = x^3 + x^2 + 1 over Rational Field with 2-adic valuation
            sage: Y.compute_etale_locus()
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(x^4 + 4/3*x^3 + 4*x + 4/3) >= 8/3


        We check Example 4.14 from [BouWe16]. The original equation is
        `y^2 = f(x) = 2*x^3 + x^2 + 32`, and `f` is not monic, as required.
        To fix this, we substitute `x/2` and multiply with `4`. Then the
        new equation is `y^2 = x^3 + x^2 + 128`: ::

            sage: f = x^3 + x^2 + 128
            sage: Y = Superp(f, vK, 2)
            sage: Y.compute_etale_locus()
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(1/x) >= -5/2
            v(x) >= 2

    .. NOTES::

    At the moment, the construction of the superelliptic curve `Y` requires that
    the polynomial `f` defining `Y` is monic, integral with respect to `v_K`
    and of degree prime to `p`. The motivation for this restriction, and its
    result is that the etale locus is contained in the closed unit disk.

    """

        X = self._X
        FX = self._FX
        f = self._f
        p = self._p
        n = f.degree()
        m = floor(n/p)
        H, G = p_approximation_generic(f,p)
        # b = [FX(H[i]) for i in range(n+1)]
        c = [FX(G[k]) for k in range(n+1)]
        d =[c[k]*f**k for k in range(n+1)]
        pl = 1
        while pl <= m:
            pl = pl*p

        a = [f]
        for i in range(1, n+1):
            a.append(a[i-1].derivative()/i)
        a = [a[i]/f for i in range(n+1)]

        pi = self._vK.uniformizer()
        delta = [ c[pl]**(p-1) * pi**(-p) ]
        delta += [ c[pl]**(i*(p-1)) * a[i]**(-pl*(p-1)) * pi**(-i*p)
                   for i in range(1, n+1) ]
        delta += [ c[pl]**(k*(p-1)) * c[k]**(-pl*(p-1)) * pi**(-p*(k-pl))
                   for k in range(m+1, n+1) if k != pl ]

        X_et = RationalDomainOnBerkovichLine(X, delta[0])
        for i in range(1, len(delta)):
            X_et = X_et.union(RationalDomainOnBerkovichLine(X, delta[i]))
            X_et.simplify()
        return X_et.intersection(ClosedUnitDisk(X))



#-----------------------------------------------------------------------




def p_approximation(f,p):
    r"""
    Return the `p`-approximation of ``f``.

    INPUT:

    - ``f`` -- a polynomial of degree `n` over a field `K`, with nonvanishing
               constant coefficient
    - ``p`` -- a prime number

    OUTPUT:

    Two polynomials `h`,`g` in `K[x]`, such that

    - `f=a_0(h^p+g)`, where `a_0` is the constant coefficient of `f`
    - `r:=deg(h)<=n/p`, and
    - `x^(r+1)` divides `g`

    Note that `h,g` are uniquely determined by these conditions.

    """

    R = f.parent()
    K = R.base_ring()
    x = R.gen()
    n = f.degree()
    r = floor(n/p)
    a0 = f[0]
    assert a0.is_unit()

    h = R(1)
    f = f/a0
    g = f-1
    for k in range(1, r+1):
        h = h+(g[k]/p)*x**k
        g = f-h**p
    return h,g


def p_approximation_generic(f,p):
    r"""
    Return the generic `p`-approximation of ``f``.

    INPUT:

    - ``f`` -- a polynomial of degree `n` over a field `K`, with nonvanishing constant coefficient
    - ``p`` -- a prime number

    OUTPUT:

    Two polynomials `H`,`K` in `K(x)[t]` which are the `p`-approximation
    of the polynomial `F:=f(x+t)`, considered as polynomial in `t`.

    """

    R = f.parent()
    x = R.gen()
    K = R.fraction_field()
    S = PolynomialRing(K, 't')
    t = S.gen()
    F = f(x+t)
    H,G = p_approximation(F,p)
    # d =[R(G[k]*f^k) for k in [0..f.degree()]]
    return H,G
