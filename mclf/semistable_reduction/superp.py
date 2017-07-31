r"""
Semistable reduction of superelliptic curves of degree `p`


Let `K` be a field of characteritic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`. In practise, `K` will 
either be a number field or a `p`-adic number field. 

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
from mclf.berkovich.berkovich_line import BerkovichLine
from mclf.berkovich.affinoid_domain import AffinoidDomainOnBerkovichLine,\
           RationalDomainOnBerkovichLine




class Superp(SageObject):

    def __init__(self, f, vK, p):

        R = f.parent()
        assert R.base_ring() is vK.domain()
        assert p == vK.residue_field().characteristic()
        self._base_ring = R
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

        # print delta

        X_et = RationalDomainOnBerkovichLine(X, delta[0])
        X_et.simplify()
        for i in range(1,len(delta)):
            X_et = X_et.union(RationalDomainOnBerkovichLine(X, delta[i]))
            X_et.simplify()
        return X_et



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





