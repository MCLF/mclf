# -*- coding: utf-8 -*-
r"""
Semistable models of superelliptic curves of degree `p`
=======================================================

Let `K` be a field of characteritic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`.

Let `f\in K[x]` be a polynomial over `K` which is not a `p`-th power and whose
radical has degree at least three. We consider the smooth projective  curve
`Y` over `K` defined generically by the equation

.. MATH::

           Y: y^p = f(x).

So `Y` is a *superelliptic curve* of degree `p`.

In this module we define a class ``SuperpModel`` which represents a semistable
model of a superelliptic curve `Y` of degree `p`, with respect to a `p`-adic
valuation on the base field `K` of `Y`.

The method to define and compute a semistable model in this particular case is
taken from

- [We17] S. Wewers, *Semistable reduction of superelliptic curves of degree p*, \
  preprint, 2017.

The key notion is the **etale locus**.

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
on the semistable reduction. The main result of [We17]
gives an explicit description of the affinoid `X^{et}` as a union
of rational domains defined by rational functions which can be
easily computed in terms of the polynomial `f` defining `Y`.

Once the etale locus `X^{et}` is computed, we can define an *inertial model*
`\mathcal{X}_0` of `X`. A semistable model `\mathcal{Y}` of `Y` can then be
obtained as the normalization of `\mathcal{X}_0` inside `Y_L`, for a sufficiently
large finite extension `L/K`.

The class ``SuperpModel`` is a subclass of the class ``SemistableModel`` and can
be instantiated via its parent. All methods to extract information about the
semistable reduction of `Y` are simply inherited from ``SemistableModel``. The
subclass itself only defines the methods to compute the etale locus and to create
the corresponding inertail model.


AUTHORS:

- Stefan Wewers (2017-07-29): initial version


EXAMPLES::

    sage: from mclf import *
    sage: R.<x> = QQ[]
    sage: f = x^4 + x^2 + 1
    sage: Y = SuperellipticCurve(f, 3)
    sage: Y
    superelliptic curve y^3 = x^4 + x^2 + 1 over Rational Field
    sage: v_3 = QQ.valuation(3)
    sage: YY = SuperpModel(Y, v_3)
    sage: YY
    semistable model of superelliptic curve Y: y^3 = x^4 + x^2 + 1 over Rational Field, with respect to 3-adic valuation
    sage: YY.etale_locus()
    Affinoid with 3 components:
    Elementary affinoid defined by
    v(x) >= 3/4
    Elementary affinoid defined by
    v(x - 2) >= 5/4
    Elementary affinoid defined by
    v(x + 2) >= 5/4

    sage: YY.is_semistable()
    True
    sage: YY.components()
    [the smooth projective curve with Function field in u1 defined by u1^3 + 2*x^4 + 2*x^2 + 2,
     the smooth projective curve with Function field in u2 defined by u2^3 + u2 + 2*x^2,
     the smooth projective curve with Function field in u2 defined by u2^3 + u2 + 2*x^2,
     the smooth projective curve with Function field in u2 defined by u2^3 + u2 + 2*x^2]
    sage: YY.conductor_exponent()
    12

We check that issues #39 and #40 have been fixed: ::

    sage: v_2 = QQ.valuation(2)
    sage: f =  x^5 - 5*x^4 + 3*x^3 - 3*x^2 + 4*x - 1
    sage: Y = SuperellipticCurve(f, 2)
    sage: Y2 = SemistableModel(Y, v_2)
    sage: Y2.etale_locus()
    Affinoid with 2 components:
    Elementary affinoid defined by
    v(x + 1) >= 2/3
    Elementary affinoid defined by
    v(x^4 +  4*x + 4) >= 8/3
    sage: Y2.is_semistable()
    True


TO DO:

- more doctests


"""

# *****************************************************************************
#       Copyright (C) 2017-2018 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************

from sage.all import PolynomialRing, FunctionField, floor, GaussValuation
from mclf.berkovich.berkovich_line import BerkovichLine
from mclf.berkovich.berkovich_trees import BerkovichTree
# from mclf.berkovich.affinoid_domain import ClosedUnitDisk
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
from mclf.curves.superelliptic_curves import SuperellipticCurve
from mclf.semistable_reduction.reduction_trees import ReductionTree
from mclf.semistable_reduction.semistable_models import SemistableModel


class SuperpModel(SemistableModel):
    r"""
    Return a semistable model of a superelliptic curve of degree `p`.

    INPUT:

    - ``Y`` -- a superelliptic curve over a field `K`
    - ``vK`` -- a discrete valuation on `K`

    The field `K` must be of characteristic `0` and the residue characteristic
    of ``vK`` must be a prime `p` which is equal to the covering degree of `Y`.

    OUTPUT: the object representing a semistable model of `Y`.


    .. NOTE::

        For the time being, we need to make the following additional assumptions
        on the curve `Y`:

        - the polynomial `f` which is part of the defining equation
          `y^p = f(x)` is of degree prime to `p`.

        This restrictions is preliminary and will be removed in a future version.
        Note that a superelliptic curve of degree `p` can be written in the required
        form if and only if the map `Y\to X` has a `K`-rational branch point.


    EXAMPLES:


    """

    def __init__(self, Y, vK):

        p = vK.residue_field().characteristic()
        assert p == Y.covering_degree()
        assert isinstance(Y, SuperellipticCurve)
        f = Y.polynomial()
        R = f.parent()
        assert R.base_ring() is vK.domain(), "the domain of vK must be the base field of f"
        assert p == vK.residue_field().characteristic(), "the exponent p must be the residue characteristic of vK"
        assert not p.divides(f.degree()), "the degree of f must be prime to p"
        self._p = p
        self._base_valuation = vK
        v0 = GaussValuation(R, vK)
        phi, psi, f1 = v0.monic_integral_model(f)
        # now f1 = phi(f).monic()
        if f1 != f.monic():
            print("We make the coordinate change (x --> {}) in order to work\
                with an integral polynomial f".format(phi(R.gen())))
            self._f = f1
            a = phi(f).leading_coefficient()
            pi = vK.uniformizer()
            m = (vK(a)/p).floor()
            a = pi**(-p*m)*a
            self._a = a
            FX = FunctionField(vK.domain(), R.variable_name())
            S = PolynomialRing(FX, 'T')
            T = S.gen()
            FY = FX.extension(T**p-FX(a*f1), 'y')
            self._FX = FX
            self._FY = FY
            Y = SmoothProjectiveCurve(FY)
            self._curve = Y
        else:
            self._f = f.monic()
            self._a = vK.domain().one()
            self._FY = Y.function_field()
            self._FX = Y.rational_function_field()
            self._curve = Y
        X = BerkovichLine(self._FX, vK)
        self._X = X

    def __repr__(self):
        return "semistable model of superelliptic curve Y: y^{} = {} over {},\
            with respect to {}".format(self._p, self._a*self._f,
                                       self.base_valuation().domain(),
                                       self.base_valuation())

    def etale_locus(self):
        r"""
        Return the etale locus of the cover `Y\to X`.

        OUTPUT: the etal locus, an affinoid subdomain of the Berkovich line
        `X` (the analytic space associated to the projektive line over the
        completion of the base field `K` with respect to the valuation `v_K`).

        EXAMPLES:

        ::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: R.<x> = QQ[]
            sage: f = x^3 + x^2 + 1
            sage: Y = SuperellipticCurve(f, 2)
            sage: Y
            superelliptic curve y^2 = x^3 + x^2 + 1 over Rational Field
            sage: YY = SuperpModel(Y, v_2)
            sage: YY.etale_locus()
            Elementary affinoid defined by
            v(x^4 + 4*x + 4) >= 8/3

        We check Example 4.14 from [BouWe16]. The original equation is
        `y^2 = f(x) = 2x^3 + x^2 + 32`, and `f` is not monic, as required.
        To fix this, we substitute `x/2` and multiply with `4`. Then the
        new equation is `y^2 = x^3 + x^2 + 128`: ::

            sage: f = x^3 + x^2 + 128
            sage: Y = SuperellipticCurve(f, 2)
            sage: YY = SuperpModel(Y, v_2)
            sage: YY.etale_locus()
            Elementary affinoid defined by
            v(x) >= 2
            v(1/x) >= -5/2
            <BLANKLINE>

    .. NOTE::

        At the moment, the construction of the superelliptic curve `Y` requires that
        the polynomial `f` defining `Y` is monic, integral with respect to `v_K`
        and of degree prime to `p`. The motivation for this restriction, and its
        result is that the etale locus is contained in the closed unit disk.

        """
        from mclf.berkovich.piecewise_affine_functions import Discoid, valuative_function
        from mclf.berkovich.affinoid_domain import UnionOfDomains

        if hasattr(self, "_etale_locus"):
            return self._etale_locus

        X = self._X
        v_K = X.base_valuation()
        FX = self._FX
        f = self._f
        p = self._p
        n = f.degree()
        m = floor(n/p)
        H, G = p_approximation_generic(f, p)
        # b = [FX(H[i]) for i in range(n+1)]
        c = [FX(G[k]) for k in range(n+1)]
        pl = 1
        while pl <= m:
            pl = pl*p

        a = [f]
        for i in range(1, n+1):
            a.append(a[i-1].derivative()/i)
        a = [a[i]/f for i in range(n+1)]

        pi = self.base_valuation().uniformizer()
        D = Discoid(X.gauss_point())    # this is the closed unit disk
        delta = [valuative_function(D, ([(c[pl], p - 1)], -p*v_K(pi)))]
        delta += [valuative_function(
            D, ([(c[pl], i*(p - 1)), (a[i], -pl*(p - 1))],
                -i*p*v_K(pi))) for i in range(1, n + 1)]
        delta += [
            valuative_function(
                D, ([(c[pl], k*(p - 1)), (c[k], -pl*(p - 1))], -p*(k - pl)*v_K(pi)))
            for k in range(m + 1, n + 1) if k != pl]
        U_list = [delta[i].affinoid_domain() for i in range(len(delta))]
        X_et = UnionOfDomains(U_list)
        self._etale_locus = X_et
        return X_et

    def reduction_tree(self):
        r"""
        Return the reduction tree which determines the semistabel model.

        """
        if hasattr(self, "_reduction_tree"):
            return self._reduction_tree

        Y = self.curve()
        vK = self.base_valuation()
        X_et = self.etale_locus()
        T = BerkovichTree(self._X)
        for xi in X_et.tree().vertices():
            T, _ = T.add_point(xi)
        # this is the affinoid tree underlying the etale locus
        # the inertial components are the boundary points
        # we have to replace it by its permanent completion:
        T.permanent_completion()
        reduction_tree = ReductionTree(Y, vK, T, X_et.boundary())
        # for xi in X_et.boundary():
        #     reduction_tree.add_inertial_component(xi)

        self._reduction_tree = reduction_tree
        return reduction_tree

    def compute_semistable_reduction(self):
        r"""
        Compute the semistable reduction of this curve, and report on the
        computation and the result.

        """
        print("We try to compute the semistable reduction of the")
        print(self)
        print("which has genus ", self.curve().genus())
        print()
        print("First we compute the etale locus: ")
        print(self.etale_locus())

        reduction_tree = self.reduction_tree()
        inertial_components = reduction_tree.inertial_components()
        assert inertial_components != [], "no inertial components found! Something is wrong.."
        if len(inertial_components) > 1:
            print("There are {} inertial components to consider: ".format(
                len(inertial_components)))
        else:
            print("There is exactly one inertial component to consider:")
        print()
        for Z in inertial_components:
            print("inertial component corresponding to ")
            print(Z.interior())
            print("It splits over ", Z.splitting_field().extension_field())
            print("into {} lower components.".format(len(Z.lower_components())))
            print("The upper components are: ")
            for W in Z.upper_components():
                print(W)
                if W.field_of_constants_degree() > 1:
                    print("   (note that this component is defined over an\
                        extension of degree {} over the residue field)".format(
                        W.field_of_constants_degree()))
            print("Contribution of this component to the reduction genus is ", Z.reduction_genus())
            print
        print
        if reduction_tree.is_semistable():
            print("We have computed the semistable reduction of the curve.")
        else:
            print("We failed to compute the semistable reduction of the curve.")
            raise ValueError()


"""
auxiliary functions
-------------------
"""


def p_approximation(f, p):
    r"""
    Return the `p`-approximation of ``f``.

    INPUT:

    - ``f`` -- a polynomial of degree `n` over a field `K`, with nonvanishing
               constant coefficient
    - ``p`` -- a prime number

    OUTPUT:

    Two polynomials `h` and `g` in `K[x]`, such that

    - `f=a_0(h^p+g)`, where `a_0` is the constant coefficient of `f`
    - `r:=deg(h)\leq n/p`, and
    - `x^{(r+1)}` divides `g`

    Note that `h, g` are uniquely determined by these conditions.

    """

    R = f.parent()
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
    return h, g


def p_approximation_generic(f, p):
    r"""
    Return the generic `p`-approximation of ``f``.

    INPUT:

    - ``f`` -- a polynomial of degree `n` over a field `K`, with nonvanishing constant coefficient
    - ``p`` -- a prime number

    OUTPUT:

    Two polynomials `H` and `G` in `K(x)[t]` which are the `p`-approximation
    of the polynomial `F:=f(x+t)`, considered as polynomial in `t`.

    """

    R = f.parent()
    x = R.gen()
    K = R.fraction_field()
    S = PolynomialRing(K, 't')
    t = S.gen()
    F = f(x+t)
    H, G = p_approximation(F, p)
    # d =[R(G[k]*f^k) for k in [0..f.degree()]]
    return H, G
