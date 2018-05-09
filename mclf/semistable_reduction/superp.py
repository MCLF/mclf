r"""
Semistable reduction of superelliptic curves of degree `p`
==========================================================

Let `K` be a field of characteritic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`. For the time being, we
assume that `K` is a number field.

Let `f\in K[x]` be a polynomial over `K` which is not a `p`-th power and whose
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

from sage.all import SageObject, PolynomialRing, FunctionField, cached_method, Infinity, floor
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.affinoid_domain import *
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
from mclf.semistable_reduction.reduction_trees import ReductionTree



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

    - [We17] S. Wewers, *Semistable reduction of superelliptic curves of degree p*, \
      preprint, 2017.

    INPUT:

    - ``f`` -- a nonconstant poylnomial over a field `K`
    - ``vK`` -- a discrete valuation on `K`
    - ``p`` -- a prime number

    Here the residue characteristic of ``vK`` must be equal to the prime ``p``.
    Moreover, ``f`` must be of degree prime to ``p``.

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

    .. NOTE::

        For the time being, we need to make the following additional assumptions
        on `f`:

        - of degree prime to `p`.

        This restrictions is preliminary and will be removed in a future version.
        Note that a superelliptic curve of degree `p` can be written in the required
        form if and only if the map `Y\to X` has a `K`-rational branch point.

    """

    def __init__(self, f, vK, p):

        R = f.parent()
        assert R.base_ring() is vK.domain(), "the domain of vK must be the base field of f"
        assert p == vK.residue_field().characteristic(), "the exponent p must be the residue characteristic of vK"
        assert not p.divides(f.degree()), "the degree of f must be prime to p"
        self._p = p
        v0 = GaussValuation(R, vK)
        phi, psi, f1 = v0.monic_integral_model(f)
        # now f1 = phi(f).monic()
        if f1 != f.monic():
            print("We make the coordinate change (x --> %s) in order to work with an integral polynomial f"%phi(R.gen()))
        self._f = f1
        a = phi(f).leading_coefficient()
        pi = vK.uniformizer()
        m = (vK(a)/p).floor()
        a = pi**(-p*m)*a
        self._a = a
        self._vK = vK
        FX = FunctionField(vK.domain(), names=R.variable_names())  # this does not work in Sage 8.0
        S = PolynomialRing(FX, 'T')
        T = S.gen()
        FY = FX.extension(T**p-FX(a*f1), 'y')
        self._FX = FX
        self._FY = FY
        X = BerkovichLine(FX, vK)
        self._X = X
        Y = SmoothProjectiveCurve(FY)
        self._Y = Y


    def __repr__(self):
        return "superelliptic curve Y: y^%s = %s over %s, with respect to %s"%(self._p,
                        self._a*self._f, self._vK.domain(), self._vK)


    def curve(self):
        """
        Return the curve.

        """
        return self._Y


    def base_valuation(self):
        """
        Return the valuation on the base field.

        """
        return self._vK


    def etale_locus(self):
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

        - [We17]: *Semistable reduction of superelliptic curves of degree p*, \
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
        `y^2 = f(x) = 2x^3 + x^2 + 32`, and `f` is not monic, as required.
        To fix this, we substitute `x/2` and multiply with `4`. Then the
        new equation is `y^2 = x^3 + x^2 + 128`: ::

            sage: f = x^3 + x^2 + 128
            sage: Y = Superp(f, vK, 2)
            sage: Y.compute_etale_locus()
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(1/x) >= -5/2
            v(x) >= 2

    .. NOTE::

        At the moment, the construction of the superelliptic curve `Y` requires that
        the polynomial `f` defining `Y` is monic, integral with respect to `v_K`
        and of degree prime to `p`. The motivation for this restriction, and its
        result is that the etale locus is contained in the closed unit disk.

        """

        if hasattr(self, "_etale_locus"):
            return self._etale_locus

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
            # the following exception if necessary because calling
            # RationalDomainOnBerkovichLine(X, f) with f constant
            # result in an error
            k = delta[i].parent().constant_base_field()
            if delta[i] in k:
                # if delta[i] is constant, it must not be integral
                # otherwise we add the whole Berkovich line which is
                # not an affinoid
                assert self._vK(delta[i]) < 0, "this is not an affinoid"
                # if vK(delta[i]) >= 0 then we add the empty set, i.e
                # we do nothing
            else:
                X_et = X_et.union(RationalDomainOnBerkovichLine(X, delta[i]))
                X_et.simplify()
        X_et = X_et.intersection(ClosedUnitDisk(X))
        X_et = X_et.minimal_representation()
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
        for xi in X_et._T.vertices():
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
            print("There are %s inertial components to consider: "%len(inertial_components))
        else:
            print("There is exactly one inertial component to consider:")
        print()
        for Z in inertial_components:
            print("inertial component corresponding to ")
            print(Z.interior())
            print("It splits over ", Z.splitting_field().extension_field())
            print("into %s lower components."%len(Z.lower_components()))
            print("The upper components are: ")
            for W in Z.upper_components():
                print(W)
                if W.field_of_constants_degree() > 1:
                    print("   (note that this component is defined over an extension of degree %s over the residue field)"%W.field_of_constants_degree())
            print("Contribution of this component to the reduction genus is ", Z.reduction_genus())
            print
        print
        if reduction_tree.is_semistable():
            print("We have computed the semistable reduction of the curve.")
        else:
            print("We failed to compute the semistable reduction of the curve.")
            raise ValueError()

    def conductor_exponent(self):
        r"""
        Return the conductor exponent at p of this superelliptic curve.

        """
        return self.reduction_tree().reduction_conductor()





#-----------------------------------------------------------------------




def p_approximation(f,p):
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

    Two polynomials `H` and `G` in `K(x)[t]` which are the `p`-approximation
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
