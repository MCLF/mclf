r"""
Semistable reduction of superelliptic curves of degree prime to `p`
===================================================================

Let `K` be a field of characteritic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`. For the time being, we
assume that `K` is a number field.

Let `n\ge 2` be an integer prime to `p` and `f\in K[x]` a polynomial over `K`
which is not an `n`-th power and whose radical has degree at least three.
We consider the smooth projective  curve `Y` over `K` defined generically by
the equation

.. MATH::

           Y: y^n = f(x).

Our goal is to compute the semistable reduction of `Y` at `v_K` and to extract
nontrivial arithmetic information on `Y` from this.

More precisely, ...


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

    We also fix a `p`-adic valuation `v_K` on `K` (i.e. a discrete valuation
    with residue characteristic `p`) and assume that `p` does not divide `n`.


AUTHORS:

- Stefan Wewers (2017-10-04): initial version


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

from sage.all import SageObject, PolynomialRing, FunctionField, GaussValuation, cached_method, Infinity, floor
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.affinoid_domain import *
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
from mclf.semistable_reduction.reduction_trees import ReductionTree



class Superell(SageObject):
    r"""
    Return the superelliptic curve of degree ``n`` defined by ``f``,
    relative to the `p`-adic valuation ``vK``.

    INPUT:

    - ``f`` -- a nonconstant poylnomial over a field `K`
    - ``vK`` -- a discrete valuation on `K`
    - ``n`` -- an integer `\geq 2`

    Here the residue characteristic of ``vK`` must be prime to the residue
    characteristic of ``vK`.
    Moreover, ``f`` must be of degree prime to ``n``.

    OUTPUT: the object representing the superelliptic curve

    .. MATH::

           Y: y^n = f(x).

    This object has various functionalities to compute the semistable reduction
    of `Y` relative to `v_K`, and some arithmetic invariants associated to it
    (for instance the "exponent of conductor" of `Y` with respect to `v_K`).
    The method used to compute the semistable reduction in this particular case is
    explained in detail in

    - [We17] I.I.Bouw and S. Wewers, Computing `L`-functions and semistable
      reduction of superelliptic, Glasgow Math. J., 59(1)


    EXAMPLES:


    .. NOTE::

        For the time being, we need to make the following additional assumptions
        on `f`:

        - `f` is of degree prime to `n`.

        This restrictions is preliminary and will be removed in a future version.
        Note that a superelliptic curve of degree `n` can be written in the required
        form if and only if the map `Y\to X` has a `K`-rational branch point.

    """

    def __init__(self, f, vK, n):

        R = f.parent()
        assert R.base_ring() is vK.domain(), "the domain of vK must be the base field of f"
        assert not vK.residue_field()(n).is_zero(), "the exponent n must be prime to the residue characteristic of vK"
        assert n.gcd(f.degree()) == 1, "the degree of f must be prime to n"
        self._n = n
        v0 = GaussValuation(R, vK)
        phi, psi, f1 = v0.monic_integral_model(f)
        # now f1 = phi(f).monic()
        if f1 != f.monic():
            print(("We make the coordinate change (x --> %s) in order to work with an integral polynomial f"%phi(R.gen())))
        self._f = f1
        a = phi(f).leading_coefficient()
        pi = vK.uniformizer()
        m = (vK(a)/n).floor()
        a = pi**(-n*m)*a
        self._a = a
        self._vK = vK
        FX = FunctionField(vK.domain(), names=R.variable_names())  # this does not work in Sage 8.0
        S = PolynomialRing(FX, 'T')
        T = S.gen()
        FY = FX.extension(T**n-FX(a*f1), 'y')
        self._FX = FX
        self._FY = FY
        X = BerkovichLine(FX, vK)
        self._X = X
        Y = SmoothProjectiveCurve(FY)
        self._Y = Y


    def __repr__(self):
        return "superelliptic curve Y: y^%s = %s over %s, with respect to %s"%(self._n,
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


    def reduction_tree(self):
        r"""
        Return the reduction tree which determines the semistabel model.

        """
        if hasattr(self, "_reduction_tree"):
            return self._reduction_tree

        X = self._X
        FX = self._FX
        Y = self.curve()
        vK = self.base_valuation()
        f = self._f
        T = BerkovichTree(X)
        T = T.adapt_to_function(FX(f))
        T = T.permanent_completion()
        reduction_tree = ReductionTree(Y, vK, T)

        self._reduction_tree = reduction_tree
        return reduction_tree


    def compute_semistable_reduction(self):
        r"""
        Compute the semistable reduction of this curve, and report on the
        computation and the result.

        """
        print("We try to compute the semistable reduction of the")
        print(self)
        print(("which has genus ", self.curve().genus()))
        print()

        reduction_tree = self.reduction_tree()
        inertial_components = reduction_tree.inertial_components()
        assert inertial_components != [], "no inertial components found! Something is wrong.."
        if len(inertial_components) > 1:
            print(("There are %s inertial components to consider: "%len(inertial_components)))
        else:
            print("There is exactly one inertial component to consider:")
        print()
        for Z in inertial_components:
            print("Inertial component corresponding to ")
            print(Z.interior())
            print("It splits over ", Z.splitting_field().extension_field())
            print("into %s lower components."%len(Z.lower_components()))
            print("The upper components are: ")
            for W in Z.upper_components():
                print(W)
                if W.field_of_constants_degree() > 1:
                    print("   (note that this component is defined over an extension of degree %s over the residue field)"%W.field_of_constants_degree())
            print("Contribution of this component to the reduction genus is ", Z.reduction_genus())
            print()
        print()
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
