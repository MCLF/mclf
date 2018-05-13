r"""
Admissible reduction of curves
==============================

Let `K` be a field equipped with a discrete valuation `v_K`. For the time being,
we assume that `K` is a number field. Then `v_K` is the `\mathfrak{p}`-adic
valuation corresponding to a prime ideal `\mathfrak{p}` of `K`.

We consider a smooth projective  curve `Y` over `K`. Our goal is to compute the
semistable reduction of `Y` at `v_K` and to extract nontrivial arithmetic
information on `Y` from this.

In this module we realize a class ``AdmissibleReductionOfSmoothProjectiveCurve``
which computes the semistable reduction of a given curve `Y` at `v_K` provided
that it has *admissible reduction* at `v_K`. This is always the case if the
residue characteristic of `v_K` is zero or strictly larger than the degree
of `Y` (as a cover of the projective line).



AUTHORS:

- Stefan Wewers (2018-7-03): initial version


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

class AdmissibleReductionOfSmoothProjectiveCurve(SageObject):
    r"""
    A class representing a curve `Y` over a field `K` with a discrete valuation
    `v_K`. Assuming that `Y` has (potentially) admissible reduction at `v_K`,
    we are able to compute the semistable reduction of `Y` at `v_K`.

    INPUT:

    - ``Y`` -- a smooth projective curve over a field `K`
    - ``vK`` -- a discrete valuation on `K`

    OUTPUT: the object representing the curve `Y` and the valuation `v_K`.
    This object has various functionalities to compute the semistable reduction
    of `Y` relative to `v_K`, and some arithmetic invariants associated to it
    (for instance the "exponent of conductor" of `Y` with respect to `v_K`).
    The method used to compute the semistable reduction in this particular case is
    explained in detail in

    - [We17] I.I.Bouw and S. Wewers, Computing `L`-functions and semistable
      reduction of superelliptic, Glasgow Math. J., 59(1)


    EXAMPLES:



    """

    def __init__(self, Y, vK):

        K = vK.domain()
        assert Y.constant_base_field() == K, "K must be the constant base field of Y"
        self._original_model_of_curve = Y
        self._base_valuation = vK

        # we compute the ramification locus and, if it is not contained in the
        # standard unit disk, we change the model of Y
        FY = Y.function_field()
        FX = Y.rational_function_field()
        F = FY.polynomial()
        assert F.base_ring() == FX
        X = BerkovichLine(FX, vK)
        Delta = F.discriminant()

        self._curve = Y
        self._berkovich_line = X

        T = BerkovichTree(X)
        T = T.adapt_to_function(Delta)
        T = T.permanent_completion()
        reduction_tree = ReductionTree(Y, vK, T)

        self._reduction_tree = reduction_tree


    def original_model_of_curve(self):
        """ Return the original model of the curves. """
        return self._original_model_of_curve


    def curve(self):
        """ Return the curve. """
        return self._curve


    def reduction_tree(self):
        """ Return the reduction tree. """
        return self._reduction_tree


    def is_semistable(self):
        """ Check whether the reduction is semistable. """
        return self.reduction_tree().is_semistable()


    def components(self):
        r"""
        Return the list of all components of the admissible reduction of the curve.
        """

        components = []
        for Z in self.reduction_tree().inertial_components():
            components += [W.curve() for W in Z.upper_components()]
        return components


    def components_of_positive_genus(self):
        r"""
        Return the list of all components of of the admissible reduction of the
        curve which have positive genus.
        """

        return [W for W in self.components() if W.genus() > 0]
