r"""
Admissible reduction of curves
==============================

Let `K` be a field equipped with a discrete valuation `v_K`. For the time being,
we assume that `K` is a number field. Then `v_K` is the `\mathfrak{p}`-adic
valuation corresponding to a prime ideal `\mathfrak{p}` of `K`.

We consider a smooth projective  curve `Y` over `K`. Our goal is to compute the
semistable reduction of `Y` at `v_K` and to extract nontrivial arithmetic
information on `Y` from this.

In this module we realize a class ``AdmissibleModel``
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
#       Copyright (C) 2017-2018 Stefan Wewers <stefan.wewers@uni-ulm.de>
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
from mclf.semistable_reduction.semistable_model import SemistableModel


class AdmissibleModel(SemistableModel):
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



    EXAMPLES:



    """

    def __init__(self, Y, vK):

        K = vK.domain()
        assert Y.constant_base_field() == K, "K must be the constant base field of Y"
        self._original_model_of_curve = Y
        self._base_valuation = vK

        # we compute the branch locus and, if it is not contained in the
        # standard unit disk, we change the model of Y
        # actually, this should be done with a call Y.branch_locus()
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


   
