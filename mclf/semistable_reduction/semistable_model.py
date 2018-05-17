r"""
Semistable reduction of a smooth projective curve over a local field
====================================================================

Let `K` be a field of characteristic zero and `v_K` a discrete valuation on `K`
whose residue field is finite of characteristic `p>0`. For the time being, we
assume that `K` is a number field.

We consider a smooth projective  curve `Y` over `K`. Our goal is to compute the
semistable reduction of `Y` at `v_K` and to extract nontrivial arithmetic
information on `Y` from this.


AUTHORS:

- Stefan Wewers (2018-5-16): initial version


EXAMPLES::

<Lots and lots of examples>



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

from sage.all import SageObject, PolynomialRing, FunctionField, GaussValuation, cached_method, Infinity, floor
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.affinoid_domain import *
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
from mclf.semistable_reduction.reduction_trees import ReductionTree




class SemistableModel(SageObject):
    r"""
    Return class for computing the semistable reduction of a curve with respect
    to a discrete valuation of the ground field.

    This is a base class for various classes of curves and methods for
    computing the semistable reduction. It may also be considered as a wrapper
    for the class ``ReductionTree``.

    INPUT:

    - ``Y`` -- a smooth projective curve
    - ``vK`` -- a discrete valuation on the base field `K` of `Y`


    EXAMPLES:




    """

    def curve(self):
        """
        Return the curve.

        """
        return self._Y


    def base_field(self):
        """
        Return the base field of this curve.

        """
        self._Y.base_field()


    def base_valuation(self):
        """
        Return the valuation on the base field of the curve.

        """
        return self._vK


    def reduction_tree(self):
        """
        Return the reduction tree underlying this semistable model.

        """
        return self._reduction_tree


    def compute_semistable_reduction(self):
        """
        Compute the semistable reduction of this curve (and report on the
        ongoing computation)

        This method should be superseded by the child classes of SemistableModel.

        """
        raise NotImplementedError


    def conductor_exponent(self):
        r"""
        Return the conductor exponent at p of this curve.

        """
        return self.reduction_tree().reduction_conductor()


    def is_semistable(self):
        """
        Check whether the model is really (potentially) semistable.

        """
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
