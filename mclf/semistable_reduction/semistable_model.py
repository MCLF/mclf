r"""
Semistable reduction of a smooth projective curve over a local field
====================================================================

Let `K` be a field and `v_K` a discrete valuation on `K`. We let `\mathcal{O}_K`
denote the valuation ring of `v_K` and `\mathbb{F}_K` the residue field.

We consider a smooth projective  curve `Y` over `K`. Our goal is to compute the
*semistable reduction* of `Y` at `v_K` and to extract nontrivial arithmetic
information on `Y` from this.

Let us define what we mean by 'semistable reduction' and by 'computing'.
By the famous result of Deligne and Mumford there exists a finite, separable
field extension `L/K`,  an extension `v_L` of `v_K` to `L` (whose valuation ring
we call `\OO_L`) and an `\OO_L`-model `\mathcal{Y}` of `Y_L` whose special fiber
`\bar{Y}:=\mathcal{Y}_s` is reduced and has at most ordinary double points as
singularities. We call `\mathcal{Y}` a semistabel model and `\bar{Y}` a semistable
reduction of `Y`.

Let us assume, for simplicity, that `K` is complete with respect to `v_K`. Then
the extension `v_L` to `L` is unique and `L` is complete with respect to `v_L`.
Then we we may moreover assume that `L/K` is a Galois extension and that the
tautological action of the Galois group of `L/K` extends to the
semistable model `\mathcal{Y}`. By restriction we obtain an action of `{\rm Gal}(L/K)`
on `\bar{Y}`. (In practise we mostly work with fields `K` which are not complete.
To make sense of the above definitions, one simply has to replace `K` by its completion.)

When we say *the semistable reduction* of `Y` we actually mean  the extension
`L/K`, the `\mathbb{F}_L`-curve `\bar{Y}` and the action of the former
on the latter.

Note that neither `L/K` nor `\bar{Y}` are unique, but their nonuniqueness is in
a sense inessential. For instance, one may replace `L` by a larger Galois
extension `L'/K`; as a consequence the curve `\bar{Y}` gets replaced by its
base extension to the residue field of `L'`. Also, certain blowups of the semistable
model `\mathcal{Y}` may result in a new semistable model `\mathcal{Y}` with special
fiber `\bar{Y}'`. The only difference between `\bar{Y}` and `\bar{Y}'` are some
new irreducible components, which are 'contractible', i.e. they are smooth of
genus `0` and meet the rest of `\bar{Y}'` in at most two points.


At the moment, we do not have an effective method at our disposal to compute the
semistable reduction of an arbitrary curve `Y`, but only a set of methods which
can be applied for certain classes of curves. We always assume that the
curve `Y` is given as a finite separable cover

.. MATH::

      \phi: Y \to X,

where `X=\mathbb{P}^1_K` is the projective line over `K`. There are two main
cases that we can handle:
- the order of the monodromy group of `\phi` (i.e. the Galois group of its
  Galois closure) is prime to the residue characteristic of the valuation `v_K`.
- `\phi` is a Kummer cover of degree `p`, where `p` is the (positive) residue
  characteristic of `v_K`
In the first case, the method of *admissible reduction* is available. In the
second case, the results of

    - [We17] S. Wewers, *Semistable reduction of superelliptic curves of degree p*, \
      preprint, 2017.

tell us what to do. In both cases, there exists a normal `\mathcal{O}_K`-model
`\mathcal{X}_0` of `X=\mathbb{P}^1_K` (the *inertial model*) whose normalization
in the function field of `Y_L` is a semistable model, for a sufficiently large
finite extension `L/K`. Once the right inertial model is defined, the method for
computing the semistable model `\mathcal{Y}` and its special fiber `\bar{Y}` are
independent of the particular case (these computations are done within the Sage
class ``ReductionTree``).

In this module we define a base class ``SemistableModel``. An object in this class
is initialized by a pair `(Y,v_K)` , where `Y` is a smooth projective curve over
a field `K` and `v_K`  is a discrete valuation on `K`. The class provides access
to functions which compute and extract information from the semistable reduction
of `Y` with respect to `v_K`.



.. NOTE::

    For the time being, we have to assume that `K` is a number field.
    Then `v_K` is the valuation associated to a prime ideal of `K` (i.e. a maximal
    ideal of its ring of integers).


AUTHORS:

- Stefan Wewers (2018-5-16): initial version


EXAMPLES:

We compute the stable reduction and the conductor exponent of the Picard curve

.. MATH::

    Y:\; y^3 = x^4 - 1.

at the primes `p=2,3`:  ::

    sage: from mclf import *
    sage: v_2 = QQ.valuation(2)
    sage: R.<x> = QQ[]
    sage: Y = SuperellipticCurve(x^4-1, 3)
    sage: Y
    superelliptic curve y^3 = x^4 - 1 over Rational Field
    sage: Y2 = SemistableModel(Y, v_2)
    sage: Y2.is_semistable()
    True

The stable reduction of `Y` at `p=2` has four components, one of genus `0` and
three of genus `1`. ::

    sage: [Z.genus() for Z in Y2.components()]
    [0, 1, 1, 1]
    sage: Y2.components_of_positive_genus()
    [the smooth projective curve with Function field in y defined by y^3 + x^4 + x^2,
     the smooth projective curve with Function field in y defined by y^3 + x^2 + x,
     the smooth projective curve with Function field in y defined by y^3 + x^2 + x + 1]
    sage: Y2.conductor_exponent()
    6
    sage: v_3 = QQ.valuation(3)
    sage: Y3 = SemistableModel(Y, v_3)
    sage: Y3.is_semistable()
    True
    sage: Y3.components_of_positive_genus()
    [the smooth projective curve with Function field in y defined by y^3 + y + 2*x^4]
    sage: Y3.conductor_exponent()
    6

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
from mclf.curves.superelliptic_curves import SuperellipticCurve


class SemistableModel(SageObject):
    r"""
    This is a base class for various classes of curves and methods for
    computing the semistable reduction. Objects of this class are determined by
    a smooth projective curve `Y` over a field `K` and a discrete valuation
    `v_K` on `K`.

    INPUT:

    - ``Y`` -- a smooth projective curve
    - ``vK`` -- a discrete valuation on the base field `K` of `Y`

    Instantiation of this class actually creates an instant of a suitable subclass,
    which represent the kind of curve for which an algorithm for computing the
    semistable reduction has been implemented.


    EXAMPLES::

        sage: from mclf import *
        sage: v_5 = QQ.valuation(5)
        sage: FX.<x> = FunctionField(QQ)
        sage: R.<y> = FX[]
        sage: FY.<y> = FX.extension(y^3 - y^2 + x^4 + x + 1)
        sage: Y = SmoothProjectiveCurve(FY)
        sage: YY = SemistableModel(Y, v_5)

    The degree of `Y` as a cover of the projective line is `4`, which is prime
    to `p=5`. Hence `Y` has admissible reduction and we have created an instance
    of the class ``AdmissibleModel``. ::

        sage: isinstance(YY, AdmissibleModel)
        True

    Actually, `Y` has good reduction at `p=5`. ::

        sage: YY.is_semistable()
        True
        sage: YY.components_of_positive_genus()
        [the smooth projective curve with Function field in y defined by y^3 + 4*y^2 + x^4 + x + 1]

    """
    def __init__(self, Y, vK):

        from mclf.semistable_reduction.admissible_reduction import AdmissibleModel
        from mclf.semistable_reduction.superp_models import SuperpModel

        p = vK.residue_field().characteristic()
        if isinstance(Y, SuperellipticCurve) and Y.covering_degree() == p:
            # we create an instance of ``SuperpModel``
            self.__class__ = SuperpModel
            SuperpModel.__init__(self, Y, vK)
        elif p==0 or p.gcd(Y.covering_degree()) == 1:
            # we create an instance of ``AdmissibleModel``
            self.__class__ = AdmissibleModel
            AdmissibleModel.__init__(self, Y, vK)
        else:
            raise NotImplementedError


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


    def compute_semistable_reduction(self, verbosity=1):
        """
        Compute the semistable reduction of this curve (and report on the
        ongoing computation).

        INPUT:

        -- ``verbosity`` - a nonnegative integer (default: 1)

        OUTPUT:

        Calling this function initiates the creation of a ``ReductionTree``
        which essentially encodes a semistable model of the curve. Depending
        on the verbosity level, messages will be printed which report on the
        ongoing computation. If ``verbosity`` is set to `0`, no message will
        be printed.

        This method must be implemented by the subclasses of SemistableModel
        (which are characterized by a particular method for computing a
        semistable model). At the moment, these subclasses are
        - ``AdmissibleModel``
        - ``Superell``
        - ``Superp``

        """
        raise NotImplementedError


    def is_semistable(self):
        """
        Check whether the model is really (potentially) semistable.

        """
        return self.reduction_tree().is_semistable()


    def semistable_reduction(self):
        r"""
        Return the special fiber of this semistable model.

        Note:  not yet implemented

        """
        raise NotImplementedError


    def stable_reduction(self):
        r"""
        Return the special fiber of the stable model of this curve.

        The stable model is obtained from this semistable model by contracting
        all 'unstable' components.

        Note:  not yet implemented

        """
        raise NotImplementedError


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


    def conductor_exponent(self):
        r"""
        Return the conductor exponent at p of this curve.

        """
        return self.reduction_tree().reduction_conductor()
