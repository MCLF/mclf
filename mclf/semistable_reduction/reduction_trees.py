r"""
Reduction trees: a data structure for reduction of covers of the projective line.
=================================================================================

Let `K` be a field with a discrete valuation `v_K`. We let `X:=\mathbb{P}^1_K`
denote the projective line over `K`. We are also given a finite cover

.. MATH::

      \phi: Y \to X,

where `Y` is a smooth projective and absolutely irreducible curve. We assume that
`Y` has positive genus.

A **reduction** of the cover `\phi` over `v_K` is given by the
following data:

- a finite extension `L/K`,
- an extension `v_L` of `v_K` to `L`,
- semistable models `\mathcal{X},\mathcal{Y}` of `X_L, Y_L` (with respect to `v_L`),
- a finite morphism `\Phi_L: \mathcal{Y} \to \mathcal{X}` extending `\phi`.

  Restriction of `\Phi_L` to the special fibers yields a finite
  morphism

.. MATH::

    \bar{\phi}: \bar{Y} \to \bar{X}

between (not necessarily smooth) curves over the residue field of `L`. This map
is often called the *reduction* of the cover `\phi`, by abuse of
terminology.

A reduction `\Phi_L` is called **Galois** if

- the extension `L/K` is Galois (with Galois group `G`), and
- the natural action of the decomposition group `G_{v_L}\subset G` of `v_L`
  on `Y_L` extends to the model `\mathcal{Y}`.

If this is the case, then we can form the quotient schemes
`\mathcal{X}_0:=\mathcal{X}/G_{v_L}` and `\mathcal{Y}_0:=\mathcal{Y}/G_{v_L}`.
There is then a natural finite and `G_{v_K}`-invariant morphism

.. MATH::

     \Phi_0:\mathcal{Y}_0\to\mathcal{X}_0,

called the **Galois invariant model** of the reduction. A crucial point
of our method is that the reduction `\Phi_L` is uniquely determined by the
following data:

- the `v_K`- model `\mathcal{X}_0` of `X=\mathbb{P}^1_K`, and
- the Galois extension `L/K`, and
- the extension `v_L` of `v_K` to `L`.

To see this, note that `\mathcal{Y}` and `\mathcal{X}` are the normalization of
`\mathcal{X}_0` inside the function fields `F(Y_L)` and `F(X_L)=L(x)`,
respectively, localized at `v_L`.

Conversely, given any normal `v_K`-model `\mathcal{X}_0` of `X`, a Galois
extension `L/K` and an extension `v_L` of `v_K` to `L`, normalization yields a
Galois-invariant reduction `\Phi_L` of `\phi` at `v_L`.

To summarize the discussion up to this point: the reduction of a cover
`\phi:Y\to X` at a place `v_K` can be described solely by a normal `v_K`-model
of the projective line `X`.

This module realizes a base class ``ReductionTree`` which is able to store
the essential information about a reduction of a cover `\phi`. It also provides
some general functionality for extracting this information.

Essentially, a ``ReductionTree`` is a ``BerkovichTree`` (see ??), together with
some extra information.

AUTHORS:

- Stefan Wewers (2017-8-10): initial version


EXAMPLES::

    Add examples ..

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
from mac_lane import *
from mclf.berkovich import *

#----------------------------------------------------------------------------

#                       Reduction trees
#                       ===============


class ReductionTree(SageObject):
    r"""
    Initialize and return a reduction tree associated to a curve and a valuation.

    INPUT:

    - ``Y`` -- a curve over a basefield `K`, given as ``SmoothProjectiveCurve``
    - ``vK`` -- a discrete valuation on `K`
    - ``T`` -- a Berkovich tree on the Berkovich line `X^{an}` underlying `(Y,v_K)`,
      or ``None`` (default: ``None``)

    OUTPUT: the reduction tree for ``Y`` relative to ``vK``, with given Berkovich tree.

    If ``T`` is ``None`` then the reduction tree is empty (and vertices may be
    added 'by hand').

    .. NOTE::

        In the present release, the base field `K` must be a number field.

    """

    def __init__(self, Y, vK, T=None):

        assert Y.constant_base_field() == vK.domain()
        self._Y = Y
                     # Y is a SmoothProjectiveCurve
        self._X = BerkovichLine(Y.rational_function_field(), vK)
                     # X is a BerkovichLine
        self._vK = vK
        if T == None:
            self._T = BerkovichTree(self._X)
        else:
            self._T = T
        self._reduction_components = []
        self._reduction_nodes = []

    def __repr__(self):

        return "Reduction of %s, relative to %s"%(self._Y, self._vK)

    def curve(self):
        r"""
        Return the curve `Y`.
        """
        return self._Y

    def berkovich_line(self):
        r"""
        Return the Berkovich line `X` of which the curve `Y` is a cover.
        """
        return self._X

    def base_valuation(self):
        r"""
        Return the specified valuation of the base field.
        """
        return self._vK

    def base_field(self):
        r"""
        Return the base field.
        """
        return self._vK.domain()


    def reduction_components(self):
        r"""
        Return the list of reduction components.
        """
        return self._reduction_components

    def add_reduction_component(self, xi, eta_list=[], basepoint=None):
        r"""
        Add a new reduction component to the tree.

        INPUT:

        - ``xi`` -- a point of type II on the underlying Berkovich line
        - ``eta_list`` -- a list of type-V-points (default: ``[]``)
        - ``base_point`` -- a point of type I (default: ``None``)

        OUTPUT: The reduction tree is changed in the following way:

        - the point ``xi`` is added as a vertex of the reduction tree
        - a new ``ReductionComponent`` is created (with the initial values
          ``xi``, ``eta_list`` and ``base_point``) and added to the list
          of reduction components of this reduction tree.

        WARNING:

        We note that this is a potentially dangerous operation, if ``xi`` is
        not already a vertex of the tree. The probems is that when the tree
        changes, this information is not passed down to the reduction components.

        """
        self._T, subtree = self._T.add_point(xi)
        self._reduction_components.append(ReductionComponent(self, subtree, eta_list, basepoint))


    def reduction_genus(self):
        r"""
        Return the genus of the reduction.

        OUTPUT: a nonnegative integer, which is the genus of the reduction
        of the curve `Y` specified by the data in this ``ReductionTree``.

        .. Note::

            For the moment we only count the contribution of the reduction
            component, and the contribution of the loops is left out. Hence the
            result is correct only if `Y` has abelian reduction.

        """

        if not hasattr(self, "_reduction_genus"):
            self._reduction_genus = sum([Z.reduction_genus() for Z in self.reduction_components()])
            # for the moment, we only count the contribution of the components
            # and dismiss the loops.
        return self._reduction_genus



    def reduction_conductor(self):
        r"""
        Return the conductor of the curve.

        OUTPUT: a nonnegative integer, which is the conductor of the local Galois
        representation associated to the reduction which is specified in this
        ``ReductionTree``. If the reduction is semistable, then the result is
        the conductor of `Y`.

        .. Note::

            For the moment we only count the contribution of the reduction
            component, and the contribution of the loops is left out. Hence our
            result is only correct if the curve `Y` has abelian reduction.

        """

        if not hasattr(self, "_reduction_genus"):
            self._reduction_genus = sum([Z.reduction_genus() for Z in self.reduction_components()])
            # for the moment, we only count the contribution of the components
            # and dismiss the loops.
        return self._reduction_genus



    def is_semistable(self):
        r"""
        Check wether the reduction specified by this object is semistable.

        """

        return self.reduction_genus() == self.curve().genus()




#------------------------------------------------------------------------------

#                 Reduction components
#                 ====================


class ReductionComponent(SageObject):
    r"""
    Return the reduction component corresponding to a type-II-point.

    INPUT:

    - ``Y`` -- a reduction tree
    - ``subtree`` -- a subtree of the Berkovich tree of `Y`
    - ``eta_list`` -- a list of points of type V on `X`, with boundary point ``xi``
    - ``basepoint`` -- (default: ``None``) a point of type I on `X`, or ``None``

    OUTPUT: The reduction component on ``Y``, corresponding to the root of ``subtree``.

    The root `\xi` of the given subtree must be a point of type II on the
    Berkovich line `X` underlying `Y`. It corresponds to an irreducible component
    of the special fiber of the inertial model `\mathcal{X}_0` of `X` given
    by this reduction tree.

    The *reduction component* which is generated by this command is an object
    for hosting methods which compute information about the irreducible components
    of models `Y` lying above `\xi`, over various extensions of the base field.

    ``eta_list`` is not used at the moment.

    ``basepoint`` should be a point which specializes to the interior of the
    component of the model `\mathcal{X}_0` corresponding to `\xi`. It is used
    to compute the *splitting field* of the reduction component.
    If ``None`` is given, then a suitable point is chosen.

    """


    def __init__(self, Y, subtree, eta_list=[], basepoint=None):

        self._Y = Y
        self._subtree = subtree
        self._xi = subtree.root()
        assert self._xi.type() == "II", "xi must be a point of type II!"
        self._eta_list = eta_list
        self._basepoint = basepoint
        # we check whether the basepoint lies in the interior; both
        # basepoint and interior are created by this (if they were not already given)
        assert self.interior().is_contained_in(self.basepoint()), \
            "the basepoint must lie in the interior of the reduction component!"

    def curve(self):
        """
        Return the curve `Y`.
        """
        return self._Y.curve()

    def berkovich_line(self):
        """
        Return the underlying Berkovich line `X`.
        """
        return self._Y.berkovich_line()

    def type_II_point(self):
        """
        Return the type-II-point corresponding to this reduction component.
        """
        return self._xi

    def basepoint(self):
        """
        Return the base point.

        The *basepoint* is a type-I-point on the underlying Berkovich line which
        specializes to the interior of this component of the special fiber of
        `\mathcal{X}_0`. If no base point is given when the reduction component
        was created, then such a point is computed now.

        """
        if self._basepoint == None:
            self._basepoint = self.interior().point_close_to_boundary(self._xi)
        return self._basepoint


    def interior(self):
        r"""
        Return the interior of this reduction component.

        OUTPUT:

        an elementary affinoid subdomain of the underlying Berkovich line.

        The **interior** of a reduction component is the elementary affinoid
        subdomain of the underlying Berkovich line whose canonical reduction
        is an open affine subset of this reduction component of the base model
        `\mathcal{X}_0`.

        It is chosen such that the canonical reduction does not contain the
        points of intersection with the other components of `\mathcal{X}_{0,s}`
        and is disjoint from the residue classes corresponding to the elements
        of ``eta_list``.

        .. NOTE::

            At the moment, the interior is computed only once, when the reduction
            component is created. If the tree is changed later, the interior
            is not updated.
        """

        if not hasattr(self, "_interior"):
            eta_list = self._eta_list
            subtree = self._subtree
            xi = self._xi
            if not subtree.parent() == None:
                eta_list.append(TypeVPointOnBerkovichLine(xi, subtree.parent().root()))
            for child in subtree.children():
                eta_list.append(TypeVPointOnBerkovichLine(child.root(), subtree.parent().root()))
            print "eta_list = ", eta_list
            self._interior = ElementaryAffinoidOnBerkovichLine([eta_list])
        return self._interior

    def splitting_field(self, check=False):
        r"""
        Return a splitting field for this reduction component.

        INPUT:

        - ``check`` -- a boolean (default: ``False``)

        OUTPUT: a weak Galois extension `(L,v_L)` of the base field.

        At the moment, the *splitting field* of a reduction component is a
        weak Galois extension `(L,v_L)` of the base field with the following
        properties:

        - the basepoint becomes rational over the strict henselization of `(L,v_L)`
        - all lower components have multiplicities one over `(L,v_L)`
        - the fiber of the cover `\phi:Y\to X` over the base point splits over
          the strict henselization of `(L,v_L)`
        """
        pass


    def upper_components(self, vL=None, multiplicities=False):
        r"""
        Return the upper components relative to a given extension of the base field.

        INPUT:

        - ``vL`` -- a discrete valuation on a finite extension `L` of the base
          field `K`, extending the base valuation `v_K`. If ``vL`` is ``None``
          then we take for `L` the splitting field of the reduction component.
        - ``multiplicities`` -- a boolean (default: ``False``)

        OUTPUT: a list of curves over the residue field of `v_L`, or (if
        ``multiplicities`` is ``True``) a list of pairs `(W,m)`, where `W` is
        a curve and `m` is a positive integer.

        The entries of the list are the normalizations of the irreducible
        components of the special fiber of the `v_L`-model `\mathcal{Y}` lying
        over the given reduction component (possibly with their multiplicities).

        """
        pass

    def lower_components(self, vL=None, multiplicities=False):
        r"""
        Return the lower components relative to a given extension of the base field.

        INPUT:

        - ``vL`` -- a discrete valuation on a finite extension `L` of the base
          field `K`, extending the base valuation `v_K`. If ``vL`` is ``None``
          then we take for `L` the splitting field of the reduction component.
        - ``multiplicities`` -- a boolean (default: ``False``)

        OUTPUT: a list of curves over the residue field of `v_L`, or (if
        ``multiplicities`` is ``True``) a list of pairs `(W,m)`, where `W` is
        a curve and `m` is a positive integer.

        The entries of the list are the irreducible components of the special
        fiber of the `v_L`-model `\mathcal{X}` (the normalization of
        `\mathcal{X}_0`) lying over the given reduction component. The integer
        `m` acompanying the curve (if given) is the multiplivity of this component.

        """
        pass

    def reduction_genus(self, vL=None):
        r"""
        Return the sum of the genera of the upper components.

        INPUT:

        - ``vL`` -- a discrete valuation on a finite extension `L` of the base
          field `K`, extending the base valuation `v_K`. If ``vL`` is ``None``
          then we take for `L` the splitting field of the reduction component.

        OUTPUT: a nonnegative integer, the sum of the genera of the upper
        components for this reduction component, computed with respect to the
        extension `(L,v_L)`.
        """

        pass