r"""
Reduction trees: a data structure for semistable reduction of covers of the projective line.
============================================================================================

Let `K` be a field with a discrete valuation `v_K`. We let `X:=\mathbb{P}^1_K`
denote the projective line over `K`. We are also given a finite cover

.. MATH::

      \phi: Y \to X,

where `Y` is a smooth projective and absolutely irreducible curve. We assume that
`Y` has positive genus.

Let `\mathcal{X}_0` be a (normal) `v_K`-model of `X`. Then for every finite
field extension `L/K` and every extension `v_L` of `v_K` to `L`, we obtain
`v_L`-models `\mathcal{X}` of `X_L` and `\mathcal{Y}` of `Y_L` and a finite map
`\mathcal{Y}\to\mathcal{X}` extending `\phi` by normalizing `\mathcal{X}_0`.
Restricting this map to the special fiber yields a finite map

.. MATH::

         \bar{\phi}: \bar{Y} \to \bar{X}

between projective curves over the residue field of `v_L`. We call this the
*reduction* of `\phi` *over* `(L,v_L)` with respect to the *inertial model*
`\mathcal{X}_0`.

If we fix `\phi` and `\mathcal{X}_0` then there exists `(L,v_L)` such that the
curves `\bar{Y}` and `\bar{X}` are reduced. If this is the case, any further
extension of `(L,v_L)` will not change `\bar{Y}` and `\bar{X}` in an essential
way (more precisely, it will only replace `\bar{Y}` and `\bar{X}` by their
base extensions to the larger residue field). Therefore we call the models
`\mathcal{Y}` and `\mathcal{X}` *permanent*.

We say that `\mathcal{X}_0` is a *semistable inertial model* of `\phi` if
the permanent models `\mathcal{Y}` and `\mathcal{X}` are semistable, and
all irreducible components of the (semistable) curves `\bar{Y}` and `\bar{X}`
are smooth (i.e. they do not intersect themselves).

The class ``ReductionTree`` defined in this module is a datastructure which
encodes a cover `\phi:Y\to X` and an inertial model `\mathcal{X}_0` as above,
and provides functionality for computing the reduction
`\bar{\phi}:\bar{Y}\to\bar{X}` with respect to extensions `(L,v_L)`. In
particular, it allows us to check whether the given inertial model `\mathcal{X}_0`
is semistable and, if this is the case, to compute the semistable reduction of
the curve `Y`.


The inertial model
------------------

The inertial model `\mathcal{X}_0` of `X` is determined by a *Berkovich tree*
`T` on the analytic space `X^{an}` (the *Berkovich line* over `\hat{K}`, the
completion of `K` with respect to `v_K`). Thus,
* the irreducible components of the special fiber of `\mathcal{X}_0` (called
  the *inertial components*) correspond to the vertices of `T` which are points
  of type II on `X^{an}`.
* the vertices of `T` which are points of type I (i.e. closed points on `X`)
  are considered *marked points* on `X`
* an edge of `T` connecting two points of type II correspond to the point
  of intersection of the two corresponding inertial components
* an edge of `T` connecting a point of type II and a point of type II corresponds
  to the specialization of a marked point to an inertial component

In particular, the inertial model `\mathcal{X}_0` is a *marked* model. As a
result, the models `\mathcal{X}` and `\mathcal{Y}` induced by `\mathcal{X}_0`
and an extension `(L,v_L)` are marked models, too. The condition that
`\mathcal{X}_0` is a semistable inertial model therefore implies that `\mathcal{X}`
and `\mathcal{Y}` are *marked* semistable models, for `L/K` sufficiently large.
Recall that this means that the marked points specialize to the smooth points
on the special fiber.


Reduction components
--------------------

Let us fix an inertial component `Z_0`. The *interior* of `Z_0` is the affinoid
subdomain of `X^{an}` consisting of all points which specialize to a point on
`Z_0` which is neither the point of intersection with another inertial component
nor the specialization of a marked point (exception: if there is a unique
inertial component and no marking then this is all of `X^{an}` and not an
affinoid). We have to choose a *basepoint* for `Z_0`, which is a closed point on
`X` lying inside the interior. This choice is made in a heuristic manner;
the degree of the base point should be as small as possible. Then a *splitting
field* for `Z_0` is a finite extension `(L,v_L)` of `(K,v_K)` with the property
that the base point and all points on `Y` above it are `\hat{L}`-rational (where
`\hat{L}` denotes the completion of `L` with respect to `v_L`).





AUTHORS:

- Stefan Wewers (2017-8-10): initial version


EXAMPLES::

    sage: from mclf import *
    sage: FX.<x> = FunctionField(QQ)
    sage: v_2 = pAdicValuation(QQ, 2)
    sage: X = BerkovichLine(FX, v_2)
    sage: T = BerkovichTree(X, X.gauss_point())
    sage: T, _ = T.add_point(X.infty())
    sage: R.<y> = FX[]
    sage: FY.<y> = FX.extension(y^2-x^3-1)
    sage: Y = SmoothProjectiveCurve(FY)
    sage: RT = ReductionTree(Y, v_2, T)
    sage: RT.add_reduction_component(T.root())
    sage: Z = RT.reduction_components()[0]
    sage: Z
    base component of reduction tree with interior Elementary affinoid defined by
    v(x) >= 0

TODO:


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
from sage.rings.all import ZZ, NumberField, FunctionField
from mac_lane import *
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.berkovich_trees import BerkovichTree
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
from mclf.berkovich.affinoid_domain import ElementaryAffinoidOnBerkovichLine
from mclf.padic_extensions.fake_padic_completions import FakepAdicCompletion
from mclf.padic_extensions.weak_padic_galois_extensions import WeakPadicGaloisExtension
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
from mclf.curves.morphisms_of_smooth_projective_curves import MorphismOfSmoothProjectiveCurves

#----------------------------------------------------------------------------

#                       Reduction trees
#                       ===============


class ReductionTree(SageObject):
    r"""
    Initialize and return a reduction tree associated to a curve and a valuation.

    INPUT:

    - ``Y`` -- a curve over a basefield `K`, given as ``SmoothProjectiveCurve``
    - ``vK`` -- a discrete valuation on `K`
    - ``T`` -- a Berkovich tree on the Berkovich line `X^{an}` underlying `(Y,v_K)`

    OUTPUT: a reduction tree for ``Y`` relative to ``vK``; the inertial model
    `\mathcal{X}_0` is the marked model of `X` induced by the Berkovich tree `T`.
    Note that after initialization, the list of *inertial components* is empty.
    The user has to mark those vertices of `T` which correspond to components
    of `\mathcal{X}_0` and which he wishes to use for the computation of the
    reduction of `\phi` by adding them to this list via the method
    ``add_inertial_component``.


    .. NOTE::

        In the present release, the base field `K` must be the field of rational
        numbers.
    """


    def __init__(self, Y, vK, T):

        assert Y.constant_base_field() == vK.domain()
        self._Y = Y
                     # Y is a SmoothProjectiveCurve
        self._X = BerkovichLine(Y.rational_function_field(), vK)
                     # X is a BerkovichLine
        self._vK = vK
        self._T = T
        self._inertial_components = []


    def __repr__(self):

        return "A reduction tree for  %s, relative to %s"%(self._Y, self._vK)


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


    def inertial_components(self):
        r"""
        Return the list of inertial components.
        """
        return self._inertial_components


    def add_inertial_component(self, xi, basepoint=None):
        r"""
        Add a new inertial component to the list of such.

        INPUT:

        - ``xi`` -- a point of type II on the underlying Berkovich line; it
          is assumed that ``xi`` is a vertex of the Berkovich tree `T`

        OUTPUT: a new inertial component is created and appended to the list
        of all inertial components.

        """
        self._inertial_components.append(InertialComponent(self, xi))


    def reduction_genus(self):
        r"""
        Return the genus of the reduction.

        OUTPUT: a nonnegative integer, which is the genus of the reduction
        of the curve `Y` specified by the data in this ``ReductionTree``.

        .. Note::

            For the moment we only count the contribution of the inertial
            component, and the contribution of the loops is left out. Hence the
            result is correct only if `Y` has abelian reduction.

        """
        if not hasattr(self, "_reduction_genus"):
            self._reduction_genus = sum([Z.reduction_genus() for Z in self.inertial_components()])
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
        if not hasattr(self, "_reduction_conductor"):
            self._reduction_conductor = sum([Z.reduction_conductor() for Z in self.inertial_components()])
            # for the moment, we only count the contribution of the components
            # and dismiss the loops.
        return self._reduction_conductor


    def is_semistable(self):
        r"""
        Check wether the reduction specified by this object is semistable.

        """
        return self.reduction_genus() == self.curve().genus()



#------------------------------------------------------------------------------

#                    inertial components
#                    ===============


class InertialComponent(SageObject):
    r"""
    Return the inertial component corresponding to a type-II-point which is
    a vertex of `T`.

    INPUT:

    - ``R`` -- a reduction tree
    - ``xi`` -- a point of type II on the Berkovich line `X` underlying `R`;
      it is assumed that `\xi` is a vertex of the Berkovich tree `T` underlying `R`

    OUTPUT: The base component corresponding to `\xi`.

    It is assumed that `\xi` is a vertex of the given Berkovich tree. It thus
    corresponds to an irreducible component of the special fiber of the inertial
    model `\mathcal{X}_0`. If this is not the case, an error is raised.

    The *inertial component* which is generated by this command is an object
    for hosting methods which compute information about the irreducible components
    of models `Y` of `X` lying above `\xi`, over various extensions of the base field.

    """
    def __init__(self, R, xi):
        assert xi.type() == "II", "xi must be a point of type II!"
        self._R = R
        subtree = R._T.find_point(xi)
        assert subtree, "xi must be a vertex of T"
        self._subtree = subtree
        self._xi = xi
        self._valuation = xi.valuation()
        self._curve = SmoothProjectiveCurve(make_function_field(xi.valuation().residue_field()))
        self._lower_components = {}
        self._upper_components = {}
        self._reduction_genus = {}


    def __repr__(self):
        return "inertial component of reduction tree with interior %s"%self.interior()


    def reduction_tree(self):
        r"""
        Return the reduction tree of this component.
        """
        return self._R


    def curve(self):
        r"""
        Return the smooth projective curve underlying this inertial component.
        """
        return self._curve


    def function_field(self):
        r"""
        Return the function field of this inertial component
        (which is the residue field of the valuation corresponding to it).
        """
        return self.curve().function_field()


    def berkovich_line(self):
        r"""
        Return the underlying Berkovich line `X`.
        """
        return self._R.berkovich_line()


    def type_II_point(self):
        r"""
        Return the type-II-point `\xi` corresponding to this base component.

        """
        return self._xi


    def valuation(self):
        return self._valuation


    def basepoint(self):
        r"""
        Return the base point.

        The *basepoint* is a type-I-point on the underlying Berkovich line which
        specializes to the interior of this component of the special fiber of
        `\mathcal{X}_0`. If no base point is given when the base component
        was created, then such a point is computed now.

        """
        if not hasattr(self, "_basepoint"):
            self._basepoint = self.interior().point_close_to_boundary(self._xi)
        return self._basepoint


    def interior(self):
        r"""
        Return the interior of this inertial component.

        OUTPUT:

        an elementary affinoid subdomain of the underlying Berkovich line.

        The **interior** of a base component is the elementary affinoid
        subdomain of the underlying Berkovich line whose canonical reduction
        is an open affine subset of this inertial component of the inertial model
        `\mathcal{X}_0`.

        It is chosen such that the canonical reduction does not contain the
        points of intersection with the other components of `\mathcal{X}_{0,s}`
        and is disjoint from the residue classes of the marked points.

        """
        if not hasattr(self, "_interior"):
            eta_list = []
            subtree = self._subtree
            xi = self._xi
            if subtree.has_parent():
                eta_list.append(TypeVPointOnBerkovichLine(xi, subtree.parent().root()))
            for child in subtree.children():
                eta_list.append(TypeVPointOnBerkovichLine(xi, child.root()))
            self._interior = ElementaryAffinoidOnBerkovichLine([eta_list])
        return self._interior


    def splitting_field(self, check=False):
        r"""
        Return a splitting field for this inertial component.

        INPUT:

        - ``check`` -- a boolean (default: ``False``)

        OUTPUT: a weak Galois extension `(L,v_L)` of the base field.

        At the moment, the *splitting field* of a inertial component is a
        weak Galois extension `(L,v_L)` of the base field with the following
        properties:

        - the basepoint becomes rational over the strict henselization of `(L,v_L)`
        - all lower components have multiplicities one over `(L,v_L)`
        - the fiber of the cover `\phi:Y\to X` over the base point splits over
          the strict henselization of `(L,v_L)`

        .. WARNING::

            For the moment, this only works if the basepoint is contained inside
            the closed unit disk.

        """
        if not hasattr(self, "_splitting_field"):
            vK = self.reduction_tree().base_valuation()
            K = vK.domain()
            # K must be number field for the rest to work
            # Actually, it must be QQ!
            assert K == QQ, "K must be QQ"
            Kh = FakepAdicCompletion(K, vK)
            fiber = self.reduction_tree().curve().fiber(self.basepoint().function_field_valuation())
            # `fiber` should be a list of points on Y
            F = []
            for xi in fiber:
                L = xi.residue_field()
                # L should be a (relative) number field (which may include QQ)
                if not L == QQ:
                    f = L.absolute_polynomial().change_ring(K)
                    F += [g for g,m in f.factor()]
            # F = self.curve().fiber_equations(self.basepoint().function_field_valuation())
            e = self.type_II_point().pseudovaluation_on_polynomial_ring().E()
            self._splitting_field = WeakPadicGaloisExtension(Kh, F, minimal_ramification=e)
        return self._splitting_field


    def upper_components(self, u=Infinity):
        r"""
        Return the upper components relative to a given extension of the base field.

        INPUT:

        - ``u`` -- an integer, or ``Infinity`` (default: ``Infinity``)

        OUTPUT: the list of upper components of the model of the reduction tree
        over this inertial component. If `u=` ``Infinity`` then the splitting field
        of this inertial component is used to compute the upper components. Otherwise,
        `u` must be step in the ramification filtration of the splitting field,
        and then the corresponding subfield is used.

        """
        if u in self._upper_components.keys():
            return self._upper_components[u]
            # we have already computed this before!

        lower_components = self.lower_components(u)
        upper_components = []
        for Z in lower_components:
            upper_components += Z.upper_components()
        self._upper_components[u] = upper_components
        return upper_components


    def lower_components(self, u=Infinity):
        r"""
        Return the lower components relative to a given extension of the base field.

        INPUT:

        - ``u`` -- an integer, or ``Infinity`` (default: ``Infinity``)

        OUTPUT: the list of lower components of the model of the reduction tree
        lying over this base component. If `u=\infty` then these components
        are computed over the splitting field of the base component. Otherwise,
        `u` is assumed to be a break in the ramification filtration of the
        splitting field, and then we use the corresponding subfield.

        The entries of the list correspond to the irreducible components of the
        special fiber of the `v_L`-model `\mathcal{X}` (the normalization of
        `\mathcal{X}_0`) lying over the given inertial component.

        """
        if u in self._lower_components.keys():
            return self._lower_components[u]
            # we have already computed this before!

        L = self.splitting_field()
        if u == Infinity:
            vL = L.valuation()
        else:
            L = L.ramification_subfield(u)
            vL = L.valuation()

        FX = self.berkovich_line().function_field()
        L = vL.domain()      # actually, this is the number field underlying L
        FXL = FunctionField(L, FX.variable_name())
        XL = BerkovichLine(FXL, vL)
        f, s = self.type_II_point().discoid()
        f = FXL(f)

        v0 = self.valuation()
        F0 = self.function_field()
        x0 = FXL(v0.lift(v0.residue_field().gen()))
        lower_valuations = [xi.valuation() for xi in XL.points_from_inequality(f, s)]
        lower_components = []
        for v in lower_valuations:
            F1 = make_function_field(v0.residue_field())
            phi = F0.hom(F1(v.reduce(x0)))
            lower_components.append(LowerComponent(self, vL, v, phi))
        self._lower_components[u] = lower_components
        return lower_components


    def reduction_genus(self, u=Infinity):
        r"""
        Return the sum of the genera of the upper components.

        INPUT:

        - ``u`` -- an integer, or Infinity (default: ``Infinity``)

        OUTPUT: a nonnegative integer, the sum of the genera of the upper
        components for this base component, computed with respect to the
        splitting field. If `u\neq\infty` then it is assumed that `u` is a
        break in the ramification filtration of the splitting field, and then
        the corresponding subfield is used instead.

        TODO:

        At the moment, the output is correct only if field of constants of all
        upper components is equal to the residue field of the valuation `v_L`.
        In general we have to multiply the genus of a component with the degree
        of the extension 'field of constants' over 'residue field of `v_L`'.

        """
        if u in self._reduction_genus.keys():
            return self._reduction_genus[u]
        else:
            self._reduction_genus[u] = sum([W.genus()*W.field_of_constants_degree()
                    for W in self.upper_components(u)])
            return self._reduction_genus[u]


    def reduction_conductor(self):
        r"""
        Return the contribution of this inertial component to the conductor exponent.

        """
        if not hasattr(self, "_reduction_conductor"):
            L = self.splitting_field()
            n = L.ramification_degree()
            ramification_filtration = L.ramification_filtration()
            if len(ramification_filtration) == 0:
                self._reduction_conductor = ZZ(0)
                return ZZ(0)

            delta_list = []
            for u, m_u in ramification_filtration:
                L_u = L.ramification_subfield(u)
                g_u = self.reduction_genus(u)
                delta_list.append((u, m_u, g_u))
            g = self.reduction_genus()
            g_0 = delta_list[0][2]
            epsilon = 2*(g - g_0)
            u, m_u, g_u = delta_list[0]
            delta = m_u/n*2*(g - g_u)*u
            for i in range(1,len(delta_list)):
                u, m_u, g_u = delta_list[i]
                v = delta_list[i-1][0]
                delta += m_u/n*2*(g - g_u)*(u - v)
            self._reduction_conductor = epsilon + delta

        return self._reduction_conductor


#-----------------------------------------------------------------------------

#                 reduction components
#                 ====================

class ReductionComponent(SageObject):
    r"""
    The superclass for the classes ``LowerComponent`` and ``UpperComponent``.

    """

    def reduction_tree(self):
        r"""
        Return the reduction tree underlying the reduction component.

        """
        return self._inertial_component.reduction_tree()


    def inertial_component(self):
        r"""
        Return the inertial component underlying this reduction component.

        """
        return self._inertial_component


    def base_valuation(self):
        r"""
        Return the base valuation of this reduction component.

        """
        return self._base_valuation


    def base_field(self):
        r"""
        Return the base field of this reduction component.

        """
        return self._base_valuation.domain()


    def valuation(self):
        r"""
        Return the valuation corresponding to this reduction component.

        """
        return self._valuation


    def curve(self):
        r"""
        Return the normalization of this reduction component.

        """
        return self._curve


    def function_field(self):
        r"""
        Return the function field of this reduction component.

        Note that the *function field* of this reduction component is the residue
        field of the corresponding valuation `v`. It must not be confused with
        the domain of `v`, which is the function field of the generic fiber.

        """
        return self._function_field


    def constant_base_field(self):
        r"""
        Return the constant base field of this reduction component.

        """
        return self._constant_base_field


    def multiplicity(self):
        r"""
        Return the multiplicity of this reduction component.

        """
        pi_L = self.base_valuation().uniformizer()
        pi = self.valuation().uniformizer()
        return ZZ(self.valuation()(pi_L)/self.valuation()(pi))


class LowerComponent(ReductionComponent):
    r"""
    Return the lower component corresponding to a given valuation.

    INPUT:

    - ``Z0`` -- an inertial component of a reduction tree `Y`
    - ``vL`` -- a discrete valuation on a finite extension `L` of the base
      field of `Y`, extending the base valuation on `Y`
    - ``v`` -- a discrete valuation on the base extension to `L` of the function
      field `F_X`, extending `v_L`
    - ``phi`` -- the natural morphism from the function field of ``Z0`` into
        the residue field of ``v``

    OUTPUT: The lower component above `Z` corresponding to `v`.

    """
    def __init__(self, Z0, vL, v, phi):
        self._inertial_component = Z0
        self._valuation = v
        self._base_valuation = vL
        F = make_function_field(v.residue_field())
        self._function_field = F
        self._constant_base_field = vL.residue_field()
        self._curve = SmoothProjectiveCurve(F, vL.residue_field())
        self._phi = phi


    def __repr__(self):
        return "lower component of reduction tree corresponding to  %s"%self.valuation()


    def upper_components(self):
        r"""
        Return the list of all upper components lying above this lower component.

        """
        v = self.valuation()
        FY = self.reduction_tree().curve().function_field()
        FYL = base_change_of_function_field(FY, self.base_field())
        upper_valuations = [FunctionFieldValuation(FYL, w) for w in v.mac_lane_approximants(FYL.polynomial())]
        return [UpperComponent(self, w) for w in upper_valuations]


    def map_to_inertial_component(self):
        r"""
        Return the natural map from this lower component to its inertial component.

        """
        # we hope that this works by the natural inclusion of function fields:
        return MorphismOfSmoothProjectiveCurves(self.curve(), self.inertial_component().curve(), self._phi)


class UpperComponent(ReductionComponent):
    r"""
    Return the upper component corresponding to a given valuation.

    INPUT:

    - ``Z`` -- a lower component of a reduction tree `Y`
    - ``v`` -- a discrete valuation on the base extension to `L` of the function
      field `F_Y`, extending the valuation corresponding to `Z`

    OUTPUT: The lower component above `Z` corresponding to `v`.

    """
    def __init__(self, Z, v):
        self._lower_component = Z
        self._inertial_component = Z.inertial_component()
        self._base_valuation = Z.base_valuation()
        self._valuation = v
        self._function_field = make_function_field(v.residue_field())
        self._constant_base_field = Z.constant_base_field()
        self._curve = SmoothProjectiveCurve(self._function_field, Z.constant_base_field())


    def __repr__(self):
        return "upper component of reduction tree corresponding to  %s"%self.valuation()


    def genus(self):
        r"""
        Return the genus of this upper reduction component.

        """
        return self.curve().genus()


    def field_of_constants_degree(self):
        r"""
        Return the degree of the field of constants over the constant base field
        of this upper reduction component.

        """
        return self.curve().field_of_constants_degree()


    def lower_component(self):
        r"""
        Return the lower component underneath this upper component.
        """
        return self._lower_component


    def map_to_lower_component(self):
        r"""
        Return the natural map from this upper component to the lower component beneath.

        """
        # we hope that this works by the natural inclusion of function fields:
        return MorphismOfSmoothProjectiveCurves(self.curve(), self.lower_component().curve())


#-----------------------------------------------------------------------------

#                       auxiliary functions
#                       -------------------

def base_change_of_function_field(F, L):
    r"""
    Return the base change of a function field with respect to an extension
    of the base field.

    INPUT:

    - ``F`` -- a function field over a field `K`
    - ``L`` -- a finite field extension of `K`

    OUTPUT:

    the function field `F_L:= F\otimes_K L`.

    It is not checked whether the result is really a function field.

    """
    F0 = F.base()
    F0L = FunctionField(L, F0.variable_name())
    if F0 == F:
        # F is a rational function field
        return F0L
    else:
        return F0L.extension(F.polynomial().change_ring(F0L), F.variable_name())


def make_function_field(k):
    r"""
    Return the function field corresponding to this field.

    INPUT:

    - ``k`` -- the residue field of a discrete valuation on a function field.

    OUTPUT:

    the field `k` as a function field; this is rather experimental..

    """
    from sage.rings.function_field.function_field import is_FunctionField
    if is_FunctionField(k):
        return k
    if hasattr(k, "base_field"):
        # it seems that k is an extension of a rational function field
        k0 = k.base_field()
        f0 = FunctionField(k0.base_ring(), k0.base().variable_name())
        G = k.modulus().change_ring(f0)
        # G *should* be irreducible, but unfortunately this is sometimes
        # not true, due to a bug in Sage's factoring
        assert G.is_irreducible(), "G must be irreducible! This problem is probably caused by a bug in Sage's factoring."
        return f0.extension(G, 'y')
    else:
        # it seems that k is simply a rational function field
        return FunctionField(k.base_ring(), k.variable_name())
