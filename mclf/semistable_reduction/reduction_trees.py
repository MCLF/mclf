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
- normal models `\mathcal{X},\mathcal{Y}` of `X_L, Y_L` (with respect to `v_L`),
- a finite morphism `\Phi_L: \mathcal{Y} \to \mathcal{X}` extending `\phi`.

  Restriction of `\Phi_L` to the special fibers yields a finite
  morphism

.. MATH::

    \bar{\phi}: \bar{Y} \to \bar{X}

between (not necessarily smooth) curves over the residue field of `L`. This map
is often called a *reduction* of the cover `\phi`, by abuse of
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
- the extension `L/K`, and
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

    # sage: from mclf import *
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

- if we create a reduction tree from a tree `T`, there should be certain
  requirements on `T` which insure that it makes sense. For instance, if
  we mark a vertex as a ``BaseComponent``, then the interior of this component
  should be well defined.
- if we allow adding new vertices to the tree, then it must be made sure that
  the above requirements are kept, and all the adjustements which we do to the
  tree must be passed on to the base components.
- Maybe it is safer to not allow any adjustements to the tree at all.

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

        In the present release, the base field `K` must be the field of rational
        numbers.
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
        Return the list of base components.
        """
        return self._reduction_components


    def add_reduction_component(self, xi, basepoint=None):
        r"""
        Add a new base component to the tree.

        INPUT:

        - ``xi`` -- a point of type II on the underlying Berkovich line
        - ``base_point`` -- a point of type I (default: ``None``)

        OUTPUT: The reduction tree is changed in the following way:

        - the point ``xi`` is added as a vertex of the reduction tree
        - a new ``BaseComponent`` is created (with the initial values
          ``xi`` and ``base_point``) and added to the list
          of base components of this reduction tree.

        .. WARNING::

        We note that this is a potentially dangerous operation, if ``xi`` is
        not already a vertex of the tree. The probems is that when the tree
        changes, this information is not passed down to the base components.

        """
        subtree = self._T.find_point(xi)
        if subtree == None:
            self._T, subtree = self._T.add_point(xi)
            print "warning: had to add %s to the tree."%xi
        self._reduction_components.append(BaseComponent(self, subtree, basepoint))


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
        if not hasattr(self, "_reduction_conductor"):
            self._reduction_conductor = sum([Z.reduction_conductor() for Z in self.reduction_components()])
            # for the moment, we only count the contribution of the components
            # and dismiss the loops.
        return self._reduction_conductor


    def is_semistable(self):
        r"""
        Check wether the reduction specified by this object is semistable.

        """
        return self.reduction_genus() == self.curve().genus()


    def is_reduced(self):
        r"""
        Check whether all upper components of this reduction tree have multiplicity one.

        """
        return all(Z.is_reduced() for Z in self.reduction_components())




#------------------------------------------------------------------------------

#                    base components
#                    ===============


class BaseComponent(SageObject):
    r"""
    Return the base component corresponding to a type-II-point.

    INPUT:

    - ``Y`` -- a reduction tree
    - ``subtree`` -- a subtree of the Berkovich tree underlying `Y`;
      its root `\xi` is a point of type II on the Berkovich line `X` underlying `Y`
    - ``basepoint`` -- (default: ``None``) a point of type I on `X`, or ``None``

    OUTPUT: The base component on ``Y``, corresponding to the root of ``subtree``.

    It is assumed that `\xi` is a vertex of the given reduction tree. It thus
    corresponds to an irreducible component of the special fiber of the base
    model `\mathcal{X}_0` of `X` given by this reduction tree. (If `\xi` is not
    a vertex of the tree, it is added to the tree.)

    The *base component* which is generated by this command is an object
    for hosting methods which compute information about the irreducible components
    of models `Y` lying above `\xi`, over various extensions of the base field.

    ``basepoint`` should be a point which specializes to the interior of the
    component of the model `\mathcal{X}_0` corresponding to `\xi`. It is used
    to compute the *splitting field* of the base component.
    If ``None`` is given, then a suitable point is chosen.

    """

    def __init__(self, Y, subtree, basepoint=None):
        self._Y = Y
        self._subtree = subtree
        self._xi = subtree.root()
        assert self._xi.type() == "II", "xi must be a point of type II!"
        if basepoint != None:
            self._basepoint = basepoint
        # we check whether the basepoint lies in the interior; both
        # basepoint and interior are created by this (if they were not already given)
        assert self.interior().is_contained_in(self.basepoint()), \
            "the basepoint must lie in the interior of the base component!"
        self._lower_components = {}
        self._upper_components = {}
        self._reduction_genus = {}


    def __repr__(self):
        return "base component of reduction tree with interior %s"%self.interior()


    def reduction_tree(self):
        r"""
        Return the reduction tree of this component.
        """
        return self._Y


    def curve(self):
        r"""
        Return the curve `Y`.
        """
        return self._Y.curve()


    def berkovich_line(self):
        r"""
        Return the underlying Berkovich line `X`.
        """
        return self._Y.berkovich_line()


    def type_II_point(self):
        r"""
        Return the type-II-point `\xi` corresponding to this base component.
        """
        return self._xi


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
        Return the interior of this base component.

        OUTPUT:

        an elementary affinoid subdomain of the underlying Berkovich line.

        The **interior** of a base component is the elementary affinoid
        subdomain of the underlying Berkovich line whose canonical reduction
        is an open affine subset of this base component of the base model
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
            eta_list = []
            subtree = self._subtree
            xi = self._xi
            if not subtree.parent() == None:
                eta_list.append(TypeVPointOnBerkovichLine(xi, subtree.parent().root()))
            for child in subtree.children():
                eta_list.append(TypeVPointOnBerkovichLine(xi, child.root()))
            self._interior = ElementaryAffinoidOnBerkovichLine([eta_list])
        return self._interior


    def splitting_field(self, check=False):
        r"""
        Return a splitting field for this base component.

        INPUT:

        - ``check`` -- a boolean (default: ``False``)

        OUTPUT: a weak Galois extension `(L,v_L)` of the base field.

        At the moment, the *splitting field* of a base component is a
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
            fiber = self.curve().fiber(self.basepoint().function_field_valuation())
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


    def inertial_valuations(self):
        r"""
        Return the valuations corresponding to the inertial components.

        """
        if not hasattr(self, "_inertial_valuations"):
            F = self.reduction_tree().curve().function_field()
            F0 = self.reduction_tree().berkovich_line().function_field()
            assert F0 is F.base()
            v = self.type_II_point().valuation()
            # v is a discrete valuation on F0
            self._inertial_valuations = [FunctionFieldValuation(F, w) for w in v.mac_lane_approximants(F.polynomial())]
        return self._inertial_valuations


    def upper_components(self, u=Infinity):
        r"""
        Return the upper components relative to a given extension of the base field.

        INPUT:

        - ``u`` -- an integer, or ``Infinity`` (default: ``Infinity``)

        OUTPUT: the list of upper components of the model of the reduction tree
        over this base component. If `u=` ``-1`` then the splitting field
        of this base component is used to compute the upper components. Otherwise,
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
        `\mathcal{X}_0`) lying over the given base component.

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
        lower_valuations = [xi.valuation() for xi in XL.points_from_inequality(f, s)]

        lower_components = [LowerComponent(self, vL, v) for v in lower_valuations]
        self._lower_components[u] = lower_components
        return lower_components


    # maybe this is obsolte now
    def upper_valuations(self, vL=None):
        r"""
        Return the valuations corresponding to the upper components of this
        base component, relative to a given extension of the base field.

        INPUT:

        - ``vL`` -- a discrete valuation of a finite extension `L` of the base field.

        OUTPUT:

        the list of all extensions of the inertial component to the function field
        of the base of `Y` to L, which restrict to `v_L`.

        .. WARNING::

            For the moment, it is not checked whether the resulting valuations
            extend `v_L`. Hence the result is only correct if `v_L` is the unique
            extension of the base valuation to `L`.

        """
        if vL == None:
            vL = self.splitting_field().valuation()
        lower_valuations = self.lower_valuations(vL)
        FYL = base_change_of_function_field(self.curve().function_field(), vL.domain())
        upper_valuations = []
        for v in lower_valuations:
            # upper_valuations += v.extensions(FYL)
            # this does not work due to a bug in mac_lane
            new_valuations = [FunctionFieldValuation(FYL, w) for w in v.mac_lane_approximants(FYL.polynomial())]
            upper_valuations += new_valuations
            # it is not checked whether these extensions restrict to vL
        return upper_valuations


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


    def is_reduced(self):
        r"""
        Check whether all upper components have multiplicity one.

        """
        pass


    def reduction_conductor(self):
        r"""
        Return the contribution of this base component to the conductor exponent.

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
        return self._base_component.reduction_tree()


    def base_component(self):
        r"""
        Return the base component underlying this reduction component.

        """
        return self._base_component


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

    - ``Z0`` -- a base component of a reduction tree `Y`
    - ``vL`` -- a discrete valuation on a finite extension `L` of the base
      field of `Y`, extending the base valuation on `Y`
    - ``v`` -- a discrete valuation on the base extension to `L` of the function
      field `F_X`, extending `v_L`

    OUTPUT: The lower component above `Z` corresponding to `v`.

    """
    def __init__(self, Z0, vL, v):
        self._base_component = Z0
        self._valuation = v
        self._base_valuation = vL
        F = make_function_field(v.residue_field())
        self._function_field = F
        self._constant_base_field = vL.residue_field()
        self._curve = SmoothProjectiveCurve(F, vL.residue_field())


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
        self._base_component = Z.base_component()
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
