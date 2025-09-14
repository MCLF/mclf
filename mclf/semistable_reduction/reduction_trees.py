# -*- coding: utf-8 -*-
r"""
Reduction trees: a data structure for semistable reduction of covers of the projective line
===========================================================================================

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


**The inertial model**

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
* an edge of `T` connecting a point of type II and a point of type I corresponds
  to the specialization of a marked point to an inertial component

In particular, the inertial model `\mathcal{X}_0` is a *marked* model. As a
result, the models `\mathcal{X}` and `\mathcal{Y}` induced by `\mathcal{X}_0`
and an extension `(L,v_L)` are marked models, too. The condition that
`\mathcal{X}_0` is a semistable inertial model therefore implies that `\mathcal{X}`
and `\mathcal{Y}` are *marked* semistable models, for `L/K` sufficiently large.
Recall that this means that the marked points specialize to the smooth points
on the special fiber.


**Reduction components**

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
    sage: v_2 = QQ.valuation(2)
    sage: X = BerkovichLine(FX, v_2)
    sage: T = BerkovichTree(X, X.gauss_point())
    sage: T, _ = T.add_point(X.infty())
    sage: R.<y> = FX[]
    sage: FY.<y> = FX.extension(y^2-x^3-1)
    sage: Y = SmoothProjectiveCurve(FY)
    sage: RT = ReductionTree(Y, v_2, T)
    sage: RT
    A reduction tree for  the smooth projective curve with Function field in y
    defined by y^2 - x^3 - 1, relative to 2-adic valuation
    sage: RT.inertial_components()
    [inertial component of reduction tree with interior Elementary affinoid defined by
     v(x) >= 0
     ]

TODO:

* better documentation
* more doctests

"""


# *****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************

from sage.rings.integer_ring import Z as ZZ
from sage.rings.rational_field import Q as QQ
from sage.rings.function_field.constructor import FunctionField
from sage.structure.sage_object import SageObject
from sage.rings.infinity import Infinity
from mclf.berkovich.berkovich_line import BerkovichLine
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
from mclf.berkovich.affinoid_domain import ElementaryAffinoidOnBerkovichLine
from mclf.padic_extensions.fake_padic_completions import FakepAdicCompletion
from mclf.padic_extensions.weak_padic_galois_extensions import WeakPadicGaloisExtension
from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve, PointOnSmoothProjectiveCurve
from mclf.curves.morphisms_of_smooth_projective_curves import MorphismOfSmoothProjectiveCurves

# ----------------------------------------------------------------------------

#                       Reduction trees
#                       ===============


class ReductionTree(SageObject):
    r"""
    Initialize and return a reduction tree associated to a curve and a valuation.

    INPUT:

    - ``Y`` -- a curve over a basefield `K`, given as ``SmoothProjectiveCurve``
    - ``vK`` -- a discrete valuation on `K`
    - ``T`` -- a Berkovich tree on the Berkovich line `X^{an}` underlying `(Y,v_K)`
    - ``separable_components`` -- a list of type-II-points on `X^{an}` which
      are vertices of `T` (or ``None``)

    OUTPUT: a reduction tree for ``Y`` relative to ``vK``; the inertial model
    `\mathcal{X}_0` is the marked model of `X` induced by the Berkovich tree `T`.

    Note that the tree `T` will be modified by the creation of the reduction tree.


    .. NOTE::

        In the present release, the base field `K` must be the field of rational
        numbers.

    """

    def __init__(self, Y, vK, T, separable_components=None):

        assert Y.constant_base_field() == vK.domain()
        self._Y = Y
        self._vK = vK
        self._T = T
        self._X = T.berkovich_line()

        if separable_components is None:
            # all vertices of T are marked as "separable"
            for T1 in T.subtrees():
                T1.is_separable = True
        else:
            # only vertices in separable_components are marked as "separable"
            for T1 in T.subtrees():
                T1.is_separable = False
            for xi in separable_components:
                T1 = T.find_point(xi)
                assert T1 is not None, "xi is not a vertex of T"
                T1.is_separable = True

        # create the inertial components
        inertial_components = []
        for T1 in T.subtrees():
            xi = T1.root()
            if xi.type() == "II":
                Z = InertialComponent(self, xi, T1.is_separable)
                T1.inertial_component = Z
                inertial_components.append(Z)
        self._inertial_components = inertial_components

    def __repr__(self):
        return "A reduction tree for  {}, relative to {}".format(self._Y, self._vK)

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

    def berkovich_tree(self):
        r"""
        Return the Berkovich tree underlying this reduction tree.
        """
        return self._T

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

    def add_inertial_component(self, xi):
        r"""
        Add a new inertial component to the list of such.

        INPUT:

        - ``xi`` -- a point of type II on the underlying Berkovich line; it
          is assumed that ``xi`` is a vertex of the Berkovich tree `T`

        OUTPUT: a new inertial component `Z` is created and appended to the list
        of all inertial components. Moreover, `Z` is assigned to the new
        attribute ``inertial_component``  of the subtree of `T` with root
        `\xi`.

        """
        subtree = self.berkovich_tree().find_point(xi)
        assert subtree is not None, "xi is not a vertex of the given Berkovich tree"
        Z = InertialComponent(self, xi)
        self._inertial_components.append(Z)
        subtree.inertial_component = Z

    def reduction_genus(self):
        r"""
        Return the genus of the reduction.

        OUTPUT: a nonnegative integer, which is the arithmetic genus of the reduction
        of the curve `Y` specified by the data in this ``ReductionTree``, provided
        this reduction is semistable.

        In fact, the number we compute is the sum of the genera of the upper
        components (i.e. the normalizations of the irreducible components of
        `\bar{Y}`) and the number of loops of the component graph of `\bar{Y}`,
        which is (number of double points) - (number of components) + 1.

        EXAMPLES:

        We test that the arithmetic genus of a totally degenerate curve is computed correctly::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: v_3 = QQ.valuation(3)
            sage: f = (x^2 - 3)*(x^2 + 3)*(x^3 - 3)
            sage: Y = SuperellipticCurve(f, 2)
            sage: Y.genus()
            3
            sage: Y3 = SemistableModel(Y, v_3)
            sage: Y3.reduction_tree().reduction_genus()
            3

        """
        if not hasattr(self, "_reduction_genus"):
            reduction_genus = 1
            for Z in self.inertial_components():
                reduction_genus += Z.reduction_genus() + Z.outdegree() - Z.component_degree()
            self._reduction_genus = reduction_genus
        return self._reduction_genus

    def reduction_conductor(self):
        r"""
        Return the conductor of the curve.

        OUTPUT: a nonnegative integer, which is the conductor of the local Galois
        representation associated to the reduction which is specified in this
        ``ReductionTree``. If the reduction is semistable, then the result is
        the conductor of `Y`.

        TODO: Write better documentation.

        EXAMPLES:

        We check that the conductor exponent takes the component graph into account as well::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Y = SuperellipticCurve(x^3 + x^2 + 3, 2)
            sage: Y3 = SemistableModel(Y, QQ.valuation(3))
            sage: Y3.is_semistable()
            True
            sage: Y3.conductor_exponent() # indirect doctest
            1

        """
        if not hasattr(self, "_reduction_conductor"):
            self._reduction_conductor = 1 + sum([Z.reduction_conductor() for Z in self.inertial_components()])
        return self._reduction_conductor

    def is_semistable(self):
        r"""
        Check whether the reduction specified by this object is semistable.

        """
        return self.reduction_genus() == self.curve().genus()


# ------------------------------------------------------------------------------

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
    - ``is_separable`` -- boolean (default: ``True``)

    OUTPUT: The base component corresponding to `\xi`.

    It is assumed that `\xi` is a vertex of the given Berkovich tree. It thus
    corresponds to an irreducible component of the special fiber of the inertial
    model `\mathcal{X}_0`. If this is not the case, an error is raised.

    The *inertial component* which is generated by this command is an object
    for hosting methods which compute information about the irreducible components
    of models `Y` of `X` lying above `\xi`, over various extensions of the base field.

    """

    def __init__(self, R, xi, is_separable=True):
        assert xi.type() == "II", "xi must be a point of type II!"
        self._R = R
        subtree = R._T.find_point(xi)
        assert subtree, "xi must be a vertex of T"
        self._subtree = subtree
        self._xi = xi
        self._valuation = xi.valuation()
        F, phi, psi = make_function_field(xi.valuation().residue_field())
        k = R.base_valuation().residue_field()
        # this is the natural constant base field of the component;
        # we assume here that it is a finite field, and the embedding
        # of k into F can be easily determined
        self._component = SmoothProjectiveCurve(F, k)
        # we have to remember the isomorphism between the residue field and F
        self._to_function_field = phi
        self._from_function_field = psi
        self._lower_components = {}
        self._upper_components = {}
        self._reduction_genus = {}
        self._is_separable = is_separable

    def __repr__(self):
        return "inertial component of reduction tree with interior {}".format(self.interior())

    def reduction_tree(self):
        r"""
        Return the reduction tree of this component.
        """
        return self._R

    def is_separable(self):
        r"""
        Return ``True`` is this inertial component is separable.
        """
        return self._is_separable

    def component(self):
        r"""
        Return the smooth projective curve underlying this inertial component.

        Note that the constant base field of this curve is, by definition,
        the residue field of the base valuation. This may differ from the
        field of constants of its function field.
        """
        return self._component

    def function_field(self):
        r"""
        Return the function field of this inertial component
        (which is the residue field of the valuation corresponding to it).
        """
        return self.component().function_field()

    def reduce(self, f):
        r""" Return the reduction of a rational function to this component.

        INPUT:

        - ``f`` -- an element of the function field of the Berkovich line

        It is assumed that `f` a unit of the valuation ring corresponding to
        this component.

        OUTPUT: the image of `f` in the function field of this component.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Y = SuperellipticCurve(x^3-1, 2)
            sage: Y3 = SemistableModel(Y, QQ.valuation(3))
            sage: Z = Y3.reduction_tree().inertial_components()[1]
            sage: f = Z.valuation().element_with_valuation(1/2)^2/3
            sage: Z.reduce(f)
            x

        """
        assert self.valuation()(f) == 0, "f must be a unit of the valuation ring"
        return self._to_function_field(self.valuation().reduce(f))

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
        r"""
        Return the valuation on the function field corresponding to this component.

        """
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
        from mclf.berkovich.affinoid_domain import AffinoidTree
        X = self.berkovich_line()
        if not hasattr(self, "_interior"):
            subtree = self._subtree
            xi = self._xi
            T = AffinoidTree(X, root=xi, is_in=True)
            for child in subtree.children():
                T1 = AffinoidTree(X, root=child.root(), is_in=False)
                T.make_child(T1)
            if subtree.has_parent():
                T1 = AffinoidTree(X, root=subtree.parent().root(), is_in=False)
                T1.make_child(T)
                T = T1
            self._interior = ElementaryAffinoidOnBerkovichLine(T)
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
        - if the inertial component is marked as *separable* then the fiber of
          the cover `\phi:Y\to X` over the base point splits over
          the strict henselization of `(L,v_L)`

        .. WARNING::

            For the moment, this only works if the basepoint is contained inside
            the closed unit disk.

        """
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

        if not hasattr(self, "_splitting_field"):
            vK = self.reduction_tree().base_valuation()
            K = vK.domain()
            # K must be number field for the rest to work
            # Actually, it must be QQ!
            assert K == QQ, "K must be QQ"
            Kh = FakepAdicCompletion(K, vK)

            R = PolynomialRing(K, 'x')
            if self.is_separable():
                fiber = self.reduction_tree().curve().fiber(self.basepoint().function_field_valuation())
                # `fiber` should be a list of points on Y
                F = []
                for xi in fiber:
                    L = xi.residue_field()
                    # L should be a (relative) number field (which may include QQ)
                    if not L == QQ:
                        f = L.absolute_polynomial().change_ring(K)
                        f = R(f)
                        F += [g for g, m in f.factor()]
                # F = self.curve().fiber_equations(self.basepoint().function_field_valuation())
            else:
                L = self.basepoint().function_field_valuation().residue_field()
                if L == QQ:
                    F = []
                else:
                    f = L.absolute_polynomial().change_ring(K)
                    f = R(f)
                    F = [f]
            e = self.type_II_point().pseudovaluation_on_polynomial_ring().E()
            # print("F = ", F)
            # print("e = ", e)
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
        `\mathcal{X}_0`) lying over the given inertial component. By definition,
        the constant base field of these components is the residue field of
        `v_L` (and it may differ from its field of constants).

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

        # we construct the base change of the underlying Berkovich line
        # to L:
        FX = self.berkovich_line().function_field()
        L = vL.domain()      # actually, this is the number field underlying L
        FXL = FunctionField(L, FX.variable_name())
        # test that FX is a subring of FXL
        assert FX.is_subring(FXL)
        # hence there is a natural coercion morphism
        XL = BerkovichLine(FXL, vL)
        # the representation of xi as a discoid on X, which is defined
        # by an inequality v(f) >= s:
        f, s = self.type_II_point().discoid()
        # the lower components correspond to the connected components of
        # the base change to L of the discoid defining the inertial component:
        f = FXL(f)
        lower_valuations = [xi.valuation() for xi in XL.points_from_inequality(f, s)]

        # some preparation:
        v0 = self.valuation()
        F0 = self.function_field()
        x0 = FXL(v0.lift(v0.residue_field().gen()))
        # x0 is a lift to FXL of the canonical coordinate on the
        # inertial component; we need it to find the natural map from the
        # lower components to the inertial component.
        k0 = F0.constant_base_field()
        theta0 = FXL(v0.lift(k0.gen()))

        # now we construct the lower components:
        lower_components = []
        for v in lower_valuations:
            F1, to_F1, _ = make_function_field(v.residue_field())
            # we need to find the correct inclusion phi of F0 into F1
            if k0.is_prime_field():
                # we don't have to worry about the right embedding of the
                # constant base field
                phi = F0.hom(to_F1(v.reduce(x0)))
            else:
                k1 = F1.constant_base_field()
                # we have to be careful about the correct embedding of k0 into k1
                phi_base = k0.hom([k1(to_F1(v.reduce(theta0)))])
                # now phi is determined by phi_base and the image of the
                # natural coordinate of F0
                phi = F0.hom(to_F1(v.reduce(x0)), phi_base)
            lower_components.append(LowerComponent(self, vL, v, phi))
        self._lower_components[u] = lower_components
        return lower_components

    def outgoing_edges(self):
        r"""
        Return the list of outgoing edges from this inertial component.

        Here an *edge* is a point on this inertial component where it intersects
        another component; so it corresponds to an edge on the Berkovich tree
        underlying the chosen inertial model. *Outgoing* is defined with respect
        to the natural orientation of the Berkovich tree.

        """
        subtree = self._subtree
        xi0 = self.type_II_point()
        outgoing_edges = []
        for child in subtree.children():
            xi1 = child.root()
            if xi1.type() == "II":
                eta = TypeVPointOnBerkovichLine(xi0, xi1)
                v = eta.minor_valuation()
                outgoing_edges.append(PointOnSmoothProjectiveCurve(self.component(), v))
        return outgoing_edges

    def outdegree(self, u=Infinity):
        r"""
        Return the outdegree of this inertial component.

        INPUT:

        - ``u`` -- an integer, or Infinity (default: ``Infinity``)

        OUTPUT: the sum of the degrees of all edges emanating from components of
        the curve `\bar{Y}^u` which lie above this inertial component.

        Here `u` is a break in the ramification filtration of splitting field
        of this inertial component, and the curve `\bar{Y}^u` is the special fiber
        of the reduction of `Y` over the corresponding subfield `L^u` (with respect
        to the given inertial model). By *edge* we mean an edge of the component
        graph of the curve `\bar{Y}^u`; it corresponds to a point in which two
        components intersect. We call an edge *outgoing* (with respect to this
        inertail component) if it lies above an edge of the component graph of
        the special fiber of the inertial model which is directed away from this
        inertial component. The *degree* of an (upper) edge is the degree of
        the corresponding point of `\bar{Y}^u`, with respect to the residue
        field of `L^u`.

        """
        ret = 0
        for z in self.outgoing_edges():
            for Xb in self.lower_components(u):
                for x in Xb.map_to_inertial_component().fiber(z):
                    assert x.curve() == Xb.component(), "x = {},\nXb={}".format(x, Xb)
                    ret += Xb.fiber_degree_in_upper_components(x)
        return ret

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

        """
        if u in self._reduction_genus.keys():
            return self._reduction_genus[u]
        else:
            self._reduction_genus[u] = sum([W.genus()*W.field_of_constants_degree()
                                            for W in self.upper_components(u)])
            return self._reduction_genus[u]

    def component_degree(self, u=Infinity):
        r"""
        Return the sum of the degrees of the upper components above this inertial
        component.

        Here the *degree* of an upper component is the degree of its field of
        constants, as extension of the constant base field.

        """
        return sum([W.field_of_constants_degree() for W in self.upper_components(u)])

    def reduction_conductor(self):
        r"""
        Return the contribution of this inertial component to the conductor exponent.

        OUTPUT: an integer `f_Z` (where `Z` is this inertial component).

        The conductor exponent `f_Y` of the curve `Y` can be written in the form

        .. MATH::

                f_Y = 1 + \sum_Z f_Z

        where `Z` runs over all inertial components of the reduction tree and
        `f_Z` is an integer, called the *contribution* of `Z` to the conductor
        exponent.

        TODO: Write better documentation.

        """
        if not hasattr(self, "_reduction_conductor"):
            L = self.splitting_field()
            n = L.ramification_degree()
            ramification_filtration = L.ramification_filtration()
            if len(ramification_filtration) == 0:
                # this inertial components split over the base field
                self._reduction_conductor = self.outdegree() - self.component_degree()
                return self._reduction_conductor

            g = self.reduction_genus()
            h = self.outdegree() - self.component_degree()
            u_0 = ramification_filtration[0][0]
            m_0 = ramification_filtration[0][1]
            g_0 = self.reduction_genus(u_0)
            h_0 = self.outdegree(u_0) - self.component_degree(u_0)
            epsilon = 2*(g - g_0) + 2*h - h_0
            delta = m_0/n*2*(g + h - g_0 - h_0)*u_0
            for i in range(1, len(ramification_filtration)):
                u = ramification_filtration[i][0]
                m_u = ramification_filtration[i][1]
                g_u = self.reduction_genus(u)
                h_u = self.outdegree(u) - self.component_degree(u)
                v = ramification_filtration[i-1][0]
                delta += m_u/n*2*(g + h - g_u - h_u)*(u - v)
            self._reduction_conductor = epsilon + delta

        return self._reduction_conductor


# -----------------------------------------------------------------------------

#                 reduction components
#                 ====================

class ReductionComponent(SageObject):
    r"""
    The superclass for the classes ``LowerComponent`` and ``UpperComponent``.

    """
    # private attributes:
    #
    # _inertial_component
    # _valuation
    # _base_valuation
    # _component
    # _to_function_field

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

    def component(self):
        r"""
        Return the normalization of this reduction component.

        """
        return self._component

    def function_field(self):
        r"""
        Return the function field of this reduction component.

        Note that the *function field* of this reduction component is the residue
        field of the corresponding valuation `v`. It must not be confused with
        the domain of `v`, which is the function field of the generic fiber.

        """
        return self.component().function_field()

    def function_field_of_generic_fiber(self):
        r""" Return the function field of the generic fiber of the model
        underlying this reduction component.

        """
        return self.valuation().domain()

    def constant_base_field(self):
        r"""
        Return the constant base field of this reduction component.

        Note that this field is isomorphic but not equal to the residue field
        of the base valuation. The isomorphism can be obtained via the
        restriction of isomorphism between the residue field of the valuation
        corresponding to the component and the function field of the component
        (can be obtained via ``self.from_residue_field()``).

        """
        return self.component().constant_base_field()

    def multiplicity(self):
        r"""
        Return the multiplicity of this reduction component.

        By definition, this is equal to the ramification index of the valuation
        corresponding to this component over the base valuation.
        """
        pi_L = self.base_valuation().uniformizer()
        pi = self.valuation().uniformizer()
        return ZZ(self.valuation()(pi_L)/self.valuation()(pi))

    def from_residue_field(self):
        r""" Return the isomorphism from the residue field of the valuation
        corresponding to this reduction component to its function field.

        """
        return self._to_function_field

    def reduce(self, f):
        r""" Return the image of a function on the generic fiber to this component.

        """
        assert self.valuation()(f) == 0, "f must be a unit of the valuation ring"
        return self.from_residue_field(self.valuation().reduce(f))

# -------------------------------------------------------------------------------


class LowerComponent(ReductionComponent):
    r"""
    Return the lower component corresponding to a given valuation.

    A *lower component* is a reduction component `Z` on the base change `X_L`
    of the Berkovich line `X` to some finite extension `L/K`. It is by construction
    the inverse image of a given inertial component `Z_0` on `X`, which is part
    of a *reduction tree*.

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
    # private attributes, from parent:
    # _inertial_component
    # _base_valuation
    # _component
    # _to_function_field

    # own private attributes:
    #
    # _inertial_component
    # _map_to_inertial_component

    def __init__(self, Z0, vL, v, phi):
        from mclf.curves.smooth_projective_curves import make_finite_field
        self._inertial_component = Z0
        self._valuation = v
        self._base_valuation = vL
        F, to_F, from_F = make_function_field(v.residue_field())
        self._to_function_field = to_F
        self._from_function_field = from_F
        k, _, _ = make_finite_field(vL.residue_field())
        # we force k to be the constant base field of the component;
        # note that we can ignore the isomorphism, because
        # - as an absolute finite field, k can be coerced into F,
        # - the embedding itself is irrelevant; only the image matters
        self._component = SmoothProjectiveCurve(F, k)
        # construct the natural morphis Z-->Z0;
        # the corresponding morphis of function fields is the given embedding
        # phi of the function field of Z0 into the residue field of v,
        # composed with the canonical isomorphism to F
        self._map_to_inertial_component = MorphismOfSmoothProjectiveCurves(
            self.component(), Z0.component(), phi.post_compose(to_F))

    def __repr__(self):
        return "lower component of reduction tree corresponding to {}".format(
            self.valuation())

    def upper_components(self):
        r"""
        Return the list of all upper components lying above this lower component.

        This lower component corresponds to a discrete valuation `v` on a rational
        function field `L(x)` extending the valuation `v_L`, where `L/K` is some
        finite extension of the base field `K`. The upper components correspond
        to the extensions of v to the function field of `Y_L` (which is a finite
        extension of `L(x)`).

        Since the computation of all extensions of a nonstandard valuation on a
        function field to a finite extension is not yet part of Sage, we have
        to appeal to the MacLane algorithm ourselves.

        EXAMPLES:

        This example shows that extending valuations also works if the equation
        is not integral wrt the valuation v ::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Y = SuperellipticCurve(5*x^3 + 1, 2)
            sage: Y2 = SemistableModel(Y, QQ.valuation(5))
            sage: Y2.is_semistable()  # indirect doctest
            True

        """
        from sage.geometry.newton_polygon import NewtonPolygon
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        v = self.valuation()
        FXL = v.domain()
        # this is the function field of X_L, on which this lower component lives
        FY = self.reduction_tree().curve().function_field()
        # this is the function field of Y;
        # we construct the function field of Y_L, on which the upper components live:
        G = FY.polynomial().change_ring(FXL)
        FYL = FXL.extension(G, FY.variable_name())
        # now FYL = FXL(y| G(y) = 0)

        # the upper components correspond to the extensions of v to FYL
        # we use the MacLane algorithm to compute them;
        # for this, we have to make G integral with respect to v
        np = NewtonPolygon([(i, v(G[i])) for i in range(G.degree() + 1)])
        r = np.slopes()[-1]   # the largest slope
        if r <= 0:      # G is integral w.r.t. v
            upper_valuations = [
                FYL.valuation(w)
                for w in v.mac_lane_approximants(FYL.polynomial(),
                                                 require_incomparability=True)]
        else:           # G is not integral
            vK = self.reduction_tree().base_valuation()
            pi = vK.uniformizer()           # we construct a function field FYL1
            k = QQ(r / v(pi)).ceil()          # isomorphic to FYL, but with
            R1 = PolynomialRing(FXL, 'y1')  # integral equation G_1
            y1 = R1.gen()
            G1 = G(pi**(-k) * y1).monic()
            assert all(v(c) >= 0 for c in G1.coefficients()), "new G is not integral!"
            FYL1 = FXL.extension(G1, 'y1')
            y1 = FYL1.gen()
            V = v.mac_lane_approximants(G1, require_incomparability=True)
            V = [FYL1.valuation(w) for w in V]   # the extensions of v to FYL1
            upper_valuations = [
                FYL.valuation((w, FYL.hom(y1 / pi**k),
                               FYL1.hom(pi**k * FYL.gen()))) for w in V]
            #                                      made into valuations on FYL
        return [UpperComponent(self, w) for w in upper_valuations]

    def map_to_inertial_component(self):
        r"""
        Return the natural map from this lower component to its inertial component.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Y = SuperellipticCurve(x^3-x, 2)
            sage: Y3 = SemistableModel(Y,QQ.valuation(3))
            sage: Z = Y3.reduction_tree().inertial_components()[0]
            sage: W = Z.lower_components()[0]
            sage: f = W.map_to_inertial_component()
            sage: f.domain()
            the smooth projective curve with Rational function field in x over Finite Field of size 3
            sage: f.codomain()
            the smooth projective curve with Rational function field in x over Finite Field of size 3

        """
        return self._map_to_inertial_component

    def fiber_degree_in_upper_components(self, P):
        r"""
        Return the sum of the absolute degrees of the points above ``P`` on
        all upper components.

        """
        assert P.curve() == self.component(), "P must be a point on this lower component"
        ret = 0
        for Yb in self.upper_components():
            ret += Yb.map_to_lower_component().fiber_degree(P)
        return ret

# ------------------------------------------------------------------------------


class UpperComponent(ReductionComponent):
    r"""
    Return the upper component above this lower component,
    corresponding to a given valuation.

    INPUT:

    - ``Z`` -- a lower component of a reduction tree `Y`
    - ``v`` -- a discrete valuation on the base extension to `L` of the function
      field `F_Y`, extending the valuation corresponding to `Z`

    OUTPUT: The upper component above `Z` corresponding to `v`.

    Note that the constant base fields of the upper and the lower components
    are equal, by definition, and isomorphic to the residue field of `L`.

    """
    # private attributes, from parent:
    #
    # _inertial_component
    # _valuation
    # _base_valuation
    # _component
    # _to_function_field
    #
    # own private attributes:
    #
    # _lower_component
    # _map_to_lower_component

    def __init__(self, Z, v):

        self._inertial_component = Z.inertial_component()
        self._lower_component = Z
        self._base_valuation = Z.base_valuation()
        self._valuation = v
        F, to_F, _ = make_function_field(v.residue_field())
        self._component = SmoothProjectiveCurve(F, Z.constant_base_field())
        # we have to construct the embedding of the function field of Z into
        # the function field of W (this component), which gives rise to the
        # natural map W-->Z. The defining property of this embedding is its
        # compatibility with the canonical embedding of FXL into FYL
        v0 = Z.valuation()
        F0 = Z.function_field()
        # we need the isomorphism between the residue field of v0 and F0:
        from_F0 = Z._from_function_field
        # we have to find an element x0 in F which reduces to the generator
        # of F0
        x0 = to_F(v.reduce(v0.lift(from_F0(F0.gen()))))
        # we also have to define the right map between the constant base fields
        k0 = F0.constant_base_field()  # note: this may not the equal to the
        #                                constant base field of Z
        k = F.constant_base_field()    # and this may not be equal to the cbf of W
        if k0.is_prime_field():
            # there is no choice; we can take the identity on k0:
            phi_base = k0.hom(k0)
        else:
            # we have to find the element in k to which a generator
            # of k0 has to be mapped
            alpha = to_F(v.reduce((v0.lift(from_F0(k0.gen())))))
            phi_base = k0.hom(alpha, k)
        phi = F0.hom(x0, phi_base)
        self._map_to_lower_component = MorphismOfSmoothProjectiveCurves(
            self._component, Z.component(), phi)

    def __repr__(self):
        return "upper component of reduction tree corresponding to  {}".format(self.valuation())

    def genus(self):
        r"""
        Return the genus of this upper reduction component.

        """
        return self.component().genus()

    def field_of_constants_degree(self):
        r"""
        Return the degree of the field of constants over the constant base field
        of this upper reduction component.

        """
        return self.component().field_of_constants_degree()

    def lower_component(self):
        r"""
        Return the lower component underneath this upper component.
        """
        return self._lower_component

    def map_to_lower_component(self):
        r"""
        Return the natural map from this upper component to the lower component beneath.

        """
        return self._map_to_lower_component

#
# -----------------------------------------------------------------------------

#                       auxiliary functions
#                       -------------------
#


def make_function_field(K):
    r"""
    Return the function field isomorphic to this field, an isomorphism,
    and its inverse.

    INPUT:

    - ``K`` -- a field

    OUTPUT: A triple `(F,\phi,\psi)`, where `F` is a rational function field,
    `\phi:K\to F` is a field isomorphism and `\psi` the inverse of `\phi`.

    It is assumed that `K` is either the fraction field of a polynomial ring
    over a finite field `k`, or a finite simple extension of such a field.

    In the first case, `F=k_1(x)` is a rational function field over a finite
    field `k_1`, where `k_1` as an *absolute* finite field isomorphic to `k`.
    In the second case, `F` is a finite simple extension of a rational function
    field as in the first case.

    .. NOTE::

        this command seems to be partly superfluous by now, because the residue
        of a valuation is already of type "function field" whenever this makes sense.
        However, even if `K` is a function field over a finite field, it is not
        guaranteed that the constant base field is a 'true' finite field, and then
        it is important to change that.

    """
    from mclf.curves.smooth_projective_curves import make_finite_field
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    from sage.categories.function_fields import FunctionFields
    from sage.rings.function_field.function_field import is_FunctionField

    if is_FunctionField(K):
        k = K.constant_base_field()
        if k.is_finite() and hasattr(k, "base_field"):
            # k seems to be finite, but not a true finite field
            # we construct a true finite field k1 isomorphic to k
            # and F isomorphic to K with constant base field k1
            k1, phi, psi = make_finite_field(k)
            if hasattr(K, "polynomial"):
                # K is an extension of a rational function field
                K0 = K.rational_function_field()
                F0, phi0, psi0 = make_function_field(K0)
                f = K.polynomial().change_ring(phi0)
                F = F0.extension(f)
                return F, K.hom(F.gen(), phi0), F.hom(K.gen(), psi0)
            else:
                F = FunctionField(k1, K.variable_name())
                return F, K.hom(F.gen(), phi), F.hom(K.gen(), psi)
        else:
            return K, K.Hom(K).identity(), K.Hom(K).identity()

    if hasattr(K, "modulus") or hasattr(K, "polynomial"):
        # we hope that K is a simple finite extension of a field which is
        # isomorphic to a rational function field
        K_base = K.base_field()
        F_base, phi_base, psi_base = make_function_field(K_base)
        if hasattr(K, "modulus"):
            G = K.modulus()
        else:
            G = K.polynomial()
        R = G.parent()
        R_new = PolynomialRing(F_base, R.variable_name())
        G_new = R_new([phi_base(c) for c in G.list()])
        assert G_new.is_irreducible(), "G must be irreducible!"
        # F = F_base.extension(G_new, R.variable_name())
        F = F_base.extension(G_new, 'y')
        # phi0 = R.hom(F.gen(), F)
        # to construct phi:K=K_0[x]/(G) --> F=F_0[y]/(G),
        # we first 'map' from K to K_0[x]
        phi = K.hom(R.gen(), R, check=False)
        # then from K_0[x] to F_0[y]
        psi = R.hom(phi_base, R_new)
        # then from F_0[y] to F = F_0[y]/(G)
        phi = phi.post_compose(psi.post_compose(R_new.hom(F.gen(), F)))
        psi = F.hom(K.gen(), psi_base)
        return F, phi, psi
    else:
        # we hope that K is isomorphic to a rational function field over a
        # finite field
        if K in FunctionFields():
            # K is already a function field
            k = K.constant_base_field()
            k_new, phi_base, psi_base = make_finite_field(k)
            F = FunctionField(k_new, K.variable_name())
            phi = K.hom(F.gen(), phi_base)
            psi = F.hom(K.gen(), psi_base)
            return F, phi, psi
        elif hasattr(K, "function_field"):
            F1 = K.function_field()
            phi1 = F1.coerce_map_from(K)
            psi1 = F1.hom(K.gen())
            F, phi2, psi2 = make_function_field(F1)
            phi = phi1.post_compose(phi2)
            psi = psi2.post_compose(psi1)
            return F, phi, psi
        else:
            raise NotImplementedError
