r""" Affinoid subdomains of the Berkovich line.
===============================================

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `X=\mathbb{P}^1_K`
be the projective line over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. We call `X^{an}` the **Berkovich
line** over `K`.

In this file we realize a Sage class which allows us to create and work with
strictly affinoid subdomains of `X^{an}`.

Let `T` be a Berkovich tree in `X^{an}` and let `r:T\to X^{an}` denote the
canonical retraction map. Let `S` be a nonempty proper subset of `V(T)`.
We define `\bar{S}` as the union of `S` and of all edges connecting two points
of `S`. Then the inverse image `U:=r^{-1}(\bar{S})` is an affinoid subdomain of
`X^{an}`. We use the notation `U=U(T,S)`.

We say that a Berkovich tree `T` *supports* an affinoid domain `U` if there
exists a nonempty proper subset `S` of `V(T)` with `U=U(T,S)`. If this is the
case then `S` consists exactly of the vertices of `T` which lie in `U`.

Given any affinoid domain `U`, there exists a unique minimal tree `T` which
supports `U`. Moreover, every tree `T'` which contracts to `T'` supports `U`
as well.


AUTHORS:

- Stefan Wewers (2017-07-29): initial version


EXAMPLES::

<Lots and lots of examples>



TO DO:

- more doctests

- improve performance; many algorithms can be replaced by more efficient ones

- add missing functions: intersection, ..

- allow empty affinoids, and do something about the case where `U=X`


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


from sage.all import SageObject, Infinity
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
from mclf.berkovich.berkovich_trees import BerkovichTree


class AffinoidTree(BerkovichTree):
    r""" A marked Berkovich tree representing an affinoid subdomain.

    An AffinoidTree is a Berkovich tree `T` in which every vertex has an additional
    flag "is_in" with value ``True`` or ``False``. It represents an
    affinoid subdomain `U` in the way explained above.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``root`` -- a point on ``X`` or None (default = None)
    - ``children`` -- a list of affinoid trees or None (default = None)
    - ``parent`` -- an affinoid tree or none (default = None)
    - ``is_in`` -- a boolean or None (default = None)

    OUTPUT:

    An affinoid tree on ``X``. It is either empty (if only ``X`` is given) or
    it has root, parent, children and the flag ``is_in`` as given
    by the extra parameters.

    EXAMPLES::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: xi0 = X.gauss_point()
        sage: xi1 = X.point_from_discoid(x^2+2, 3/2)
        sage: xi2 = X.point_from_discoid(x^4+2, 3/2)
        sage: xi3 = X.point_from_discoid(x^2+x+1, 1)
        sage: xi4 = X.point_from_discoid(x^2+2, 1)

        sage: U1 = AffinoidTree(X)
        sage: U1 = U1.add_points([xi0], [xi1, xi3])
        sage: U2 = AffinoidTree(X)
        sage: U2 = U2.add_points([xi2], [xi4])

        sage: U = U1.union(U2)
        sage: U
        Affinoid tree with 6 vertices
    """

    def __init__(self, X, root=None, children=None, parent=None, is_in=False):
        self._X = X
        if root is None:
            self._root = None
            self._children = []
            self._parent = None
            self._is_in = False
            # Now we have an empty affinoid tree
        else:
            assert root.type() in ["I", "II"], "root must be a point of type I or II"
            self._root = root
            self._parent = parent
            if children is None:
                self._children = []
            else:
                self._children = children
            self._is_in = is_in

    def __repr__(self):
        return "Affinoid tree with {} vertices".format(len(self.vertices()))

    def _check_for_parents(self):
        r"""
        Check if parents are set correctly. For debugging only!

        """
        T0 = self
        for T1 in T0.children():
            assert T1.parent() is T0
            T1._check_for_parents()

    def copy(self, parent=None):
        """
        Return a copy of self, force ``parent`` as parent.

        WARNING! something is wrong with this function!!

        """

        T = self
        T_new = AffinoidTree(T._X, T.root(), [], parent, T._is_in)
        children = [T1.copy(T_new) for T1 in T.children()]
        T_new._children = children
        return T_new

    def is_empty_set(self):
        r""" Return whether this tree represents the empty set.

        """
        return not self.root_is_in() and all([child.is_empty_set()
                                              for child in self.children()])

    def root_is_in(self):
        r""" Return whether the root of ``self`` lies in the affinoid.
        """
        return self._is_in

    def is_in(self, xi):
        r""" Return True if ``xi`` lies in the affinoid  `U` represented by ``self``.

        INPUT:

        - ``xi`` -- a point on the Berekovich space underlying this affinoid tree

        Note that `\xi` may also be a point of type V.

        To test this, we compute the image of xi under the retraction map
        onto the total space of T=self and check whether it lies on a vertex
        in U or on an edge connecting two vertices in U.

        """
        if xi.type() == "V":
            eta = xi
            xi = eta.boundary_point()
            is_type_V = True
        else:
            is_type_V = False
        xi1, T1, T2, is_vertex = self.position(xi)
        # xi1 is the image of xi under the retraction map onto the total
        # space of T=self. If is_vertex==True then xi1 is the root of T1.
        # Otherwise, xi1 lies on the edge connecting the roots of T1 and T2.
        if is_vertex:
            if not is_type_V:
                return T1.root_is_in()
            else:
                if not T1.root_is_in():
                    return False
                # return False if there is one child or parent whose root is an out-point
                # lying in the residue class of eta
                if (T1.has_parent() and eta.is_in_residue_class(T1.parent().root())
                        and not T1.parent().root_is_in()):
                    return False
                return all([child.root_is_in()
                            or not eta.is_in_residue_class(child.root()) for child in T1.children()])
        else:
            return T1._is_in and T2._is_in

    def minimal_points(self, xi0=None):
        r""" Return the minimal points of the affinoid corresponding to this tree.

        INPUT:

        - ``xi0`` -- a point of type II or V, or ``None`` (default ``None``)

        OUTPUT: the list of all minimal points of the affinoid corresponding to
        this tree, which are `\geq \xi_0`. If `\xi_0` is not given, this condition
        is ignored.

        Note that `\xi_0` may be of type V.

        """
        T = self
        if T.root_is_in() and (xi0 is None or xi0.is_leq(T.root())):
            return [T.root()]
        else:
            minimal_points = []
            for child in T.children():
                minimal_points += child.minimal_points(xi0)
            return minimal_points

    def intersection_with_unit_disk(self):
        r""" Return the tree representing the intersection with the unit disk.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        T = self.copy()
        X = T.berkovich_line()
        eta = TypeVPointOnBerkovichLine(X.gauss_point(), X.infty())
        children = T.children()
        for child in children:
            if eta.is_in_residue_class(child.root()):
                T.remove_child(child)
        if T.root_is_in():
            T1 = AffinoidTree(X, root=X.infty(), is_in=False)
            T.make_child(T1)
        return T

    def simplify(self):
        r"""
        Simplify this tree without changing the represented affinoid.

        """
        T = self
        if T.root_is_in():
            # so far we only try to remove unnecessary in-points
            children = T.children()[:]
            # this is a shallow copy; this is necessary because the actual
            # children of T may be changed during the following loop
            for T1 in children:
                if T1.root_is_in() and len(T1.children()) == 0:
                    T.remove_child(T1)
                elif T1.root_is_in() and len(T1.children()) == 1:
                    T2 = T1.children()[0]
                    if T2.root_is_in():
                        # we can replace T1 by T2
                        T.remove_child(T1)
                        T.make_child(T2)
        for T1 in T.children():
            T1.simplify()

    def show(self):
        r""" Display a graphical representation of self.

        """
        G, vertex_dict = self.graph()
        in_list = []
        out_list = []
        for i, xi in vertex_dict.items():
            if self.is_in(xi):
                in_list.append(i)
            else:
                out_list.append(i)
            print(i, ": ", xi)
        # print(vertex_dict)
        G.show(partition=[in_list, out_list])

    def holes(self, upward_hole=True):
        r""" Return the holes of this affinoid tree.

        OUTPUT: a list of triples `(T_1, T_2, \eta)`, where `T_1`, `T_2` are
        subtrees of ``self`` and `\eta` is a point of type V, satisfying the
        following conditions:
        - `T_2` is a child of `T_1`, or vice versa
        - the root of `T_1` is a boundary point of the affinoid underlying ``self``
        - the root of `T_2` does not lie in the affinoid
        - `\eta` is the direction from the root of `T_1` to the root of `T_2`
        This implies that `\eta` is a *hole* of the affinoid represented by ``self``.

        """
        T = self
        holes = []
        if T.root_is_in():
            if upward_hole and T.has_parent() and not T.parent().root_is_in():
                eta = T.direction_to_parent()
                holes.append((T, T.parent(), eta))
            for child in T.children():
                if not child.root_is_in():
                    eta = child.direction_from_parent()
                    holes.append((T, child, eta))
        for child in T.children():
            holes += child.holes(upward_hole)
        return holes

    def connected_components(self, xi0=None):
        r""" Return a list of affinoid trees representing the connected
        components below a given point.

        INPUT:

        - ``xi0`` -- a point of type II or V

        OUTPUT: a list of affinid trees representing the connected components
        of the affinoid corresponding to this tree, which are `\geq` to the
        given point `\xi_0`. If it is not given, then we ignore
        this condition.

        Note that `\xi_0` may be of type V.

        """
        T = self
        X = T.berkovich_line()
        if hasattr(T, "_components"):
            return T._components

        minimal_points = T.minimal_points(xi0)
        components = []
        for xi1 in minimal_points:
            T1 = T.find_point(xi1)
            # T1 is the subtree of T with root xi1
            T2 = _connected_component_tree(T1)
            if T1.has_parent() and not T1.parent().root_is_in():
                new_component = AffinoidTree(X, root=T1.parent().root(), is_in=False)
                new_component.make_child(T1)
            else:
                new_component = T2
            components.append(new_component)
        new_components = []
        for T1 in components:
            holes = T1.holes(upward_hole=False)
            for _, _, eta in holes:
                new_components += T.connected_components(eta)
                # changed !
        return components + new_components

    def compute_connected_components(self, comp_list, new_comp):
        r""" Compute the connected components of the represented affinoid.

        INPUT:

        - ``comp_list`` -- a list (of lists of lists)
        - ``new_comp`` -- a list (of lists)

        OUTPUT:

        - all connected components whose root is a vertex of T=``self`` are
          added to the list ``comp_list``.
        - all boundary_lists which belong to T and to the connected component
          which contains the root of T  are added to ``new_comp`` (in particular,
          if the root of T does not lie in the affinoid then the list is unchanged).

        Here a *boundary list* is a list of type-V-points which represent holes
        of the affinoid with a common boundary point. A *connected component*
        is a list of boundary lists.

        EXAMPLES::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi0 = X.gauss_point()
            sage: xi1 = X.point_from_discoid(x+1, 1)
            sage: xi2 = X.point_from_discoid(x+1, 2)
            sage: xi3 = X.point_from_discoid(1/x, 1)

            sage: U = AffinoidTree(X)
            sage: U = U.add_points([xi0, xi2], [xi1, xi3])
            sage: U
            Affinoid tree with 4 vertices

            sage: component_list = []
            sage: U.compute_connected_components(component_list, [])
            sage: component_list
            [[[Point of type V given by residue class v(1/(x + 1)) > -2]],
            [[Point of type V given by residue class v(x + 1) > 0,
            Point of type V given by residue class v(1/x) > 0]]]

        """
        T = self
        if T._is_in:
            if T.parent() is None or T.parent()._is_in:
                holes = []
            else:
                # possible source of error: root of T is of type I
                holes = [TypeVPointOnBerkovichLine(T.root(), T.parent().root())]
            for T1 in T.children():
                if T1._is_in:
                    T1.compute_connected_components(comp_list, new_comp)
                else:
                    holes.append(TypeVPointOnBerkovichLine(T.root(), T1.root()))
                    T1.compute_connected_components(comp_list, [])
            if holes != []:
                new_comp.append(holes)

            if T.parent() is None or not T.parent()._is_in:
                # T.root() is the root of a component
                comp_list.append(new_comp)
        else:
            # the root of T does not lie in U
            for T1 in T.children():
                T1.compute_connected_components(comp_list, [])


def _connected_component_tree(T):
    r""" Return an affinoid tree corresponding to the leading connected component
    of the affinoid represented by ``T``.

    INPUT:

    - ``T`` -- an affinoid tree

    OUTPUT: a new affinoid tree `T_1` representing a connected affinoid domain
    whose minimal point is the root of `T`. This means that the out-points of
    `T_1` are precisely the leaves of `T_1`.

    If the root of `T` is an out-point, then `T_1` consists of a single out-point,
    and thus represents an empty affinoid.

    If the root of `T` is an in-point then then `T_1` has the same root as `T`,
    and its children are computed by applying ``_connected_component_tree`` to
    the children of `T`.

    This is a helper function for
    ``AffinoidDomainOnBerkovichLine.connected_component_tree``

    """
    X = T.berkovich_line()
    if T.root_is_in():
        T1 = AffinoidTree(X, root=T.root(), is_in=True)
        for child in T.children():
            T1.make_child(_connected_component_tree(child), check=True)
    else:
        T1 = AffinoidTree(X, root=T.root(), is_in=False)
    return T1


class AffinoidDomainOnBerkovichLine(SageObject):
    r"""
    The class realizing affinoid domains on a Berkovich line.

    EXAMPLES::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: U1 = RationalDomainOnBerkovichLine(X, 2*(x^2+2)/(x+1))
        sage: U2 = RationalDomainOnBerkovichLine(X, x/(x+3))
        sage: U = U1.union(U2)
        sage: U
        Affinoid with 1 components:
        Elementary affinoid defined by
        v(1/(x + 1)) >= -1


    TO DO:

    - ..

    """

    def __init__(self, T):
        r""" Return the affinoid domain corresponding to the affinoid tree ``T``.

        INPUT:

        - T -- an affinoid tree

        OUTPUT:

        the affinoid corresponding to ``T``

        """
        self._X = T._X
        self._T = T

    def __repr__(self):
        if self.is_empty():
            return "The empty set"
        elif self.is_full_berkovich_line():
            return "the full berkovich line"
        elif self.number_of_components() == 1:
            return str(self.components()[0])
        else:
            comp_str = ""
            for U in self.components():
                comp_str += str(U)
            return "Affinoid with {} components:\n{}".format(self.number_of_components(),
                                                             comp_str)

    def berkovich_line(self):
        return self._X

    def is_empty(self):
        return self.number_of_components() == 0

    def is_full_berkovich_line(self):
        return (self.number_of_components() == 1
                and self.components()[0].is_full_berkovich_line())

    def tree(self):
        if hasattr(self, "_T"):
            return self._T
        else:
            xi0 = self.berkovich_line().gauss_point()
            self._T = self.affinoid_subtree(xi0)
            self._T.simplify()
            return self._T

    def is_in(self, xi):
        r"""
        Check whether ``x`` lies on the affinoid.

        INPUT:

        - ``xi`` -- a point of type I, II or V

        OUTPUT:

        ``True`` if ``xi`` lies on the affinoid, ``False`` otherwise

        """
        return self.tree().is_in(xi)

    def components(self):
        if not hasattr(self, "_components"):
            components = []
            for T in self.tree().connected_components():
                components.append(ElementaryAffinoidOnBerkovichLine(T))
            self._components = components
        return self._components

    def number_of_components(self):
        return len(self.components())

    def boundary(self):
        r"""
        Return the Shilov boundary of the affinoid.

        The Shilov boundary is a finite set of type-II-points contained in the
        affinoid with the property that the valuative function of every rational
        function which is regular on the affinoid takes a minimum on this set.

        The Shilov boundary is simply the union of the boundaries of the
        connected components.

        """
        if not hasattr(self, "_boundary"):
            boundary = []
            for V in self.components():
                boundary += V.boundary()
            self._boundary = boundary
        return self._boundary

    def simplify(self):
        r""" Simplify this affinoid.

        This only changes the internal representation by an "affinoid tree".
        Very likely, this is unnecessary because the simplification has already
        occured when the affinoid was first constructed.

        """
        self._T = self.tree().simplify()

    def union(self, V):
        r"""
        Return the affinoid which is the union of ``self`` with ``V``.

        This is now obsolete.
        """

        T = self.tree().union(V.tree())
        return AffinoidDomainOnBerkovichLine(T)

    def intersection(self, V):
        r"""
        Return the affinoid which is the intersection of ``self`` with ``V``.

        This is now obsolete.
        """
        T = self.tree().intersection(V.tree())
        return AffinoidDomainOnBerkovichLine(T)

    def intersection_with_unit_disk(self):
        r""" Return the intersection of this affinoid with the unit disk.

        """
        T = self.tree().intersection_with_unit_disk()
        return AffinoidDomainOnBerkovichLine(T)

    def point_close_to_boundary(self, xi0):
        r"""
        Return a type-I-point inside the affinoid, close to ``xi0``.

        INPUT:

        - ``xi0`` -- a boundary point of the affinoid ``self``

        OUTPUT: a type-I-point ``xi1`` on the affinoid `U:=` ``self`` which
        is "close" to the boundary point ``xi0``.

        The latter means that ``xi1`` maps onto the irreducible components
        of the canonical reduction of `U` corresponding to ``xi0``.

        EXAMPLES::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: U = RationalDomainOnBerkovichLine(X, 2/x/(x+1))
            sage: U
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(1/x) >= -1
            v(1/(x + 1)) >= -1
            sage: xi0 = U.boundary()[0]
            sage: U.point_close_to_boundary(xi0)
            Point of type I on Berkovich line given by x + 2 = 0

        At the moment, our choice of point close to the boundary is not
        optimal, as the following example shows: ::

            sage: U = RationalDomainOnBerkovichLine(X, 2/(x^2+x+1))
            sage: U
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(1/(x^2 + x + 1)) >= -1

            sage: xi0 = U.boundary()[0]
            sage: U.point_close_to_boundary(xi0)
            Point of type I on Berkovich line given by x^2 + 3*x + 1 = 0

        The point at infinity is also inside U and 'close to the boundary',
        and has smaller degree than the point produced above.

        There is the following bug: ::

            sage: f = (-2/25*x^6 - 4*x^5 - 1351/225*x^4 - 52/225*x^3 - 173/225*x^2 - 2/9*x + 2/3)/(x^2 + 2/3*x)
            sage: h = valuative_function(D, f)
            sage: U = h.affinoid_domain()
            sage: U

            sage U.point_close_to_boundary(U.boundary()[1])

        .. TODO::

            - Use a better strategie to find a point of minimal degree.
            - fix the bug

        """
        U = self
        T = U.tree()
        X = U.berkovich_line()
        F = X.function_field()
        x = F.gen()
        T0 = T.find_point(xi0)
        assert T0 is not None and T0._is_in, "xi0 is not a boundary point"
        # we only look for point of type I which are larger than xi0
        # but it may be possibleto find other points with smaller degree
        v0 = xi0.pseudovaluation_on_polynomial_ring()
        Rb = v0.residue_ring()
        psi = Rb.one()
        for T1 in T0.children():
            if not T1._is_in:
                eta1 = TypeVPointOnBerkovichLine(xi0, T1.root())
                psi1 = eta1.minor_valuation().uniformizer()
                if psi1.denominator().is_one():
                    psi = psi * Rb(psi1.numerator())
        phib = irreducible_polynomial_prime_to(psi)
        phi = v0.lift_to_key(phib)
        if xi0.is_in_unit_disk():
            xi1 = X.point_from_discoid(phi, Infinity)
        else:
            if phi == x:
                xi1 = X.point_from_discoid(1/x, Infinity)
            else:
                xi1 = X.point_from_discoid(phi(1/x)*x**phi.degree(), Infinity)
        assert U.is_in(xi1), "error: xi1 is not contained in U"
        return xi1

    def affinoid_subtree(self, xi0, is_in=None):
        r""" Return the affinoid subtree with given root.

        This function is used inductively to construct a tree representing the
        affinoid `U`, if such a tree is not explicitly given, and the affinoid is
        defined in some other way (as a rational domain, or as a union of other
        affinoid domains,..).

        INPUT:

        - ``xi0`` - a point of type II
        - ``is_in`` -- a boolean, or ``None`` (default ``None``)

        OUTPUT: an affinoid tree with root `\xi0` which represents the
        intersection of `U` with `D_{\xi_0}`, the set of points `\geq \xi_0`
        (a closed discoid with boundary point `\xi_0`, or the full Berkovich
        line if `xi_0` is the Gauss point).

        If ``is_in`` is given, we assume it is equal to the truth value of
        "`\xi_0` lies in this affinoid". This is useful to avoid an extra test
        for membership.

        """
        from mclf.berkovich.berkovich_trees import replace_subtree
        U = self
        if is_in is None:
            is_in = U.is_in(xi0)
        if is_in:
            # we find the connected component of U\cap D_xi0
            T = U.connected_component_tree(xi0)
            # in every hole < xi0 we have to see if there are more components of U
            for T1, T2, eta in T.holes(upward_hole=False):
                # T1 is a subtree of T with child T2 and eta is the
                # direction from T1 to T2; eta does not lie in U
                T3 = U.affinoid_subtree_in_hole(eta)
                # T3 is an affinoid tree with the same root as T1 such that
                # all children lie in the direction of eta
                if not T3.is_empty_set():
                    # replace the hole (T1, T2) by T3
                    T1.remove_child(T2)
                    for new_child in T3.children():
                        T1.make_child(new_child, check=True)
            return T
        else:
            # xi0 is not in the affinoid U; we first look for all minimal points
            # of U  which are greater than xi0. Each such point is a
            # boundary point of an irreducible component of U
            # In any case, the tree we return will have xi0, or the boundary
            # of xi0, as root.
            X = self.berkovich_line()
            minimal_points = U.minimal_points(xi0)
            if len(minimal_points) == 0:
                # we give back a tree representing the empty set
                return AffinoidTree(X, root=xi0, is_in=False)
            else:
                # we construct an affinoid tree T with root xi0 whose leaves are
                # the minimal points, which are precisely the in-points of T0
                T1 = _make_affinoid_tree_with_in_leaves(X, minimal_points)
                if xi0.is_strictly_less(T1.root()):
                    T = AffinoidTree(X, root=xi0, is_in=False)
                    T.make_child(T1)
                else:
                    T = T1
                # now we replace the leaves by the subtrees defined by U
                for T1 in T.leaves(subtrees=True):
                    T2 = U.affinoid_subtree(T1.root(), is_in=True)
                    replace_subtree(T1, T2)
                return T

    def affinoid_subtree_in_hole(self, eta):
        r""" Return the affinoid subtree with given root.

        This is a helper function for ``affinoid_subtree``.

        INPUT:

        - ``eta`` - a point of type V

        OUTPUT: We assume that `\eta` represents a downward hole of this
        affinoid `U`. This means that the boundary point of `\eta` lies in `U`
        but `\eta` does not. We return an affinoid tree `T` whose root is the
        boundary point of `\eta`, representing the affinoid

        .. MATH::

            (X\backslash D_\eta)\cup (D_\eta\cap U)`.

        """
        from mclf.berkovich.berkovich_trees import replace_subtree
        U = self
        X = U.berkovich_line()
        xi0 = eta.boundary_point()
        # we find the minimal points of U inside the open discoid D_eta
        minimal_points = U.minimal_points(eta)
        if minimal_points == []:
            # we give back a tree representing a hole
            xi1 = eta.point_inside_residue_class()
            T1 = AffinoidTree(X, root=xi1, is_in=False)
            T = AffinoidTree(X, root=xi0, is_in=True)
            T.make_child(T1)
            return T
        else:
            # we construct an affinoid tree T whose leaves are the minimal points,
            # which are also precisely the in-points; the root is the supremum
            # of the leaves
            T1 = _make_affinoid_tree_with_in_leaves(X, minimal_points)
            # the tree T we want to return must have root xi0, as in-point
            T = AffinoidTree(X, root=xi0, is_in=True)
            # we have to `merge` it with T1
            xi1 = T1.root()
            assert xi0.is_leq(xi1), "something is wrong!"
            if xi1.is_leq(xi0):
                # the supremum of the minimal points is xi_0
                # the children of T1 correspond to the children of T, but we may
                # have to insert an out-point
                for T2 in T1.children():
                    if T2.root_is_in():
                        # we have to insert an out-point
                        xi3 = xi0.point_in_between(T2.root())
                        T3 = AffinoidTree(X, root=xi3, is_in=False)
                        T3.make_child(T2)
                        T.make_child(T3)
                    else:
                        T.make_child(T2)
            else:
                # the root of T1 is strictly larger than xi0
                if T1.root_is_in():
                    # T1 seems to consist of the single in-point xi1; we have to
                    # insert an out_point
                    assert len(T1.children()) == 0, "something is wrong!"
                    xi2 = xi0.point_in_between(xi1)
                    T2 = AffinoidTree(X, root=xi2, is_in=False)
                    T2.make_child(T1)
                    T.make_child(T2)
                else:
                    T.make_child(T1)
            # now we have to replace the leaves of T by the trees corresponding
            # to the corresponding portions of U
            for leaf in T.leaves(subtrees=True):
                new_subtree = U.affinoid_subtree(leaf.root(), is_in=True)
                replace_subtree(leaf, new_subtree)
            return T

    def connected_component_tree(self, xi0):
        r""" Return the tree of the connected component of this affinoid with given root.

        INPUT:

        - ``xi0`` -- a point type II or V

        OUTPUT: if `\xi_0` is a point of type II, then we return an affinoid tree
        underlying the connected component of this affinoid `U` with minimal
        point `\xi_0`.

        It is assumed but not checked that `\xi_0` lies in this affinoid.

        If `\xi_0` is of type V then we return the branch of this tree in the
        direction of `\xi_0`. This has the effect of "filling in all holes"
        which do not lie in the open discoid `D_{\xi_0}`. It does *not*
        correspond to the intersection with `D_{\xi_0}`.

        Note::

        This is the generic algorithm for the parent class
        ``AffinoidDomainOnBerkovichLine``. It is assumed that the underlying
        affinoid tree has already been computed. Otherwise we run into an
        infinite loop.

        """
        U = self
        assert U.is_in(xi0), "xi0 must lie in U: xi0 = {}".format(xi0)
        X = U.berkovich_line()
        T = U.tree()
        if xi0.type() == "V":
            is_type_V = True
            eta = xi0
            xi0 = eta.boundary_point()
        else:
            is_type_V = False
        xi1, T0, T1, is_vertex = T.position(xi0)
        if not xi0.is_equal(xi1):
            # xi0 does not lie on the tree T; this means that every point > xi0
            # are contained in U
            return AffinoidTree(X, root=xi0, is_in=True)
        # now xi0 lies on the tree
        if not is_vertex:
            # xi0 lies strictly on the path from T0 to T1
            T_new = AffinoidTree(X, root=xi0, is_in=True)
            T_new.make_child(_connected_component_tree(T1))
            T1 = T_new
        # now xi0 is the vertex of T1
        if is_type_V:
            T_new = AffinoidTree(X, root=xi0, is_in=True)
            for T2 in T1.children():
                if not eta.is_in_residue_class(T2.root()):
                    continue
                T3 = _connected_component_tree(T2)
                T_new.make_child(T3, check=True)
            return T_new
        # now xi0 is the root of T1, and is of type I or II
        T = _connected_component_tree(T1)
        return T

    def minimal_points(self, xi0=None):
        r""" Return the minimal points of this affinoid greater than a given point.

        INPUT:

        - ``xi0`` -- a point of type II, or ``None`` (default ``None``)

        OUTPUT: the list of all minimal points of this affinoid which are
        `\geq \xi_0`.

        """
        return self.tree().minimal_points(xi0)


class UnionOfDomains(AffinoidDomainOnBerkovichLine):
    r""" Return the union of a list of affinoid domains.

    INPUT:

    - ``affinoid_list`` - a nonempty list of affinoid domains

    OUTPUT: the union of the affinoid domains in ``affinoid_list``

    """

    def __init__(self, affinoid_list):

        assert affinoid_list, "the list must not be empty"
        self._X = affinoid_list[0].berkovich_line()
        self._affinoid_list = affinoid_list

    def is_in(self, xi):
        r""" Return whether ``xi`` lies in this affinoid.

        INPUT:

        - ``xi`` -- a point on the Berkovich line (type V points are allowed)

        OUTPUT: ``True`` if `\xi` lies on this affinoid.

        """
        for U in self._affinoid_list:
            if U.is_in(xi):
                return True
        return False

    def connected_component_tree(self, xi0):
        r""" Return the tree of the connected component of this affinoid with given root.

        INPUT:

        - ``xi0`` -- a point type II or V

        OUTPUT: if `\xi_0` is a point of type II, then we return an affinoid tree
        underlying the connected component of this affinoid `U` with minimal
        point `\xi_0`.

        It is assumed but not checked that ``\xi_0` is a minimal point of a
        connected component of `U`.

        If `\xi_0` is of type V then we return the branch of this tree in the
        direction of `\xi_0`. This has the effect of "filling in all holes"
        which do not lie in the open discoid `D_{\xi_0}`. It does *not*
        correspond to the intersection with `D_{\xi_0}`.

        """
        from mclf.berkovich.berkovich_trees import replace_subtree
        U = self
        affinoid_list = U._affinoid_list
        # by assumption, xi0 lies in U, so it has to lie in one of the U_i
        # we put this one at the beginning of the list
        for i in range(len(affinoid_list)):
            if affinoid_list[i].is_in(xi0):
                break
        affinoid_list = [affinoid_list[i]] + affinoid_list[:i] + affinoid_list[i+1:]
        T = affinoid_list[0].connected_component_tree(xi0)
        # this returns the empty set if xi0 is an out-point of U_1, but
        # if T represents the empty set, then nothing happens; this is wrong
        for V in affinoid_list[1:]:
            for T1, T2, eta in T.holes(upward_hole=False):
                # we have T1 < T2
                if not(T == T1 or T1.has_parent()):
                    # T1 isn't a subtree of T anymore, so we can omit this run
                    # of the loop; this is kind of dangerous, but so far it works
                    continue
                if V.is_in(eta):
                    T3 = V.connected_component_tree(eta)
                    if T == T1:
                        # the root of T and T3 are the same
                        # we remove T2
                        T.remove_child(T2)
                        # and replace it with all children of T3
                        for child in T3.children():
                            assert eta.is_in_residue_class(child.root()), "error!"
                            T.make_child(child)
                    else:
                        # now T1 should be a proper subtree of T and hence
                        # have a parent
                        replace_subtree(T1, T3)   # error if T1 has no parent
        return T

    def minimal_points(self, xi0=None):
        r""" Return the minimal points of this affinoid greater than a given point.

        INPUT:

        - ``xi0`` -- a point of type II, or ``None`` (default ``None``)

        OUTPUT: the list of all minimal points of this affinoid which are
        `\geq \xi_0`.

        """
        U = self
        affinoid_list = U._affinoid_list
        minimal_points = affinoid_list[0].minimal_points(xi0)
        for V in affinoid_list[1:]:
            new_points = V.minimal_points(xi0)
            for xi1 in new_points:
                # we see if we can replace an element of `minimal_points`
                # by xi1, or if we can add xi1
                new_minimal_points = []
                check_xi1 = True
                for xi2 in minimal_points:
                    if xi1.is_leq(xi2):
                        # we can replace xi2 by xi1
                        new_minimal_points.append(xi1)
                        check_xi1 = False
                    elif check_xi1 and xi2.is_leq(xi1):
                        # we have xi2 < xi1 so we omit xi1 and retain xi2
                        new_minimal_points.append(xi2)
                        check_xi1 = False
                    else:
                        # xi1 and xi2 are incomparable or xi1 has already been dismissed
                        new_minimal_points.append(xi2)
                if check_xi1:
                    # xi1 has not been found to be incomparable to all previous points
                    new_minimal_points.append(xi1)
                minimal_points = new_minimal_points
        return minimal_points


class ClosedUnitDisk(AffinoidDomainOnBerkovichLine):
    r"""
    Return the closed unit disk.

    The **closed unit disk** is the affinoid on the Berkovich line with
    function field `F=K(x)` defined by the inequality

    .. MATH::

          v(x) >= 0.

    INPUT:

    - ``X`` -- a Berkovich line

    OUTPUT: the closed unit disk inside ``X``

    EXAMPLES::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(3)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: ClosedUnitDisk(X)
        Affinoid with 1 components:
        Elementary affinoid defined by
        v(x) >= 0

    """

    def __init__(self, X):

        self._X = X
        T = AffinoidTree(X, root=X.gauss_point(), is_in=True)
        T1 = AffinoidTree(X, root=X.infty(), is_in=False)
        T.make_child(T1)
        self._T = T


class ElementaryAffinoidOnBerkovichLine(AffinoidDomainOnBerkovichLine):
    r"""
    Return the elementary affinoid corresponding to a boundary list.

    An "elementary affinoid" is a connected affinoid subdomain of a Berkovich
    line `X` which is the complement of a finite set of disjoint residue classes
    in `X`. It can be represented by a "boundary list" as follows.

    A "boundary list" is a list of lists, whose entries at the lowest level are
    type-V-points on `X`. Each sublist contains the type-V-points with a common
    boundary point. The elementary affinoid corresponding to a "boundary list" is
    the complement of the residue classes corresponding to the type-V-points
    contained in the sublists. The set of boundary points of the type-V-points is
    exactly the Shilov boundary of the affinoid.

    INPUT:

    - ``boundary_list`` -- a list of lists containing type-V-points.

    OUTPUT:

    The elementare affinoid corresponding to ``comp_list``.


    TO DO:

    - we need a function which produces an (algebraic) type-I-point inside the
      affinoid.

    """

    def __init__(self, T):
        X = T.berkovich_line()
        self._X = X
        self._T = T
        boundary = []
        complement = []
        if T.root_is_in():
            holes = T.holes()
        else:
            assert len(T.children()) > 0, "connected component must not be empty"
            assert len(T.children()) == 1, "component is not connected"
            T1 = T.children()[0]
            assert T1.root_is_in(), "tree must have only one out-point for eachboundary point"
            holes = T1.holes()
        for T2, _, eta in holes:
            xi = T2.root()
            if all([not xi.is_equal(xi1) for xi1 in boundary]):
                boundary.append(xi)
            complement.append(eta)
        self._boundary = boundary
        self._complement = complement
        if holes == []:
            if T.root_is_in():
                self._is_empty = False
                self._is_full_berkovich_line = True
            else:
                self._is_empty = True
                self._is_full_berkovich_line = False
        else:
            self._is_empty = False
            self._is_full_berkovich_line = False

    def __repr__(self):
        if self.is_empty():
            return "The empty set"
        elif self.is_full_berkovich_line():
            return "the full berkovich line"
        else:
            return "Elementary affinoid defined by {}".format(self.inequalities())

    def is_empty(self):
        return self._is_empty

    def is_full_berkovich_line(self):
        return self._is_full_berkovich_line

    def inequalities(self):
        r"""
        Return the inequalities defining the elementary affinoid, as a string.

        """
        inequalities = "\n"
        for eta in self._complement:
            phi, s = eta.open_discoid()
            inequalities += ("v(" + str(1/phi) + ") >= " + str(-s)) + "\n"
        return inequalities


class RationalDomainOnBerkovichLine(AffinoidDomainOnBerkovichLine):
    r"""
    Return the rational domain on ``X`` defined by ``f``.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``f`` -- a nonconstant rational function on `X`

    OUTPUT:

    the affinoid domain on `X` defined by the inequality

    .. MATH::

    v(f) >= 0.


    EXAMPLES::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: RationalDomainOnBerkovichLine(X, (x^2+2)/x*(x+1)/2)
        Affinoid with 2 components:
        Elementary affinoid defined by
        v(x^2 + 2) >= 3/2
        Elementary affinoid defined by
        v(x + 1) >= 1

        f must be nonconstant:

        sage: RationalDomainOnBerkovichLine(X, F(1/2))
        Traceback (most recent call last):
        ...
        AssertionError: f must be nonconstant


    TO DO:

    I think this can be drastically improved, by using the following ideas:

    - it should not be necessary to first build a tree with all zeroes and poles
      of `f` as leaves. At any stage of bulding the tree one looks at a discoid
      `D`. If `f` has nonnegative valuation on the boundary of `D` and
      no poles inside `D` (or nonpositive valuation on the boundary and no
      zero inside) then we can stop at `D`.
    - Instead of working with a (possible huge) rational function `f` we should
      work with a "factorization", i.e. a list of pairs `(f_i, e_i)` where
      `f_i` is an irreducible polynomial or a constant and `e_i` an integer
      (rationals are also fine).
      At any stage of building the tree, we only retain the sublist
      of pairs `(f_i,e_i)` which are "active"; for the "inactive" pairs we
      only need to know their valuations - which is constant on the subtree!

    """

    def __init__(self, X, f):
        F = X.function_field()
        f = F(f)
        assert f not in F.constant_base_field(), "f must be nonconstant"
        self._X = X
        U = AffinoidTree(X)
        xi0 = X.gauss_point()
        T = BerkovichTree(X, xi0)
        T = T.adapt_to_function(f)
        path_list = T.paths()
        for xi1, xi2 in path_list:
            in_list = []
            out_list = []
            xi1_in = xi1.v(f) >= 0
            if xi1_in:
                in_list.append(xi1)
            else:
                out_list.append(xi1)
            xi2_in = xi2.v(f) >= 0
            if xi2_in:
                in_list.append(xi2)
            else:
                out_list.append(xi2)
            if xi1_in != xi2_in:
                # there must be a point between xi1 and xi2 where v(f)=0
                # which we have to add to the in_list
                xi3 = xi1.berkovich_line().find_zero(xi1, xi2, f)
                assert xi3.v(f) == 0, "got the wrong value for t!"
                in_list.append(xi3)
            U = U.add_points(in_list, out_list)
        # we test whether U is correct
        for xi in U.vertices():
            assert (xi.v(f) >= 0) == U.is_in(xi)
        self._T = U

# -------------------------------------------------------------------------


"""
Some auxiliary functions:

"""


def irreducible_polynomial_prime_to(f, min_deg=1):
    """ Return an irreducibel polynomial prime to f.

    INPUT:

    - f: an univariat polynomial over a finite field
    - min_deg: a positive integer (default = 1)

    OUTPUT:

    an irreducible polynomial prime to f, of degree >=min_deg

    """

    R = f.parent()
    x = R.gen()
    F = R.base_ring()
    assert F.is_finite(), "base field of f must be finite."
    for d in range(min_deg, 10):
        for g in all_polynomials(F, x, d):
            if g.is_irreducible() and g.gcd(f).is_one():
                return g


def all_polynomials(F, x, d):
    """ List all polynomials in x over F of degree d.

    INPUT:

    - F: a finite field F
    - x: generator of a polynomial ring over F

    OUTPUT:

    an iterator which list all elements of F[x] of degree d.

    """
    if d == 0:
        for a in F.list():
            yield a*x**0
    else:
        for e in range(0, d):
            for f in all_polynomials(F, x, e):
                yield x**d + f


def union_of_affinoid_trees(T1, T2):
    r""" Return the tree representing the union of the affinoids with given trees.

    This is now obsolete.

    INPUT:

     - ``T1``, ``T2`` -- affinoid trees

     OUTPUT: the tree representing the union of the affinoids represented by
     `T_1` and `T_2`.

    """
    xi1 = T1.root()
    xi1_in = T1._is_in
    xi2 = T2.root()
    xi2_in = T2._is_in
    if xi2.is_leq(xi1):
        if xi1.is_leq(xi2) and not xi1_in and xi2_in:
            xi1, xi2 = xi2, xi1
            T1, T2 = T2, T1
            xi1_in = True
            xi2_in = False
    if xi1_in:
        # xi1 is the minimal point in the union
        pass


def simplify_tree_at_vertex(T, T1):
    r""" Simplify the affinoid tree at a given vertex.

    This is now obsolete.

    INPUT:

    - ``T`` -- an affinoid tree
    - ``T1`` -- a subtree of `T`

    OUTPUT: the affinoid tree `T` is simplified, starting at the subtree `T_1`.

    We check whether the root of `T_1` (which is a vertex of `T`) may be
    contracted, or whether `T_1` has a unique child which may be omitted.
    In the first case, we try to iterate this, if possible.

    This may not simplify `T` as much as possible. However, if `T` has been
    obtained from a simplified

    """
    if T1.children() == []:
        # a leaf can be omitted if its parent has the same in-out type
        if T1.has_parent() and T1.parent()._is_in == T1._is_in:
            T2 = T1.parent()
            T.remove_subtree(T1)
            simplify_tree_at_vertex(T, T2)
    elif len(T1.children()) == 1:
        T2 = T1.children()[0]


def _make_affinoid_tree_with_in_leaves(X, leaves):
    from mclf.berkovich.berkovich_trees import BerkovichTree
    T = BerkovichTree(X)
    for xi in leaves:
        T, _ = T.add_point(xi)
    return _make_affinoid_tree_with_in_leaves_inductively(T)


def _make_affinoid_tree_with_in_leaves_inductively(T):
    r""" Return an affinoid tree with in-leaves copied from a Berkovich tree.

    INPUT:

    - ``T`` -- a Berkovich tree

    OUTPUT: an affinoid tree which is a copy of T, such that the in-points are
    precisely the leaves.

    """
    if T.is_leaf():
        return AffinoidTree(T.berkovich_line(), root=T.root(), is_in=True)
    else:
        T_new = AffinoidTree(T.berkovich_line(), root=T.root(), is_in=False)
        for child in T.children():
            T_new.make_child(_make_affinoid_tree_with_in_leaves_inductively(child))
        return T_new
