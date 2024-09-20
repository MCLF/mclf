# -*- coding: utf-8 -*-
r"""
Finite subtrees of the Berkovich line
=====================================

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `X=\mathbb{P^1_K}`
be the projective line over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. We call `X^{an}` the *Berkovich
line* over `K`.

Let `\xi^g` be the *Gauss point* on `X^{an}`, corresponding to the Gauss
valuation on the function field of `X` with respect to the canonical parameter
`x`. Then `X^{an}` has a natural partial ordering for which `\xi^g` is the
smallest element. With respect to this partial ordering, any two elements have
a unique infimum.

A *Berkovich tree* is a finite (nonempty) subset `T` with the
property that for any two elements in `T` the infimum is also contained in
`T`. In particular, a `T` has a least element, called the *root* of the tree.

Given any finite subset `S` of `X^{an}`, there is now a unique minimal
subtree `T` containing `S`. We call `T` the tree *spanned* by `S`.

This module realizes finite subtrees of `X^{an}` as combinatorial objects,
more precisely as *finite rooted combinatorial trees*. So a tree consists
of a root, and a list of children. If the tree is a subtree of another tree,
then there is a link to its parent.

AUTHORS:

- Stefan Wewers (2017-02-13): initial version


EXAMPLES::

<Lots and lots of examples>
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

from sage.all import SageObject, Graph


class BerkovichTree(SageObject):
    r"""
    Create a new Berkovich tree `T`.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``root`` -- a point of ``X`` (default: None)
    - ``children`` -- a list of Berkovich trees on ``X`` (default = None)
    - ``parent`` -- a Berkovich tree or None (default: None)

    OUTPUT:

    A Berkovich tree `T` on `X` with root ``root``, children ``children`` and
    parent ``parent``.
    `T` may be empty (no root and no children), but if there are children
    then there must be root.


    EXAMPLES::

        sage: from mclf import *
        sage: v_2 = QQ.valuation(2)
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, v_2)
        sage: T = BerkovichTree(X); T
        Berkovich tree with 0 vertices
        sage: xi = X.gauss_point()
        sage: T.find_point(xi)

    """

    def __init__(self, X, root=None, children=None, parent=None):

        # print("calling BerkovichTree with root %s, children %s and
        # parent %s"%(root, children, parent))
        self._root = root
        if children is None:
            self._children = []
        else:
            self._children = children
        if root is None and self._children != []:
            raise ValueError("tree with children must have a root")

        self._parent = parent
        self._X = X
        assert all(self._X == T._X for T in self._children), \
            "children must live on the same Berkovich line as root"
        # initialize an empty dictionary, to be used by applications
        # in this module we do not touch it
        self._attr = {}

    def __repr__(self):
        return "Berkovich tree with {} vertices".format(len(self.vertices()))

    def is_empty(self):
        return self._root is None

    def root(self):
        """ Return the root of the tree."""
        return self._root

    def berkovich_line(self):
        """ Return the Berkovich line underlying this tree."""
        return self._X

    def has_parent(self):
        """ Return True if self has a parent."""
        return self._parent is not None

    def parent(self):
        """ Return the parent of self."""
        return self._parent

    def make_parent(self, parent):
        """ add ``parent`` as parent of self."""
        self._parent = parent

    def make_child(self, new_child, check=True):
        r""" Make ``new_child`` a child of self.

        INPUT:

        - ``new_child`` -- a Berkovich tree
        - ``check`` -- a boolean (default ``False``)

        We make the tree ``new_child`` a child of ``self``. For this to make
        sense, two conditions have to be satisfied:

        - the root of ``new_child`` has to be strictly greater than the root of
          ``self``
        - the root of ``new_child`` has to be incomparable to the roots of the
          already existing children of ``self``

        These conditions are checked only if ``check`` is ``True``.

        Note:

        This changes both trees ``self`` and ``new_child``.
        """
        if check:
            assert self.root().is_strictly_less(new_child.root()), \
                "new child has to be strictly greater than self"
            for child in self.children():
                assert child.root().is_incomparable(new_child.root()), \
                    "new child has to be incomparable to other children"
        self._children.append(new_child)
        new_child.make_parent(self)

    def remove_child(self, child):
        r""" Remove child from list of children of ``self``.

        INPUT:

        - ``child`` -- a Berkovich tree

        We remove ``child`` from the list of children of ``self``. If ``child``
        is not in this list, an error is raised.

        Note:

        This function changes both ``self`` and ``child``.

        """
        self._children.remove(child)
        child._parent = None

    def children(self):
        """ Return the list of all children.

        This is a deep copy of the internal list of children!
        Therefore, it cannot be used to change the tree.

        """
        return [child for child in self._children]

    def is_leaf(self):
        """ Return True if self is a leaf.

        """
        return self._root is not None and self._children == []

    def vertices(self):
        r"""
        Return the list of all vertices.

        """
        vertices = []
        if self._root is not None:
            vertices.append(self._root)
        for T in self._children:
            vertices += T.vertices()
        return vertices

    def leaves(self, subtrees=False):
        r"""
        Return the list of all leaves.

        If ``subtrees`` is ``True``, then we return the list of subtrees
        corresponding to the leaves.
        """

        leaves = []
        if self.is_leaf():
            if subtrees:
                leaves.append(self)
            else:
                leaves.append(self._root)
        else:
            for T in self._children:
                leaves += T.leaves(subtrees)
        return leaves

    def subtrees(self):
        r""" Return the list of all subtrees.
        """

        subtrees = []
        if not self.is_empty():
            subtrees.append(self)
        for T in self.children():
            subtrees += T.subtrees()
        return subtrees

    def paths(self):
        r"""
        Return the list of all directed paths of the tree.

        OUTPUT:

        the list of all directed paths of the tree, as a list of pairs
        `(\xi_1,\xi_2)`, where `\xi_2` is a child of `\xi_1`.

        """

        path_list = []
        T1 = self
        for T2 in T1.children():
            path_list.append((T1.root(), T2.root()))
            path_list += T2.paths()
        return path_list

    def direction_to_parent(self):
        r""" Return the direction to the parent.

        OUTPUT: the type V point `\eta` representing the direction from the
        root of ``self`` to the root of its parent.

        If ``self`` has no parent, an error is raised.

        The direction is not well defined if the root of ``self`` is a point of
        type I. Therefore, an error is raised in this case.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        assert self.root().type() == "II", \
            "the root must be a point of type II: root = {}, parent = {}".format(self.root(), self.parent().root())
        if not hasattr(self, "_direction_to_parent"):
            eta = TypeVPointOnBerkovichLine(self.root(), self.parent().root())
            self._direction_to_parent = eta
        return self._direction_to_parent

    def direction_from_parent(self):
        r""" Return the direction from the parent.

        OUTPUT: the type V point `\eta` representing the direction from the
        root of the parent of ``self`` to the root of ``self``.

        If ``self`` has no parent, an error is raised.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        if not hasattr(self, "_direction_from_parent"):
            eta = TypeVPointOnBerkovichLine(self.parent().root(), self.root())
            self._direction_from_parent = eta
        return self._direction_from_parent

    def copy(self):
        r""" Return a copy of self."""
        from copy import copy
        T = copy(self)
        children = []
        for child in self.children():
            children.append(child.copy())
        T._children = children
        return T

    def add_point(self, xi):
        r"""
        Return the tree spanned by self and the point xi.

        INPUT:

        - ``xi`` -- A point of type I or II on X

        OUTPUT: `T_1`, `T_2`, where

        - `T_1` is the tree obtained from `T_0`=self after inserting `\xi` as a vertex.
        - `T_2` is the subtree of `T_1` with root `\xi`

        If `T_0` has a parent, then the root of `T_0` must be less than `\xi`.
        Therefore, the parent of `T_1` will be the original parent of `T_0`.

        Note that this command may change the tree `T_0`!  For instance, `\xi` may
        become the root of `T_1` and then `T_0` has `T_1` as new parent.
        """

        T0 = self
        if T0.has_parent():
            assert T0.root().is_leq(xi), "The root of self must be less than xi, because self has a parent."
        if T0._root is None:
            T0._root = xi
            return T0, T0       # T0 is the leaf with root xi

        xi0 = T0._root
        if xi0.is_equal(xi):
            return T0, T0   # T0 has xi as root

        if xi0.is_leq(xi):
            # now xi0 < xi
            for i in range(len(T0._children)):
                # we run through all immediate children T1 of T0
                T1 = T0._children[i]
                xi1 = T1._root
                if xi1.is_leq(xi):
                    # now xi0 < xi1 <= xi and xi can be added to T1
                    T_new, T_xi = T1.add_point(xi)
                    # note that this does not change the parent of T1, which is still T0
                    # IS THIS TRUE ?? Let's check:
                    assert T_new.parent() == T0
                    T0._children[i] = T_new
                    return T0, T_xi
                elif xi.is_leq(xi1):
                    # now xi0 < xi < xi1; we have to insert x between T0 and T1
                    T1_new = BerkovichTree(T0._X, xi, [T1], T0)
                    T1.make_parent(T1_new)
                    T0._children[i] = T1_new
                    return T0, T1_new
                else:
                    xi2 = xi1.infimum(xi)
                    # note that xi0 <= xi2
                    if not xi0.is_equal(xi2):
                        # now xi0 < xi2; we have to replace T1 (as a subtree of T0)
                        # by a new tree T_new with children T1 and a leaf T_xi
                        T_xi = BerkovichTree(T0._X, xi)  # the new leaf
                        T_new = BerkovichTree(T0._X, xi2, [T1, T_xi], T0)
                        # the new subtree has parent T0
                        T1.make_parent(T_new)
                        T_xi.make_parent(T_new)
                        T0._children[i] = T_new
                        return T0, T_xi
            # if we get here, we have to add xi as a new leaf with parent xi0
            T_xi = BerkovichTree(T0._X, xi, [], T0)
            T0._children.append(T_xi)
            return T0, T_xi
        elif xi.is_leq(xi0):
            # xi is less than the root of T0
            # we have to make xi the root and append T0 as the only subtree
            T_new = BerkovichTree(T0._X, xi, [T0], None)
            T0.make_parent(T_new)
            return T_new, T_new

        else:
            # now xi0 and xi are uncomparable
            # hence we need a new root
            assert T0.parent() is None, "T0 must not have a parent"
            new_root = xi0.infimum(xi)
            T_xi = BerkovichTree(T0._X, xi)
            T_new = BerkovichTree(T0._X, new_root, [T0, T_xi])
            T0.make_parent(T_new)
            T_xi.make_parent(T_new)
            return T_new, T_xi

    def find_point(self, xi):
        r""" Find subtree with root ``xi``.

        INPUT:

        - ``xi`` -- a point on the Berkovich line underlying ``self``

        OUTPUT:

        The subtree `T` of ``self`` with root ``xi``, or ``None`` if ``xi``
        is not a vertex of ``self``.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: T = BerkovichTree(X); T
            Berkovich tree with 0 vertices

        Searching in the empty tree does not give an error anymore.::

            sage: xi = X.gauss_point()
            sage: T.find_point(xi)

            sage: T.add_point(xi)
            (Berkovich tree with 1 vertices, Berkovich tree with 1 vertices)
            sage: T.find_point(xi)
            Berkovich tree with 1 vertices


        """
        # if the tree is empty:
        if not self._root:
            return None
        if self._root.is_equal(xi):
            return self
        else:
            for T in self._children:
                T1 = T.find_point(xi)
                if T1 is not None:
                    return T1
            return None

    def remove_point(self, xi, test_inequality=True):
        r"""
        Remove a point from the tree, if possible.

        INPUT:

        - ``xi`` -- a point of type I or II on the Berkovich line
        - ``test_inequality -- a boolean (default: ``True``)

        OUTPUT:

        the tree obtained from ``self`` by removing, if possible, the vertex
        with root `\xi`.

        Removing the vertex with root `\xi` is possible if a vertex with root
        `\xi` exists, and if it has at most one child. Otherwise, nothing is
        changed.

        Note that the vertex to be removed may be the root of this tree. If this
        is the case and there is no child, then an empty tree is return *and*
        the tree is remove as a child from its parent.

        If ``test_inequality`` is ``False`` then it is assumed that `\xi` is
        greater or equal to the root of ``self``. This saves us a test for
        inequality.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: T = BerkovichTree(X)
            sage: T, _ = T.add_point(X.gauss_point())
            sage: T = T.remove_point(X.gauss_point()); T
            Berkovich tree with 0 vertices
            sage: xi_list = [xi for xi, m in X.divisor(x*(x^2+2))]
            sage: for xi in xi_list: T, _ = T.add_point(xi)
            sage: T
            Berkovich tree with 5 vertices
            sage: T.remove_point(xi_list[0])
            Berkovich tree with 4 vertices

        """
        if test_inequality and not self.root().is_leq(xi):
            # xi cannot be a vertex of this tree, so we have to do nothing
            return self
        if len(self._children) <= 1 and self.root().is_equal(xi):
            # xi is the root of this tree and can be removed
            if len(self.children()) == 0:
                # we return an empty tree
                return BerkovichTree(self.berkovich_line())
            else:
                # we return the only child
                return self._children[0]
        else:
            # xi is not the root of this tree, but
            # xi may be a vertex in at most one of the subtrees
            subtree = None
            for child in self.children():
                if child.root().is_leq(xi):
                    subtree = child
                    break
            if subtree:
                new_subtree = subtree.remove_point(xi, test_inequality=False)
                self.remove_child(subtree)
                if not new_subtree.is_empty():
                    self.make_child(new_subtree)
            return self

    def adjacent_vertices(self, xi0):
        """
        List all vertices of the tree adjacent to a given vertex.

        """
        T = self.find_point(xi0)
        if T is None:
            return []
        ret = []
        if T.has_parent():
            ret.append(T.parent().root())
        for child in T.children():
            ret.append(child.root())
        return ret

    def print_tree(self, depth=0):
        """ Print the vertices of the tree, with indentation corresponding to depth.

            It would be nicer to plot the graph and then list the points corresponding
            to the vertices.
        """

        if self._root is None:
            return
        print("___"*depth, " ", self._root)
        for T in self._children:
            T.print_tree(depth + 1)

    def position(self, xi):
        r"""
        Find the position of ``xi`` in the tree T=self.

        INPUT:

        - ``xi`` -- a point on the Berkovich line underlying T

        OUTPUT:

        xi1, T1, T2, is_vertex,

        where

        - xi1 is the image of xi under the retraction map onto the total space
          of T
        - T1 is the smallest subtree of T whose total space contains xi1
        - T2 is the child of T1 such that xi1 lies on the edge connecting T1
          and T2 (or is equal to T1 if xi1 is the root of T1)
        - is_vertex is True if xi1 is a vertex of T (which is then the root of
          T1) or False otherwise

        """

        T = self
        assert not T.is_empty(), "The tree T must not be empty."
        if not T.root().is_leq(xi) or xi.is_leq(T.root()):
            # xi1 is the root of T
            return T.root(), T, T, True
        else:
            # xi is strictly greater than the root of T
            for T1 in T.children():
                if T1.root().is_leq(xi):
                    # the position of xi lies in T1
                    return T1.position(xi)
                else:
                    # xi and the root of T1 are uncomparable
                    xi1 = T1.root().infimum(xi)
                    # xi1 is strictly less than xi and the root of T1
                    if not xi1.is_equal(T.root()):
                        # xi1 lies strictly between T and T1
                        return xi1, T, T1, False
                    # T1 is not the subtree we are looking for
            # if we get here, then xi1 is the root of T
            return T.root(), T, T, True

    def graph(self):
        """ Return a graphical representation of self.

        OUTPUT:

        G, vert_dict,

        where G is a graph object and vert_dict is a dictionary associating
        to a vertex of G the corresponding vertex of self.
        """

        G = Graph()
        G.add_vertex(0)
        vert_dict = {}
        create_graph_recursive(self, G, vert_dict, 0)
        return G, vert_dict

    def adapt_to_function(self, f):
        r"""
        Add all zeroes and poles of `f` as leaves of the tree.

        INPUT:

        - ``f`` -- a rational function on `X`

        OUTPUT:

        the new tree obtained by adding all zeroes and poles of `f` as
        vertices to the old tree.
        """

        T = self
        D = T._X.divisor(f)
        for xi, m in D:
            T, T1 = T.add_point(xi)
        return T

    def permanent_completion(self):
        r"""
        Return the permanent completion of ``self``.

        OUTPUT:

        A Berkovich tree `T_1` which is the permanent completion of ``self``.

        A Berkovich tree tree `T` on a Berkovich line `X` over `(K,v_K)` is
        called *permanently complete* if for all finite extensions `(L,v_L)` of
        `(K,v_K)`, the inverse image of the set of vertices of `T` in `X_L` is
        again the set of vertices of a Berkovich tree. It is easy to see that
        for any Berkovich tree `T` there exists a minimal refinement `T_1` which
        is permanently complete. It is called the *permanent completion* of `T`.

        ALGORITHM:

        Let `\xi_0` be the root and `\xi_1,\ldots,\xi_n` the leaves of `T`.
        To compute `T_1` we consider, for `i=1,\ldots,n`, the path
        `\gamma = [\xi_0,\xi_n]` and the function on `\gamma` which maps a point
        `\xi` to the number of geometric components of the discoid `D_\xi`.
        We add the jumps of this function to `T`. Having done this for all `i`
        we obtain the permant completion `T_1` of `T`.

        EXAMPLES::

            sage: from mclf import *
            sage: FX.<x> = FunctionField(QQ)
            sage: v_2 = QQ.valuation(2)
            sage: X = BerkovichLine(FX, v_2)
            sage: xi0 = X.point_from_discoid(x^4+2, 5)
            sage: T = BerkovichTree(X, xi0)
            sage: T.permanent_completion()
            Berkovich tree with 3 vertices

        """
        T = self
        xi0 = T.root()
        X = xi0.berkovich_line()
        if not xi0.is_gauss_point():
            for xi in component_jumps(X.gauss_point(), xi0):
                T, _ = T.add_point(xi)
        if len(T.children()) == 0:
            return T
        xi0 = T.root()
        leaves = T.leaves()
        for xi1 in leaves:
            for xi in component_jumps(xi0, xi1):
                T, _ = T.add_point(xi)
        return T


def replace_subtree(T1, T2):
    r""" Replace a subtree of a Berkovich tree by another tree.

    INPUT:

    - ``T1``, ``T2`` - Berkovich trees with the same root

    It is assumed that `T_1` has a parent, so it is a proper subtree of an
    affinoid tree `T_0`. We replace the subtree `T_1` with `T_2`.

    NOTE::

        This changes the tree `T_0`; therefore this function must be
        used carefully.

    """
    assert T1.has_parent(), "T1 must have a parent"
    assert T1.root().is_equal(T2.root()), "T1 and T2 must have the same root"
    T0 = T1.parent()
    T0.remove_child(T1)
    T0.make_child(T2, check=True)


def create_graph_recursive(T, G, vertex_dict, root_index):
    r""" Create recursively a graph from a Berkovich tree.
    """

    xi0 = T.root()
    vertex_dict[root_index] = xi0
    for T1 in T.children():
        n = G.num_verts()
        G.add_edge(root_index, n)
        create_graph_recursive(T1, G, vertex_dict, n)


def component_jumps(xi0, xi1):
    r""" Helper function for ``permanent_completion``.

    """
    from sage.geometry.newton_polygon import NewtonPolygon
    from mclf.berkovich.berkovich_line import valuations_from_inequality
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    from mclf.berkovich.berkovich_line import TypeIIPointOnBerkovichLine

    assert xi0.is_leq(xi1), "xi0 has to be an ancestor of xi1"
    X = xi0.berkovich_line()
    vK = X.base_valuation()

    v0 = xi0.pseudovaluation_on_polynomial_ring()
    v1 = xi1.pseudovaluation_on_polynomial_ring()
    y = xi1.parameter()
    if hasattr(v1, "phi"):
        phi = v1.phi()
        # v1 is an inductive valuation
    else:
        phi = v1._G
        # v1 is a limit valuation
    assert v0(phi) < v1(phi), "xi0 is not an ancestor of xi1!"
    R = phi.parent()
    x = R.gen()
    S = PolynomialRing(R, 'T')
    T = S.gen()
    G = phi(x+T)
    NP = NewtonPolygon([(i, v1(G[i])) for i in range(G.degree()+1)])
    V = []
    vertices = NP.vertices()
    for k in range(len(vertices)-1):
        i, ai = vertices[k]
        j, aj = vertices[k+1]
        a0 = aj - j*(ai-aj)/(i-j)
        # print("a0 = ", a0)
        V += valuations_from_inequality(vK, phi, a0, v0)
    ret = [TypeIIPointOnBerkovichLine(X, (v, y)) for v in V]
    """
    if xi1.is_in_unit_disk():
        ret = [X.point_from_polynomial_pseudovaluation(v) for v in V]
    else:
        ret = [X.point_from_polynomial_pseudovaluation(v, in_unit_disk=False) for v in V]
    """
    return [xi for xi in ret if (xi0.is_leq(xi) and xi.is_leq(xi1))]
    # the last 'if' is necessary if phi = v1._G above


def check_tree(T):
    if T.has_parent():
        assert T in T.parent().children(), "T is not child of parent!"
    for child in T.children():
        assert T.root().is_strictly_less(child.root()), \
            "child with root {} is not strictly greater then parent with root {}".format(child.root(), T.root())
        check_tree(child)
