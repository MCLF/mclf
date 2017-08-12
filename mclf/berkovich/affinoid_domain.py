r""" Affinoid subdomains of the Berkovich line.
===============================================

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `X=\mathbb{P}^1_K`
be the projective line over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. We call `X^{an}` the **Berkovich
line** over `K`.

In this file we realize a Sage class which allows us to create and work with
strictly affinoid subdomains of `X^{an}`.

Let `T` be a Berkovich tree in `X^{an}` and let `r:T-->X^{an}` denote the
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
from sage.rings.infinity import Infinity
from mac_lane import *
from mclf.berkovich.berkovich_line import BerkovichLine, TypeIPointOnBerkovichLine,\
                                          TypeIIPointOnBerkovichLine
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
from mclf.berkovich.berkovich_trees import BerkovichTree


class AffinoidTree(BerkovichTree):
    r""" A marked Berkovich tree representing an affinoid subdomain.

    An AffinoidTree is a Berkovich tree `T` in which every vertex has an additional
    flag "is_in_affinoid" with value ``True`` or ``False``. It represents an
    affinoid subdomain `U` in the way explained above.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``root`` -- a point on ``X``or None (default = None)
    - ``children`` -- a list of affinoid trees or None (default = None)
    - ``parent`` -- an affinoid tree or none (default = None)
    - ``is_in_affinoid`` -- a boolean or None (default = None)

    OUTPUT:

    An affinoid tree on ``X``. It is either empty (if only ``X`` is given) or
    it has root, parent, children and the flag ``is_in_affinoid`` as given
    by the extra parameters.

    EXAMPLES:
    ::

        sage: K = QQ
        sage: vK = pAdicValuation(K, 2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: xi0 = X.gauss_point()
        sage: xi1 = X.point_from_discoid(x^2+2, 3/2)
        sage: xi2 = X.point_from_discoid(x^4+2, 3/2)
        sage: xi3 = X.point_from_discoid(x^2+x+1, 1)
        sage: xi4 = X.point_from_discoid(x^2+2, 2, False)

        sage: U1 = AffinoidTree(X)
        sage: U1 = U1.add_points([xi0], [xi1, xi3])
        sage: U2 = AffinoidTree(X)
        sage: U2 = U2.add_points([xi2], [xi4])

        sage: U = U1.union(U2)
        sage: U
        Affinoid tree with 6 vertices
    """

    def __init__(self, X, root=None, children=None, parent=None, is_in_affinoid=False):

        self._X = X
        if root == None:
            self._root = None
            self._children = []
            self._parent = None
            self._is_in_affinoid = False
            # Now we have an empty affinoid tree
        else:
            self._root = root
            self._parent = parent
            self._children = children
            self._is_in_affinoid = is_in_affinoid


    def __repr__(self):

        return "Affinoid tree with %s vertices"%len(self.vertices())

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
        T_new = AffinoidTree(T._X, T.root(), [], parent,
                              T._is_in_affinoid)
        children = [T1.copy(T_new) for T1 in T.children()]
        T_new._children = children
        return T_new


    def add_point(self, xi, is_in_affinoid):
        r"""
        Return the affinoid tree spanned by self and the point xi.

        INPUT:

        - ``xi`` -- a point on the berkovich tree
        - ``is_in_affinoid`` -- a boolean

        OUTPUT:

        (`T_1`, `T_2`), where

        - `T_1` is the tree obtained from `T_0=` ``self`` after inserting ``xi``
          as a vertex.
        - `T_2` is the subtree of `T_1` with root ``xi``

        It is assumed that if `T_0` has a parent, then the root of `T_0` is less
        than `\xi`. As a result, the parent of `T_1` will be the original parent
        of `T_0`.

        Note that this command may change the tree `T_0`!  For instance, `\xi` may
        become the root of `T_1` and then `T_0` has `T_1` as new parent.

        Also, the new vertex (the root of `T_1`) is marked with the flag
        ``is_in_affinoid``.

        """

        T0 = self
        parent = T0.parent()
        if parent != None:
            assert T0.root().is_leq(xi), "The root of self must be less than xi, because self has a parent."
        if T0._root == None:
            T0._root = xi
            T0._is_in_affinoid = is_in_affinoid
            return T0, T0       # T0 is the leaf with root xi

        xi0 = T0._root
        if xi0.is_equal(xi):
            # assert T0._is_in_affinoid == is_in_affinoid
            T0._is_in_affinoid = is_in_affinoid
            return T0, T0   # T0 has xi as root

        if xi0.is_leq(xi):
            # now xi0 < xi
            for i in range(len(T0._children)):
                # we run through all immediate children T1 of T0
                T1 = T0._children[i]
                xi1 = T1._root
                if xi1.is_leq(xi):
                    # now xi0 < xi1 <= xi and xi can be added to T1
                    T_new, T_xi = T1.add_point(xi, is_in_affinoid)
                    # note that this does not change the parent of T1, which is
                    # still T0
                    # IS THIS TRUE ?? Let's check:
                    assert T_new.parent() == T0
                    T0._children[i] = T_new
                    return T0, T_xi
                elif xi.is_leq(xi1):
                    # now xi0 < xi < xi1; we have to insert x between T0 and T1
                    T1_new = AffinoidTree(T0._X, xi, [T1], T0, is_in_affinoid)
                    T1.make_parent(T1_new)
                    T0._children[i] = T1_new
                    return T0, T1_new
                else:
                    xi2 = xi1.infimum(xi)
                    # note that xi0 <= xi2
                    if not xi0.is_equal(xi2):
                        # now xi0 < xi2; we have to replace T1 (as a subtree of T0)
                        # by a new tree T_new with children T1 and a leaf T_xi
                        T_xi = AffinoidTree(T0._X, xi, [], None, is_in_affinoid)
                               # the new leaf
                        T_new = AffinoidTree(T0._X, xi2, [T1, T_xi], T0,
                                             T0._is_in_affinoid)
                        # the new subtree has parent T0
                        # and its root lies in U iff the root of T0 does
                        T1.make_parent(T_new)
                        T_xi.make_parent(T_new)
                        T0._children[i] = T_new
                        return T0, T_xi
            # if we get here, we have to add xi as a new leaf with parent xi0
            T_xi = AffinoidTree(T0._X, xi, [], T0, is_in_affinoid)
            T0._children.append(T_xi)
            return T0, T_xi
        elif xi.is_leq(xi0):
            # xi is less than the root of T0
            # we have to make xi the root and append T0 as the only subtree
            T_new = AffinoidTree(T0._X, xi, [T0], None, is_in_affinoid)
            T0.make_parent(T_new)
            T_new.make_parent(parent)
            return T_new, T_new
        else:
            # now xi0 and xi are uncomparable
            # hence we need a new root
            assert T0.parent() == None, "T0 must not have a parent"
            new_root = xi0.infimum(xi)
            T_xi = AffinoidTree(T0._X, xi, [], None, is_in_affinoid)
            T_new = AffinoidTree(T0._X, new_root, [T0, T_xi], None,
                                 is_in_affinoid and T0._is_in_affinoid)
            T0.make_parent(T_new)
            T_xi.make_parent(T_new)
            T_new.make_parent(parent)
            return T_new, T_xi


    def add_points(self, in_list, out_list):


        T = self
        for xi in in_list:
            T, subtree = T.add_point(xi, True)
        for xi in out_list:
            T, subtree = T.add_point(xi, False)
        return T


    def is_in_affinoid(self, xi):
        r""" Return True if xi lies in the affinoid  U represented by self.

        To test this, we compute the image of xi under the retraction map
        onto the total space of T=self and check whether it lies on a vertex
        in U or on an edge connecting two vertices in U.
        """

        xi1, T1, T2, is_vertex = self.position(xi)
        # xi1 is the image of xi under the retraction map onto the total
        # space of T=self. If is_vertex==True then xi1 is the root of T1.
        # Otherwise, xi1 lies on the edge connecting the roots of T1 and T2.
        if is_vertex:
            return T1._is_in_affinoid
        else:
            return T1._is_in_affinoid and T2._is_in_affinoid

    def simplify(self):
        r"""
        Return a simplified tree representing the same affinoid.

        """

        T = self
        T_new = AffinoidTree(T._X)
        for T1 in T.subtrees():
            if len(T1._children) >= 2:
                T_new, T2 = T_new.add_point(T1.root(), T1._is_in_affinoid)
            elif (T1.parent() != None) and (T1.parent()._is_in_affinoid != T1._is_in_affinoid):
                T_new, T2 = T_new.add_point(T1.root(), T1._is_in_affinoid)
            elif (T1._children != []) and (T1._children[0]._is_in_affinoid != T1._is_in_affinoid):
                T_new, T2 = T_new.add_point(T1.root(), T1._is_in_affinoid)
        return T_new



    def union(self, T1):
        r"""
        Construct the tree representing the union of two affinoids.


        INPUT:

        - ``T1`` -- an affinoid tree

        OUTPUT:

        An affinoid tree which represents the union of the affinoids represented
        by T0 = ``self`` and T1.
        """

        T0 = self
        # T = T0.copy()  strangely, this did not work
        T_new = AffinoidTree(self._X)
        for xi0 in T0.vertices():
            T_new, dump = T_new.add_point(xi0, None)
        for xi1 in T1.vertices():
            T_new, dump = T_new.add_point(xi1, None)
        # print "First step of T_new:", T_new.vertices()
        new_out = []
        for subtree in T_new.subtrees():
            xi = subtree.root()
            # print "adding xi =", xi
            xi_in_T0 = T0.is_in_affinoid(xi)
            xi_in_T1 = T1.is_in_affinoid(xi)
            # print xi_in_T0, xi_in_T1
            if xi_in_T0 == xi_in_T1:
                subtree._is_in_affinoid = xi_in_T0
                # print "xi is in union: ", xi_in_T0
                # print
            else:
                subtree._is_in_affinoid = True
                # print "xi is in union!"
                # print
                if subtree.has_parent():
                    parent = subtree.parent()
                    xi0 = parent.root()
                    xi0_in_T0 = T0.is_in_affinoid(xi0)
                    xi0_in_T1 = T1.is_in_affinoid(xi0)
                    if (xi_in_T0 != xi0_in_T0) and (xi0_in_T0 != xi0_in_T1):
                        new_out.append(xi0.point_in_between(xi))
                        # print "we have to exclude ", xi0
        T_new = T_new.add_points([], new_out)
        return T_new


    def intersection(self, T1):
        r"""
        Construct the tree representing the intersection of two affinoids.


        INPUT:

        - ``T1`` -- an affinoid tree

        OUTPUT:

        An affinoid tree which represents the intersection of the affinoids
        represented by T0 = ``self`` and T1.
        """

        T0 = self
        # T = T0.copy()  strangely, this did not work
        T = AffinoidTree(self._X)
        for xi in T0.vertices():
            T, T2 = T.add_point(xi, False)
        for xi in T1.vertices():
            T, T2 = T.add_point(xi, False)
        for subtree in T.subtrees():
            xi = subtree.root()
            subtree._is_in_affinoid = (T0.is_in_affinoid(xi) and
                                       T1.is_in_affinoid(xi))
        return T


    def show(self):
        r""" Display a graphical representation of self.
        """

        G, vertex_dict = self.graph()
        in_list = []
        out_list = []
        for i, xi in vertex_dict.items():
            if self.is_in_affinoid(xi):
                in_list.append(i)
            else:
                out_list.append(i)
            print i, ": ", xi
        # print vertex_dict
        G.show(partition=[in_list, out_list])

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

        EXAMPLES:
        ::

            sage: K = QQ
            sage: vK = pAdicValuation(K, 2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi0 = X.gauss_point()
            sage: xi1 = X.point_from_discoid(x+1, 1)
            sage: xi2 = X.point_from_discoid(x+1, 2)
            sage: xi3 = X.point_from_discoid(2+x, 1, in_unit_disk=False)

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
        if T._is_in_affinoid:
            if T.parent() == None or T.parent()._is_in_affinoid:
                holes = []
            else:
                # possible source of error: root of T is of type I
                holes = [TypeVPointOnBerkovichLine(T.root(), T.parent().root())]
            for T1 in T.children():
                if T1._is_in_affinoid:
                    T1.compute_connected_components(comp_list, new_comp)
                else:
                    holes.append(TypeVPointOnBerkovichLine(T.root(), T1.root()))
                    T1.compute_connected_components(comp_list, [])
            if holes != []:
                new_comp.append(holes)

            if T.parent() == None or not T.parent()._is_in_affinoid:
                # T.root() is the root of a component
                comp_list.append(new_comp)
        else:
            # the root of T does not lie in U
            for T1 in T.children():
                T1.compute_connected_components(comp_list, [])


class AffinoidDomainOnBerkovichLine(SageObject):
    r"""
    The class realizing affinoid domains on a Berkovich line.

    EXAMPLES:

    ::

        sage: K = QQ
        sage: vK = pAdicValuation(K, 2)
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

        comp_str = ""
        for U in self.components():
            comp_str += str(U)
        return "Affinoid with %s components:\n%s"%(self.number_of_components(),
                                                 comp_str)

    def berkovich_line(self):

        return self._X


    def is_contained_in(self, xi):
        r"""
        Check whether ``x`` lies on the affinoid.

        INPUT:

        - ``xi`` -- a point on the Berkovich line underlying the affinoid

        OUTPUT:

        ``True`` if ``xi`` lies on the affinoid, ``False`` otherwise

        """

        return self._T.is_in_affinoid(xi)


    def compute_components(self):

        T = self._T
        comp_list = []
        T.compute_connected_components(comp_list, [])
        self._comp_list = comp_list
        components = []
        for comp in comp_list:
            components.append(ElementaryAffinoidOnBerkovichLine(comp))
        self._components = components


    def components(self):

        if not hasattr(self, "_comp_list"):
            self.compute_components()

        return self._components


    def number_of_components(self):

        return len(self.components())

    def boundary(self):
        r"""
        Return the Shilov boundary of the affinoid.

        The Shilov boundary is a finite set of type-II-points contained in the
        affinoid with the property that the valuative function of every rational
        function which is regular on the affinoid takes a minimum on this set.

        The Shilov boundary is automatically computed when we construct the
        connected components.

        """

        if not hasattr(self, "_comp_list"):
            self.compute_components()
        boundary = []
        for comp in self._comp_list:
            boundary += [b_list[0].boundary_point() for b_list in comp]
        return boundary


    def simplify(self):
        r""" Simplify this affinoid.

        This only changes the internal representation by an "affinoid tree".

        """

        self._T = self._T.simplify()



    def union(self, V):
        r"""
        Return the affinoid which is the union of ``self`` with ``V``.
        """

        T = self._T.union(V._T)
        return AffinoidDomainOnBerkovichLine(T)


    def intersection(self, V):
        r"""
        Return the affinoid which is the intersection of ``self`` with ``V``.
        """
        T = self._T.intersection(V._T)
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

        EXAMPLES:

        ::

            sage: K = QQ
            sage: vK = pAdicValuation(K, 2)
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

        """

        U = self
        T = U._T
        X = U.berkovich_line()
        T0 = T.find_point(xi0)
        assert T0 != None and T0._is_in_affinoid, "xi0 is not a boundary point"
        v0 = xi0.pseudovaluation_on_polynomial_ring()
        Rb = v0.residue_ring()
        psi = Rb.one()
        for T1 in T0.children():
            if not T1._is_in_affinoid:
                eta1 = TypeVPointOnBerkovichLine(xi0, T1.root())
                psi1 = eta1.minor_valuation().uniformizer()
                assert psi1.denominator().is_one(), "psi1 is not a polynomial"
                psi = psi * Rb(psi1.numerator())
        phib = irreducible_polynomial_prime_to(psi)
        phi = v0.lift_to_key(phib)
        xi1 = X.point_from_discoid(phi, Infinity, xi0.is_in_unit_disk())
        assert U.is_contained_in(xi1), "error: xi1 is not contained in U"
        return xi1



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

    EXAMPLES:
    ::

        sage: K = QQ
        sage: vK = pAdicValuation(K, 3)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: ClosedUnitDisk(X)
        Affinoid with 1 components:
        Elementary affinoid defined by
        v(x) >= 0

    """

    def __init__(self, X):

        self._X = X
        T = AffinoidTree(X)
        T = T.add_points([X.gauss_point()], [X.infty()])
        self._T = T


class ElementaryAffinoidOnBerkovichLine(AffinoidDomainOnBerkovichLine):
    r"""
    Return the elementary affinoid corresponding to a boundary list.

    An "elementary affinoid" is a a connected affinoid subdomain of a Berkovich
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

    def __init__(self, boundary_list):

        assert boundary_list != [], "the boundary list must not be empty!"
        # boundary = [ xi_list[0].boundary_point() for xi_list in boundary_list]
        X = boundary_list[0][0].X()
        self._X = X
        boundary = []
        complement = []
        T = AffinoidTree(X)
        for boundary_comp  in boundary_list:
            xi = boundary_comp[0].boundary_point()
            T, T1 = T.add_point(xi, True)
            boundary.append(xi)
            for eta in boundary_comp:
                T, T1 = T.add_point(eta.point_inside_residue_class(), False)
                complement.append(eta)
        self._T = T
        self._comp_list = [boundary_list]
        self._boundary = boundary
        self._complement = complement

    def __repr__(self):

        return "Elementary affinoid defined by %s"%self.inequalities()

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


    EXAMPLES:
    ::

        sage: K = QQ
        sage: vK = pAdicValuation(K, 2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: U = RationalDomainOnBerkovichLine(X, (x^2+2)/x*(x+1)/2)
        Affinoid with 2 components:
        Elementary affinoid defined by
        v(x^2 + 2) >= 3/2
        Elementary affinoid defined by
        v(x + 1) >= 1

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
        self._X = X
        U = AffinoidTree(X)
        xi0 = X.gauss_point()
        T = BerkovichTree(X,xi0)
        T = T.adapt_to_function(f)
        path_list = T.paths()
        for xi1, xi2 in path_list:
            in_list =[]
            out_list= []
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
                xi3 = xi1._X.find_zero(xi1, xi2, f)
                assert xi3.v(f) == 0, "got the wrong value for t!"
                in_list.append(xi3)
            U = U.add_points(in_list, out_list)
        # we test whether U is correct
        for xi in U.vertices():
            assert (xi.v(f) >= 0) == U.is_in_affinoid(xi)
        self._T = U

#-------------------------------------------------------------------------
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
        for e in range(0,d):
            for f in all_polynomials(F, x, e):
                yield x**d+f
