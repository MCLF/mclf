r"""
Finite subtrees of the Berkovich projective line

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
subtree `T` contaning `S`. We call `T` the tree *spanned* by `S`.

This module realizes finite subtrees of `X^{an}` as combinatorial objects,
more precisely as *finite rooted combinatorial trees*. So a tree consists
of a root, and a list of subtrees.

AUTHORS:

- Stefan Wewers (2017-02-13): initial version


EXAMPLES::

<Lots and lots of examples>
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



class BerkovichTree(SageObject):
    r"""
    Create a new Berkovich tree `T`.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``root`` -- a point of ``X`` (default: None)
    - ``subtrees`` -- a list of Berkovich trees on ``X`` (default = [])

    OUTPUT:

    A Berkovich tree `T` on `X` with root ``root`` and subtrees ``subtrees``.
    `T` may be empty (no root and no subtrees), but if there are subtrees
    then there must be root.
    """

    def __init__(self, X, root=None, subtrees=[]):

        self._root = root
        self._subtrees = subtrees
        if root == None and subtrees != []:
            raise ValueError, "tree with subtrees must have a root"
        self._X = X
        assert all([self._X == T._X for T in self._subtrees]), "subtrees must live on the same Berkovich line as root"

    def __repr__(self):

        return "Berkovich tree with %s vertices"%len(self.vertices())

    def is_empty(self):

        return self._root == None

    def root(self):
        """ Return the root of the tree."""

        return self._root

    def subtrees(self):
        """ Return the list of all subtrees."""

        return self._subtrees

    def is_leaf(self):
        """ Return True if self is a leaf.
        """

        return self._root != None and self._subtrees == []


    def vertices(self):
        r"""
        Return the list of all vertices.
        """

        vertices = []
        if self._root != None:
            vertices.append(self._root)
        for T in self._subtrees:
            vertices += T.vertices()
        return vertices

    def leaves(self):
        r"""
        Return the list of all vertices.
        """

        leaves = []
        if self.is_leaf():
            leaves.append(self._root)
        else:
            for T in self._subtrees:
                leaves += T.leaves()
        return leaves

    def add_point(self, xi):
        r"""
        Return the tree spanned by self and the point xi.

        INPUT:

        - xi -- A point of type I or II on X

        OUTPUT:

        A new tree T, which is spanned by self and the additional point xi.
        """

        T0 = self
        if T0._root == None:
            T0._root = xi
            return T0       # T0 is the leaf with root xi

        xi0 = T0._root
        if xi0.is_equal(xi):
            return T0   # nothing changes

        if xi0.is_leq(xi):
            # now xi0 < xi
            for i in range(len(T0._subtrees)):
                T1 = T0._subtrees[i]
                xi1 = T1._root
                if xi1.is_leq(xi):
                    # now xi0 < xi1 <= xi
                    T1_new = T1.add_point(xi)
                    T0._subtrees[i] = T1_new
                    return T0
                elif xi.is_leq(xi1):
                    # now xi0 < xi < xi1
                    T1_new = BerkovichTree(T0._X, xi, [T1])
                    T0._subtrees[i] = T1_new
                    return T0
                else:
                    xi2 = xi1.infimum(xi)
                    # note that xi0 <= xi2
                    if not xi0.is_equal(xi2):
                        # now xi0 < xi2
                        T_xi = BerkovichTree(T0._X, xi)
                        T_new = BerkovichTree(T0._X, xi2, [T1, T_xi])
                        T0._subtrees[i] = T_new
                        return T0
            # if we get here, we have to add xi as a new leaf with parent xi0
            T_new = BerkovichTree(T0._X, xi)
            T0._subtrees.append(T_new)
            return T0
        else:
            # now xi0 and xi are uncomparable
            # hence we need a new root
            new_root = xi0.infimum(xi)
            T1 = BerkovichTree(T0._X, xi)
            T_new = BerkovichTree(T0._X, new_root, [T0, T1])
            return T_new

    def print_tree(self, depth=0):
        """ Print the vertices of the tree, with identation corresponding to depth.
        """

        if self._root == None:
            return
        print "___"*depth, " ", self._root
        for T in self._subtrees:
            T.print_tree(depth + 1)
