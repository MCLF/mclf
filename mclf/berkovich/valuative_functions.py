r""" Valuative functions on the Berkovich projective line.
=========================================================

Let `K` be a field, `v_K` a discrete valuation on `K` and `X=\mathbb{P}^1_K`
the *Berkovich line* over `K`.

Let `f in F=K(x)` be a nonzero rational function. We associate to `f`
the function

..MATH::    H_f:X^{an} \to \RR\cup\{\pm\infty\},  \xi \mapsto v_\xi(f).


**Definition:** A *valuative function* on `X^{an}` is a function of the form

..MATH::      H = a_0 + \sum_i a_i\cdot H_{f_i}

where the `f_i` are irreducible polynomials in the parameter `x`,
and the `a_i` are rational numbers, with `a_i \neq 0` for `i > 0`.

Valuative functions are *harmonic* in the sense of [??]. In particular,
given a valuative function `H` on `X^{an}`, there always exists a Berkovich
tree `T` (see ??) such that `H` is an affine function on every edge of `|T|`.
Also, any refinement of `T` has the same property. We call `T` *compatible*
with `H`.

In this module we provide a class for working with valuative functions on the
Berkovich line.

AUTHORS:

- Stefan Wewers (2017-2019)


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

from sage.all import SageObject
from mclf.berkovich.berkovich_trees import BerkovichTree


class ValuativeFunction(SageObject):
    r""" A valuative function on the Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``L`` -- a list of pairs `(f, a)`, or triples `(f, a, [\xi])`, consisting of
                 - a polynomial `f` (element of the function field on `X`)
                 - a nonzero rational number `a`, and *possibly*
                 - a list of type-I-points `[\xi]`
    - ``a_0`` -- a rational number
    - ``root`` -- a point of type I or II, or ``None`` (default: ``None``)
    - ``assume_complete_factorization`` -- a Boolean (default: ``False``)

    OUTPUT:

    The valuative function given by the datum (L, a_0).
    Here `a_0` is a rational number and `L` is a list of pairs `(f_i, a_i)`,
    where `f_i` is a polynomial in the standard parameter on the Berkovich line
    and `a_i` is a nonzero rational number; the corresponding valuative function
    is defined as

    .. MATH::

        H(\xi) := a_0 + \sum_i a_i v(f(\xi)).

    The domain of this function is either the full Berkovich line `X`, or a
    closed discoid `D`.

    If ``root`` is equal to the Gauss point (the default) then the domain is `X`.
    If ``root`` not equal to the Gauss point, then the domain is the closed
    diskoid `D` with boundary point ``root``. Recall that this is the set of all
    points on the Berkovich line which are `\geq ` to ``root`` with respect to
    the partial ordering.

    Note that ``root`` may be a point of type I (a minimal element). If this is
    the case, then the closed discoid degenerates to a single point and the
    valuative function is given by one value, possibly (and typically) equal to
    `\pm \infty`.

    If ``assume_complete_factorization`` is ``True`` then it is assumed that the
    list `L` consists of triples `(f, a, [\xi])`, where the `f` are irreducible
    and pairwise prime, and `[\xi]` is the list of all zeroes of `f`. Otherwise,
    we assume that `L` consists of pairs `(f, a)`.

    """

    def __init__(self, X, L, a_0, root=None, assume_complete_factorization=False):

        self._X = X
        v_K = X.base_valuation()
        infty = X.infty()

        if root is None:
            root = X.gauss_point()
        if root.is_gauss_point():
            only_discoid = False  # we consider the full Berkovic line X
        else:
            only_discoid = True   # we restrict the function on a closed discoid
        self._root = root
        self._only_discoid = only_discoid

        if not assume_complete_factorization:
            # factor the f and recompute (L, a_0); this means also adding
            # the zeroes of each factor
            L1 = []
            irreducible_factors = []
            # note that a factor h in irreducible_factor must have the same
            # position as the pair (h, b) in L1
            for f, a in L:
                F = f.factor()
                a_0 = a_0 + a*v_K(F.unit())
                for g, m in F:
                    if g in irreducible_factors:
                        # the factor g occured before
                        i = irreducible_factors.index(g)
                        h, b, zeroes = L1[i]
                        assert h == g, "something is wrong!"
                        L1[i] = (h, b + a*m, zeroes)
                    else:
                        zeroes = [xi for xi, m in X.prime_divisor(g)]
                        L1.append((g, a*m, zeroes))
                        irreducible_factors.append(g)
            # we have recomputed L and updated a_0 accordingly
            L = L1

        # compute the degree of the valuative function; this is a rational
        # number which is positive (resp. negative) iff the valuative function
        # takes the value -Infinity (resp. +Infinity) in the infinity point.
        degree = sum([a*f.numerator().degree() for f, a, zeroes in L])
        self._degree = degree

        if only_discoid:
            # simplify (L, a_0) by restricting it to the discoid
            L1 = []
            for f, a, zeroes in L:
                if all([not root.is_leq(xi) for xi in zeroes]):
                    # no root of f lies in the discoid D
                    a_0 = a_0 + a*root.v(f)
                else:
                    L1.append((f, a, zeroes))
            L = L1
            # the function is constant on the discoid if L is empty, but also
            # if the discoid is degenerate.
            is_constant = (len(L) == 0 or root.type() == "I")
        else:
            # the function is constant on the discoid if L is empty
            is_constant = (len(L) == 0)

        # we compute the list of all endpoints
        endpoints = []
        for f, a, zeroes in L:
            endpoints += zeroes
        if not degree.is_zero() and self.is_in_domain(infty):
            endpoints.append(infty)
        print endpoints

        self._valuative_function = (L, a_0)
        self._is_constant = is_constant
        self._endpoints = endpoints

        # if the function is constant, then we are done
        if is_constant:
            self._subtrees = []
        # otherwise we still have to construct the subtrees; they correspond to
        # the clusters formed by the set of endpoints
        else:
            # this may replaced by something more efficient later
            T = BerkovichTree(X, root=root)
            for xi in endpoints:
                T, _ = T.add_point(xi)
            # the roots of the children of T

            # create the subtrees
            # these are themselves valuative functions, restricted to the smallest
            # closed discoid containing all endpoints in one residue disk
            subtrees = []
            for child in T.children():
                new_root = child.root()
                new_subtree = ValuativeFunction(X, L, a_0, root=new_root,
                                                assume_complete_factorization=True)
                subtrees.append(new_subtree)
            self._subtrees = subtrees

    def __repr__(self):
        return "the valuative function on {} given by {}".format(self.domain(),
                                                                 self.description())

    def berkovich_line(self):

        return self._X

    def root(self):
        return self._root

    def domain(self):
        if self._only_discoid:
            return self.root()
        else:
            return self.berkovich_line()

    def description(self):
        return self._valuative_function

    def is_in_domain(self, xi):

        if self._only_discoid:
            return self.root().is_leq(xi)
        else:
            return True

    def eval(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity).
        """

        pass

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the underlying Berkovich line

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to ``eta``.

        """
        pass

    def dendrite(self):
        r""" Return the dendrite of this valuative function.

        OUTPUT: the *dendrite* of this valuative function, i.e. the minimal
        subtree of the Berkovich line on which the function is nonconstant.

        """
        pass

    def find_zero(self, xi1, xi2):
        r""" Return the next zero of this valuative function on the given path.

        INPUT:

        - ``xi1``, ``xi2`` -- points on the Berkovich line such that `\xi_1<\xi2`

        OUTPUT: The smallest point between `\xi1` and `\xi2` where this valuative
        function has a zero, or ``None`` if no such zero exist.

        """
        pass
