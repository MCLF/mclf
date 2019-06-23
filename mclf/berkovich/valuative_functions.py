r""" Valuative functions on the Berkovich projective line.
=========================================================

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `X=\mathbb{P}^1_K`
be the projective line over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. We call `X^{an}` the *Berkovich
line* over `K`.

According to [Ber1990], `X^{an}` is a simply connected quasi-polyhedron.
Basically, this means that any two points `\xi_1,\xi_2` are the endpoints
of a unique interval `[\xi_1,\xi_2]\subset X^{an}`. There is a canonical affine
and metric structure on these intervals. So `[\xi_1,\xi_2]\cong [a,b]` such
that '|a-b|' is independent of the choices (if `\xi_1` is a point of type I
then `a=-\infty`, and similar for `\xi_2` and `b`).

Let `T` be a *Berkovich tree* inside `X^{an}`, see ??. Then `T` spans a
metric tree `|T|` inside `X^{an}` (where 'metric' has to be understood properly;
the points of type I lie at 'infinity').  The `edges` of `|T|` are precisely
the intervals between the points corresponding to the adjacent vertices.
Therefore, the edges of `|T|` have a canonical affine structure.

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

In this module we provide a class for working with harmonic functions on the
Berkovich line. Our main algorithms computes, from the input of a finite list
of harmonic functions, a Berkovich tree `T` compatible with all elements of the
list.

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

from sage.all import SageObject, Infinity
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine


class ValuativeFunction(SageObject):
    r""" A valuative function on the Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``L`` -- a list of pairs `(f, a)`, or triples `(f, a, [\xi])`, consisting of
                 - a polynomial `f`
                 - a nonzero rational number `a`, and *possibly*
                 - the list of zeroes of `f`, if ``zeroes_are_given`` is true
    - ``a_0`` -- a rational number
    - ``root`` -- a type-II-point (default: ``None``)
    - ``zeroes_are_given`` -- a Boolean (default: ``False``)
    - ``assume_irreducibility`` -- a Boolean (default: ``True``)

    OUTPUT:

    The harmonic function on the Berkovic line `X`, given by the datum (L, a_0).
    If `L=[(f_1, a_1),\ldots,(f_n,a_n)]` then the corresponding valuative function
    is defined as

    .. MATH::

        H(\xi) := a_0 + \sum_i a_i v(f(\xi)).

    If ``root`` is given, and not equal to the Gauss point, then we only consider
    this function on the closed diskoid with boundary point ``root``. Recall that
    this is the set of all points on the Berkovich line which are `\geq ` to
    ``root`` with respect to the partial ordering.

    If ``root`` is given, and equal to a point of type I (a minimal element),
    then this closed discoid degenerates to a point. In this case, the valuative
    function is given by one value, possibly `\pm \infty`.

    If ``zeroes_are_given`` is ``True`` then it is assumed that ``L`` actually
    consists of *triples* `(f, a, [\xi_1,\ldots,\xi_r])`, where the `\xi_i` are
    the zeroes of `f`.

    If ``assume_irreducibility`` is ``False`` then it is not assumed that the
    polynomials `f` are irreducible.
    """

    def __init__(self, X, L, a_0, root=None, zeroes_are_given=False,
                 assume_irreducibility=True):

        self._X = X
        v_K = X.base_valuation()

        if not assume_irreducibility:
            # factorize the f and recompute (L, a_0)
            assert not zeroes_are_given, "if zeroes are given, then we must assume irreducibility"
            L1 = []
            for f, a in L:
                F = f.factor()
                a_0 = a_0 + a*v_K(F.unit())
                L1 = L1 + [(g, a*m) for g, m in F]
            L = L1

        # compute the degree of the valuative function; this is a rational
        # number which is positive (resp. negative) iff the valuative function
        # takes the value -Infinity (resp. +Infinity) in the infinity point.
        degree = sum([a*f.numerator().degree() for f, a in L])
        self._degree = degree

        if root is None:
            root = X.gauss_point()
        if X.is_gauss_point(root):
            only_discoid = False  # we consider the full Berkovic line X
        else:
            only_discoid = True   # we restrict the function on a closed discoid
        self._root = root
        self._only_discoid = only_discoid

        if not zeroes_are_given:
            L = [(f, a, X.prime_divisor(f)) for f, a in L]

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
            # we can also dismiss the infinity point if it is not contained
            # in our discoid
            infty_is_critical = (not degree.is_zero()) and root.is_leq(X.infty())
        else:
            # the infty point is a critical point iff the degree is not zero
            infty_is_critical = not degree.is_zero()
            # the function is constant on the discoid if L is empty
            is_constant = (len(L) == 0)

        self._infty_is_critical = infty_is_critical
        self._valuative_function = (L, a_0)
        self._is_constant = is_constant

        # if the function is constant, then we are done
        if is_constant:
            self._subtrees = []
        else:
            # find the new branches of the tree;
            # each branch is represented by a pair (eta, endpoints), where eta
            # is a point of type V and endpoints is the list of type-I-points
            # contained in the residue disk corresponding to eta
            if infty_is_critical:
                branches = [(TypeVPointOnBerkovichLine(root, X.infty()),
                             X.infty())]
            else:
                branches = []
            for f, a, zeroes in L:
                for xi in zeroes:
                    new_branch = True
                    for eta, endpoints in branches:
                        if eta.is_in_residue_class(xi):
                            endpoints.append(xi)
                            new_branch = False
                    if new_branch:
                        eta = TypeVPointOnBerkovichLine(root, xi)
                        branches.append((eta, [xi]))

            # create the subtrees corresponding to the branches;
            # these are themselves valuative functions, restricted to the smallest
            # closed discoid containing all endpoints in one residue disk
            subtrees = []
            for eta, endpoints in branches:
                new_root = endpoints[0]
                for xi in endpoints[1:]:
                    new_root = new_root.infimum(xi)
                subtrees.append(ValuativeFunction(X, L, a_0, root=new_root,
                                                  zeroes_are_given=True,
                                                  assume_irreducibility=True))
            self._subtrees = subtrees

    def __repr__(self):
        return "the valuative function on {} given by {}".format(self.domain(),
                                                                 self.description())

    def berkovich_line(self):

        return self._X

    def domain(self):

        pass

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
