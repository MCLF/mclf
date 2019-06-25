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

sage: from mclf import *
sage: F.<x> = FunctionField(QQ)
sage: X = BerkovichLine(F, QQ.valuation(2))

We can define a valuative function by a rational function on `X`::

sage: f = (x^2+2*x-2)/(2*x-1)
sage: H = ValuativeFunction(X, f)

We check that the value of `H` is the valuation of `f`, at several points::

sage: xi = X.gauss_point()
sage: H(xi), xi.v(f)
(0, 0)
sage: xi = X.infty()
sage: H(xi), xi.v(f)
(-Infinity, -Infinity)
sage: xi = X.point_from_discoid(x, 3)
sage: H(xi), xi.v(f)
(1, 1)

We can also define a valuative function by a pair `(L, a_0)`::

sage: L = [(x - 1, 2/3), (x + 1, 3/2)]
sage: a_0 = -3
sage: H = ValuativeFunction(X, (L, a_0))
sage: xi = X.point_from_discoid( x + 1, 2)
sage: H(xi)
2/3

We can compute the rational domain given by the inequality `H(\xi)\geq 0`::

sage: H.rational_domain()
Affinoid with 2 components:
Elementary affinoid defined by
v(x - 1) >= 9/4
Elementary affinoid defined by
v(x + 1) >= 14/9

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

from sage.all import SageObject, Infinity, sgn
from mclf.berkovich.berkovich_trees import BerkovichTree


class ValuativeFunction(SageObject):
    r""" A valuative function on the Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``f`` -- a nonconstant rational function on `X`, or
               a pair `(L, a_0)`, where `L` is
                 a list of pairs `(g, a)`, or
                 a list of triples `(g, a, [\xi])`, consisting of
                 - a polynomial `g` (element of the function field on `X`)
                 - a nonzero rational number `a`, and *possibly*
                 - a list of type-I-points `[\xi]`, and
                `a_0` -is a rational number
    - ``root`` -- a point of type I or II, or ``None`` (default: ``None``)
    - ``assume_complete_factorization`` -- a Boolean (default: ``False``)

    OUTPUT: If `f` is a rational function, then we create the valuative function
    `H` defined as

    .. MATH::

        H(\xi) := v_K(f(\xi))

    If ``f`` is a pair `(L, a_0)` as above, where `L` is a list of pairs
    `(f_i, a_i)`, then the corresponding valuative function is defined as

    .. MATH::

        H(\xi) := a_0 + \sum_i a_i v(f(\xi)).

    The domain of `H` is either the full Berkovich line `X`, or a
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

    If ``assume_complete_factorization`` is ``True`` then it is assumed that `f`
    is a pair `(L, a_0)`, and that the
    list `L` consists of triples `(f, a, [\xi])`, where the `f` are irreducible
    and pairwise prime, and `[\xi]` is the list of all zeroes of `f`.

    """

    def __init__(self, X, f, root=None, assume_complete_factorization=False):

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

        if not isinstance(f, type(())):
            assert f.parent() is X.function_field(), "f must be an element of the function field of X"
            L = [(f, 1)]
            a_0 = 0
            assume_complete_factorization = False
        else:
            L, a_0 = f

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
                        zeroes = [xi for xi, e in X.prime_divisor(g)]
                        L1.append((g, a*m, zeroes))
                        irreducible_factors.append(g)
            # we have recomputed L and updated a_0 accordingly
            L = L1

        # compute the degree of the valuative function; this is a rational
        # number which is positive (resp. negative) iff the valuative function
        # takes the value -Infinity (resp. +Infinity) in the infinity point.
        degree = sum([a*f.numerator().degree() for f, a, _ in L])
        self._degree = degree

        if root.type() == "I":
            # this means the domain is a degenerate discoid consisting of a
            # single point of type I
            if root.is_infinity():
                if degree > 0:
                    a_0 = -Infinity
                elif degree < 0:
                    a_0 = Infinity
                else:
                    a_0 += sum([a*v_K(f.numerator().leading_coefficient())
                                for f, a, _ in L])
            else:
                a_0 = a_0 + sum([a*root.v(f) for f, a, _ in L])
            L = []
            is_constant = True
        elif only_discoid:
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
            is_constant = (len(L) == 0)
        else:
            # the function is constant on the discoid if L is empty
            is_constant = (len(L) == 0)

        # we compute the list of all endpoints
        if is_constant:
            if a_0 == Infinity or a_0 == -Infinity:
                endpoints = [root]
            else:
                endpoints = []
        else:
            endpoints = []
            for f, a, zeroes in L:
                endpoints += zeroes
            if not degree.is_zero() and self.is_in_domain(infty):
                endpoints.append(infty)

        self._description = (L, a_0)
        self._is_constant = is_constant
        self._endpoints = endpoints

        # if the function is constant, then we are done
        if is_constant:
            self._restrictions = []
        # otherwise we still have to construct the restrictions; they correspond to
        # the clusters formed by the set of endpoints
        else:
            # this may replaced by something more efficient later
            T = BerkovichTree(X, root=root)
            for xi in endpoints:
                T, _ = T.add_point(xi)
            # the roots of the children of T

            # create the restrictions
            # these are themselves valuative functions, restricted to the smallest
            # closed discoid containing all endpoints in one residue disk
            restrictions = []
            for child in T.children():
                new_root = child.root()
                new_subtree = ValuativeFunction(X, (L, a_0), root=new_root,
                                                assume_complete_factorization=True)
                restrictions.append(new_subtree)
            self._restrictions = restrictions

    def __repr__(self):
        return "a valuative function on {}".format(self.domain())

    def berkovich_line(self):

        return self._X

    def root(self):
        return self._root

    def domain(self):
        if self._only_discoid:
            return self.root()
        else:
            return self.berkovich_line()

    def only_discoid(self):
        return self._only_discoid

    def degree(self):
        return self._degree

    def is_constant(self):
        return self._is_constant

    def endpoints(self):
        return self._endpoints

    def restrictions(self):
        return self._restrictions

    def description(self):
        return self._description

    def is_in_domain(self, xi):

        if self._only_discoid:
            return self.root().is_leq(xi)
        else:
            return True

    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity).

        """
        assert self.is_in_domain(xi), "xi must lie in the domain of this function"
        L, a_0 = self.description()
        v_K = self.berkovich_line().base_valuation()
        if not xi.is_infinity():
            return a_0 + sum([a*xi.v(f) for f, a, _ in L])
        else:
            degree = self.degree()
            if degree > 0:
                return -Infinity
            elif degree < 0:
                return Infinity
            else:
                return a_0 + sum([a*v_K(f.numerator().leading_coefficient())
                                  for f, a, _ in L])

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the underlying Berkovich line

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to ``eta``.

        """
        # check that eta lies in the domain!
        assert (self.is_in_domain(eta.boundary_point())
                and self.is_in_domain(eta.point_inside_residue_class())), "eta does not lie in the domain"
        L, a_0 = self.description()
        return sum([a*eta.derivative(f) for f, a, _ in L])

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

        OUTPUT: The first point on the path from `\xi1` and `\xi2` where this
        valuative function has a zero, or ``None`` if no such point exist.

        NOTE:

        We are assuming for the moment that the function `H` is affine on the path
        `[\xi_1,\xi_2]`. As this is true precisely on the edges of the tree
        underlying `H`, we check that both points lie on the same edge and raise
        an error if this is not the case.

        EXAMPLES::

        """

        from sage.all import sgn
        from mclf.berkovich.berkovich_line import TypeIIPointOnBerkovichLine, valuation_from_discoid
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine

        H = self
        X = H.berkovich_line()
        F = X.function_field()
        x = F.gen()
        assert H.is_in_domain(xi1), "xi1 must lie in the domain of this function"
        assert H.is_in_domain(xi2), "xi2 must lie in the domain of this function"
        assert xi1.is_leq(xi2) and not xi2.is_leq(xi1), \
            "xi1 must be strictly smaller than xi2"
        # check that xi1 and xi2 lie on the same edge
        h1 = H(xi1)
        h2 = H(xi2)
        assert (h1 <= 0 and h2 >= 0) or (h1 >= 0 and h2 <= 0),\
            "the values of H at xi1 and xi2 must have different sign"
        if h1 == 0:
            return xi1
        if h2 == 0:
            return xi2
        # in case xi2 is a limit point, we have to make sure that its
        # discoid representation is sufficiently precise to get the sign
        # of xi2.v(f) right:
        if xi2.is_limit_point():
            xi2_approx = xi2.approximation()
            count = 0
            while sgn(H(xi2_approx)) != sgn(h2) and count < 100:
                xi2_approx = xi2.improved_approximation()
                count += 1
            assert count < 100, "could not find sufficient approximation!"
            xi2 = xi2.approximation()   # it is now ok to replace xi2 by an approximation

        if xi2.is_in_unit_disk():
            phi, s2 = xi2.discoid()
            s1 = xi1.v(phi)
            # we are looking for t, s1 < t < s2, such that f has zero valuation
            # at the point xi_t: v(phi) >= t.
            eta = TypeVPointOnBerkovichLine(xi1, xi2)
            m = H.derivative(eta)
            n = eta.derivative(phi)
            # now the function t |--> v_t(f) has slope m/n
            t = s1 - n*h1/m
            xi3 = X.point_from_discoid(phi, t)
        else:
            v1 = xi1.pseudovaluation_on_polynomial_ring()
            v2 = xi2.pseudovaluation_on_polynomial_ring()
            assert hasattr(v2, "phi"), "xi2 = {}, v2 = {}".format(xi2, v2)
            phi = v2.phi()
            s1 = v1(phi)
            eta = TypeVPointOnBerkovichLine(xi1, xi2)
            m = H.derivative(eta)
            n = eta.derivative(phi(1/x))
            t = s1 - n*h1/m
            v3 = valuation_from_discoid(X.base_valuation(), phi, t)
            xi3 = TypeIIPointOnBerkovichLine(X, (v3, 1/x))
        assert H(xi3) == 0
        return xi3

    def rational_domain(self):
        r""" Return the rational domain defined by this function.

        OUTPUT: the rational subdomain of the domain of this function `H`,
        defind by the inequality

        .. MATH::

            H(xi) \geq 0.

        Note: for the moment we assume that the domain of this function is the
        whole Berkovich line.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, QQ.valuation(2))
            sage: H1 = ValuativeFunction(X, 2*x)
            sage: H1.rational_domain()
            Affinoid with 1 components:
            Elementary affinoid defined by
            v(x) >= -1
            sage: H2 = ValuativeFunction(X, x*(x-1)/2)
            sage: H2.rational_domain()
            Affinoid with 2 components:
            Elementary affinoid defined by
            v(x - 1) >= 1
            Elementary affinoid defined by
            v(x) >= 1

        """
        from mclf.berkovich.affinoid_domain import AffinoidDomainOnBerkovichLine
        assert not self.only_discoid(), "the domain must be the whole Berkovich line"
        return AffinoidDomainOnBerkovichLine(self._affinoid_tree())

    def _affinoid_tree(self):
        r""" Return the affinoid tree underlying the rational domain.

        This is a helper function for ``rational_domain()`` which works
        recursively.

        OUTPUT: an affinoid tree `T` with the following properties (`H` is this
        valuative function):

        - `T` is the refinement of the tree underlying H, obtained by adding
          all zeroes of `H` lying on the interior of an edge
        - the flag ``is_in_affinoid`` is set for each vertex according to the
          value of `H` in this point.

        """
        from mclf.berkovich.affinoid_domain import AffinoidTree
        H = self
        X = H.berkovich_line()
        xi0 = H.root()
        xi0_in = (H(xi0) >= 0)
        s0 = H(xi0)
        subtrees = [H1._affinoid_tree() for H1 in H.restrictions()]
        new_subtrees = []
        for T1 in subtrees:
            xi1 = T1.root()
            s1 = H(xi1)
            if sgn(s0)*sgn(s1) < 0:
                xi2 = H.find_zero(xi0, xi1)
                T2 = AffinoidTree(X, root=xi2, children=[T1], parent=None,
                                  is_in_affinoid=True)
                new_subtrees.append(T2)
                T1.make_parent(T2)
            else:
                new_subtrees.append(T1)
        T0 = AffinoidTree(X, root=xi0, children=new_subtrees, parent=None,
                          is_in_affinoid=xi0_in)
        for T1 in new_subtrees:
            T1.make_parent(T0)
        return T0
