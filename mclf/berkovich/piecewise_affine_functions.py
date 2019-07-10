r""" Piecewise affine functions on the Berkovich projective line.
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

Valuative functions are piecewise affine.


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

from sage.all import SageObject, Infinity


class Domain(SageObject):
    r""" A domain in the Berkovich line, defined by inequalities.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``inequalities`` -- a list of pairs `(f, a)`
    - ``strict_inequalities`` -- a list of pairs `(g, b)`

    OUTPUT: the domain of `X` which is the intersection of the domains defined
    by the inequalities

    .. MATH::

        v(f) \leq a, \quad v(g) < b.

    Here `f, g` are assumed to be nonconstant rational functions on `X`, and
    `a`, `b` rational numbers.

    If the ``inequalities`` and ``strict_inequalities`` are both empty then the
    full Berkovich line is returned.

    """

    def __init__(self, X, inequalities, strict_inequalities):
        self._X = X
        self._inequalities = inequalities
        self._strict_inequalities = strict_inequalities

    def __repr__(self):
        if self.is_full_berkovich_line():
            return "the Berkovich line"
        else:
            return "domain defined by {} {}".format(self.inequalities(), self.strict_inequalities())

    def is_in(self, xi):
        r""" Return whether a point lies in this domain.

        INPUT:

        - ``xi`` -- a point of type I, II, or V on the Berkovich line

        OUTPUT: ``True`` if `\xi` lies on this domain.

        Note that `\xi` may also be a point of type V (which is officially not
        a point of the Berkovich line).
        """
        xi_type = xi.type()
        if xi_type == "I" or xi_type == "II":
            return (all([xi.v(f) >= a for f, a in self._inequalities])
                    and all([xi.v(f) > a for f, a in self._strict_inequalities]))
        elif xi_type == "V":
            xi0 = xi.boundary_point()
            for f, a in self._inequalities:
                b = xi0.v(f)
                if b < a or (b == a and xi.derivative(f) < 0):
                    return False
            for f, a in self._strict_inequalities:
                b = xi0.v(f)
                if b < a or (b == a and xi.derivative(f) <= 0):
                    return False
            return True

    def berkovich_line(self):
        return self._X

    def inequalities(self):
        inequalities = "\n"
        for phi, s in self._inequalities:
            inequalities += ("v(" + str(phi) + ") >= " + str(s)) + "\n"
        return inequalities

    def strict_inequalities(self):
        str_inequalities = ""
        for phi, s in self._strict_inequalities:
            str_inequalities += ("v(" + str(phi) + ") > " + str(s)) + "\n"
        return str_inequalities

    def is_full_berkovich_line(self):
        return self._inequalities == [] and self._strict_inequalities == []

    def minimal_point(self):
        assert self.is_full_berkovich_line(), "an arbitrary domain has no minimal point"
        return self.berkovich_line().gauss_point()


class Discoid(Domain):
    r""" Return a closed discoid of the Berkovich line.

    INPUT:

    - ``xi0`` - a point on the Berkovich line `X`
    - ``xi1`` (default: ``None``) -- another point on `X`

    OUTPUT: the discoid `D` consisting of all point on the Berkovich line which
    are greater or equal to `\xi_0`. If `\xi_1` is given, then it is checked
    whether `\xi1` lies in `D`.

    If `\xi_0` is the Gauss point, then `D` is taken to be the closed discoid
    with minimal point `\xi_0`, containing `\xi_1`. If `\xi_1` is not given,
    then `D` is taken to be the closed unit disk.

    EXAMPLES::

    sage: from mclf import *
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, QQ.valuation(2))
    sage: Discoid(X.gauss_point())
    the discoid defined by v(x) >= 0

    """

    def __init__(self, xi0, xi1=None):

        X = xi0.berkovich_line()
        self._X = X
        if xi1 is None:
            phi, s = xi0.discoid()
        else:
            assert xi0.is_leq(xi1), "xi1 must be larger then xi0"
            phi, _ = xi1.discoid()
            s = xi0.v(phi)
        self._minimal_point = xi0
        self._phi = phi
        self._s = s

    def __repr__(self):
        return "the discoid defined by v({}) >= {}".format(self._phi, self._s)

    def is_in(self, xi):
        r""" Return whether the point xi lies in this domain.

        INPUT:

        - ``xi`` -- a point of type I, II or V on the Berkovich line

        OUTPUT: ``True`` if `\xi` lies in this domain, ``False`` otherwise.

        """
        point_type = xi.type()
        if point_type == "I" or point_type == "II":
            return xi.v(self._phi) >= self._s
        elif point_type == "V":
            xi0 = xi.boundary_point()
            return xi0.v(self._phi) >= self._s and xi.derivative(self._phi) >= 0

    def minimal_point(self):
        return self._minimal_point


def open_discoid(xi0, xi1):
    r""" Return an open discoid.

    INPUT:

    - ``xi0``, ``xi1`` -- points on the Berkovich line `X`

    OUTPUT: the open discoid `D` with boundary point `xi_0` which contains `\xi_1`.
    Note that `\xi0` is *not* contained in `D`.

    It is assumed that `\xi_0 < \xi_1`. This means that `D` cannot contain the
    Gauss point.

    EXAMPLES::

    sage: from mclf import *
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, QQ.valuation(2))
    sage: xi0 = X.point_from_discoid(x-1, 1)
    sage: xi1 = X.point_from_discoid(x+1, 2)
    sage: open_discoid(xi0, xi1)
    domain defined by
     v(x + 1) > 1

    """
    from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
    assert xi0.is_leq(xi1) and not xi0.is_equal(xi1), "we must have xi0 < xi1"
    phi, s = TypeVPointOnBerkovichLine(xi0, xi1).open_discoid()
    return Domain(xi0.berkovich_line(), [], [(phi, s)])


def open_annuloid(xi0, xi1):
    r""" Return an open annuloid.

    INPUT:

    - ``xi0``, ``xi1`` -- points of type II on the Berkovich line `X`

    OUTPUT: the open annuloid `A` with boundary points `xi_0` and `\xi_1`.
    Note that `\xi0` and `\xi_1` are *not* contained in `D`.

    It is assumed that `\xi_0 < \xi_1`. This means that `A` cannot contain the
    Gauss point.

    EXAMPLES::

    sage: from mclf import *
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, QQ.valuation(2))
    sage: xi0 = X.point_from_discoid(x-1, 1)
    sage: xi1 = X.point_from_discoid(x+1, 2)
    sage: open_annuloid(xi0, xi1)
    domain defined by
     v(x - 1) > 1
    v(1/(x + 1)) > -2

    """
    from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
    assert xi1.type() == "II", "xi1 must be of type II"
    assert xi0.is_leq(xi1) and not xi0.is_equal(xi1), "we must have xi0 < xi1"
    phi0, s0 = TypeVPointOnBerkovichLine(xi0, xi1).open_discoid()
    phi1, s1 = xi1.discoid()
    return Domain(xi0.berkovich_line(), [], [(phi0, s0), (1/phi1, -s1)])


class DirectedPath(SageObject):
    r""" A directed path on the Berkovic path.

    INPUT:

    - ``xi1``, ``xi2`` -- two points on the Berkovich line such that `\xi1\leq \xi_2`

    OUTPUT: the directed path `\gamma = [\xi_1,\xi_2]`.

    EXAMPLES::

    sage: from mclf import *
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, QQ.valuation(2))

    We can define a path by specifying the initial and the terminal point::

    sage: xi1 = X.point_from_discoid(x, 1)
    sage: xi2 = X.point_from_discoid(x^2 + 4, 5)
    sage: gamma = DirectedPath(xi1, xi2)
    sage: gamma
    path from Point of type II on Berkovich line, corresponding to v(x) >= 1 to Point of type II on Berkovich line, corre
sponding to v(x^2 + 4) >= 5

    We use the *standard parametrization* for a path; it depends on the discoid
    representation of the terminal point::

    sage: gamma.point(3)
    Point of type II on Berkovich line, corresponding to v(x + 2) >= 3/2

    sage: gamma.point(6)
    AssertionError                            Traceback (most recent call last)
    ...
    AssertionError: desired point is not on the path

    Given a path `\gamma=[\xi_1,\xi_2]`, we define its *tube* `D` as follows.
    If `\xi_2` is of type II, then `D` is the open annuloid
    with boundary point points `\xi_1` and `\xi_2`. If `\xi_1` is of type I,
    then `D:=D_{\xi_1}` is the discoid with boundary point `\xi_1`.::

    sage: gamma.tube()

    sage: gamma.is_in_tube(X.gauss_point())
    False

    sage: gamma.is_in_tube(xi2)
    True

    """

    def __init__(self, xi1, xi2):
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        assert xi1.is_leq(xi2), "xi1 must be less or equal to xi2"
        self._initial_point = xi1
        self._terminal_point = xi2
        self._initial_point_is_gauss_point = xi1.is_gauss_point()
        if xi2.is_limit_point():
            self._is_limit_path = True
            xi2 = xi2.approximation(xi1, require_maximal_degree=True)
            # we have to make sure that the degree of the polynomial phi
            # does not increase when updating the approximation;
            # otherwise the standard parametrization of the path would change
        else:
            self._is_limit_path = False
        phi = self._make_phi(xi2)
        s2 = xi2.v(phi)
        s1 = xi1.v(phi)
        self._phi = phi
        self._s1 = s1
        self._s2 = s2
        self._initial_tangent_vector = TypeVPointOnBerkovichLine(xi1, xi2)

    def __repr__(self):
        return "path from {} to {}".format(self.initial_point(),
                                           self.terminal_point())

    def berkovich_line(self):
        r""" Return the Berkovich line on which this path lives. """
        return self._initial_point.berkovich_line()

    def initial_point(self):
        r""" Return the initial point of this path."""
        return self._initial_point

    def terminal_point(self):
        r""" Return the terminal point of this path. """
        return self._terminal_point

    def is_limit_path(self):
        r""" Return whether the terminal point of this path is a limit point.
        """
        return self._is_limit_path

    def tube(self):
        r""" Return the tube around this path.

        Let `\xi_1` be the initial and `\xi_2` be the terminal point of this path.
        Then the *tube* is either the open annuloid with boundary points `\xi_1`
        and `\xi2` (if `\xi_2` is of type II) or the closed discoid with boundary
        point `xi_1` (if `\xi_2` is of type I).

        """
        if hasattr(self, "_tube"):
            return self._tube
        if self.terminal_point().type() == "II":
            tube = open_annuloid(self.initial_point(), self.terminal_point())
        else:
            tube = open_discoid(self.initial_point(), self.terminal_point())
        self._tube = tube
        return tube

    def initial_parameter(self):
        return self._s1

    def terminal_parameter(self):
        if self.is_limit_path():
            return Infinity
        else:
            return self._s2

    def is_parameter(self, t, in_interior=False):
        if in_interior:
            return t > self.initial_parameter() and t < self.terminal_parameter()
        else:
            return t >= self.initial_parameter() and t <= self.terminal_parameter()

    def point(self, t):
        r""" Return the point on the path with given parameter.

        INPUT:

        - ``t`` -- a rational number, or ``Infinity``

        OUTPUT: the point `\xi = \gamma(t)` on this path, with respect to the
        standard parametrization.

        .. Note::

            If this path is a limit path, then the standard paramatrization is
            computed with respect to an approximation of the terminal point.
            The approximation is updated such that `t` is in the domain of the
            parametrization. However, it could happen that updating the
            approximation changes the parametrization.

            This problem will disappear once we implement the flag
            ``require_maximal_degree`` in ``mclf.berkovich.berkovich_line``.

        """
        assert t >= self._s1
        if self.is_limit_path():
            if t == Infinity:
                return self.terminal_point()
            while t > self._s2:
                self._improve_approximation()
        else:
            assert t >= self._s1 and t <= self._s2, "desired point is not on the path"
        X = self.berkovich_line()
        phi = self._phi
        # this is not optimal
        return X.points_from_inequality(phi, t)[0]

    def tangent_vector(self, t):
        r""" Return the tangent vector at a given point.

        INPUT:

        - ``t`` -- a rational number, or `\infty`

        OUTPUT: the type-V-point which is the tangent vector at the point
        `\gamma(t)` in the direction of `\gamma`.

        It is assumed that the point `\gamma(t)` does exist and is not the
        terminal point of `\gamma`.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        return TypeVPointOnBerkovichLine(self.point(t), self.terminal_point())

    def parameter(self, xi):
        r""" Return the parameter of a point on the annulus corresponding to this path.
        """
        if self.is_limit_path():
            if self.terminal_point().is_equal(xi):
                return Infinity
            else:
                self._improve_approximation(xi)
        t = xi.v(self._phi)
        assert t >= self._s1 and t <= self._s2, "xi does not lie on the annulus"
        return t

    def retraction(self, xi):
        r""" Return the retraction of a point in the tube onto the path.
        """
        assert self.is_in_domain(xi), "xi must be in the tube"
        return self.point(self.parameter(xi))

    def is_in_tube(self, xi):
        r""" Check whether the point lies in the tube of this path.
        """
        return self.tube().is_in(xi)

    def is_on_path(self, xi):
        if not self.is_in_tube(xi):
            return False
        else:
            return xi.is_equal(self.retraction(xi))

    def slope(self, eta):
        r""" Return the slope of this path at a given point of type V.

        INPUT:

        - ``eta`` -- a point of type V on the Berkovich line

        OUTPUT: the slope of this path `\gamma` at `\eta`.

        We assume that `\eta` lies in the tube of `\gamma`. The *slope*
        of `\gamma` at `\xi` is the right derivative `dt/ds`, evaluated at the
        retraction of `\xi` to `\gamma`. Here `s` is the *canonical parameter*
        and `t` the *standard parameter*.

        """
        xi = eta.boundary_point()
        t = self.parameter(xi)
        if eta.is_in_residue_class(self.terminal_point()):
            return self.tangent_vector(t).derivative(self._phi)
        else:
            return 0

    def initial_tangent_vector(self):
        return self._initial_tangent_vector

    def initial_slope(self):
        initial_slope = self.initial_tangent_vector().derivative(self._phi)
        if not hasattr(self, "_initial_slope"):
            self._initial_slope = initial_slope
        else:
            if self._initial_slope != initial_slope:
                print "Warning: initial_slope of {} has changed!".format(self)
                self._inititial_slope = initial_slope
        return initial_slope

    def _improve_approximation(self, xi=None):
        xi2 = self.terminal_point()
        if xi is None:
            xi2 = xi2.improved_approximation()
        else:
            xi2 = xi2.approximation(certified_point=xi)
        phi = self._make_phi(xi2)
        s2 = xi2.v(phi)
        s1 = self.initial_point().v(phi)
        assert s1 == self._s1, "Warning: s_1 has changed: before: {}, after: {}".format(s1, self._s1)
        assert phi.numerator().degree() == self._phi.numerator().degree(), "warning: degree of phi has changed!"
        self._phi = phi
        self._s2 = s2

    def _make_phi(self, xi):
        phi, _ = xi.discoid()
        # phi is an irreducible polynomial in x, or is 1/x
        # if phi is a polynomial in x with non-integral roots, we have to
        # change it into a polynomial in 1/x with integral root
        if phi.denominator().degree() == 0:
            X = xi.berkovich_line()
            v_K = X.base_valuation()
            g = phi.numerator()
            if v_K(g.leading_coefficient()) > v_K(g[0]):
                x = X.function_field().gen()
                phi = phi*x**(-g.degree())
        return phi


class AffineFunction(SageObject):
    r""" An affine function on a closed annuloid or a closed discoid.

    INPUT:

    - ``xi1``, ``xi2`` -- points on the Berkovich line `X` such that `\xi_1<=\xi_2`
    - ``a``, ``b`` -- rational numbers

    OUTPUT: the affine function `h` on the domain `D` of the path
    `\gamma = [\xi_1,\xi]` defined by `a` and `b`. If `t:D \to \RR` is the
    standard parametrization, then

    .. MATH::

            h(\xi) := a\cdot r_\gamma(\xi) + b.

    """

    def __init__(self, gamma, a, b):

        self._gamma = gamma
        self._a = a
        self._b = b

    def __repr__(self):
        return "affine function on the tube of the {}, with initial value {}.".format(self.path(), self.initial_value())

    def berkovich_line(self):
        return self._initial_point.berkovich_line()

    def path(self):
        return self._gamma

    def initial_point(self):
        return self.path().initial_point()

    def terminal_point(self):
        return self.path().terminal_point()

    def domain(self):
        return self.path().tube()

    def is_in_domain(self, xi):
        return self.domain().is_in(xi)

    def __call__(self, xi):
        self.path().initial_slope()
        return self._a * self.path().parameter(xi) + self._b

    def initial_value(self):
        if not hasattr(self, "_initial_value"):
            self._initial_value = self(self.initial_point())
        return self._initial_value

    def terminal_value(self):
        if not hasattr(self, "_terminal_value"):
            self._terminal_value = self(self.terminal_point())
        return self._terminal_value

    def derivative(self, eta):
        r""" Return the derivative of this affine function w.r.t. a type V point.

        INPUT:

        - ``eta`` -- a type-V-point on the Berkovich line

        OUTPUT: the derivative of this affine function `h` w.r.t. the tangent
        vector corresponding to `eta`.

        """
        assert self.is_in_domain(eta), "eta must lie in the domain of this function"
        return self._a * self.path().slope(eta)

    def is_constant(self):
        return self._a == 0

    def is_increasing(self):
        return self._a > 0

    def find_zero(self):
        r""" Return an isolated zero of this affine function (if there is one).

        OUTPUT: a point `\xi` on the interior of the path underlying this
        function which is an isolated zero.

        If no such zero exists, ``None`` is returned.

        We note that "isolated" implies that the function is not constant if
        `\xi` exists, and therefore there is at most one such point.

        """
        return self.find_point_with_value(0)

    def find_point_with_value(self, c):
        r""" Return a point where this affine function takes a given value.

        OUTPUT: a point `\xi` on the interior of the underlying path such that
        the function is nonconstant in `\xi` and takes the value `c`.

        If no such point exists, ``None`` is returned.

        """
        a = self._a
        b = self._b
        gamma = self.path()
        if a == 0:
            return None
        else:
            t = (c - b)/a
            if gamma.is_parameter(t, in_interior=True):
                xi = gamma.point(t)
                return xi
            else:
                return None


class PiecewiseAffineFunction(SageObject):
    r""" A piecewise affine function on a domain in the Berkovich line.

    INPUT:

    - ``D`` -- a domain in the Berkovich line
    - ``a0`` -- a rational number
    - ``restrictions`` -- a list of pairs `(h_1,h_2)`

    OUTPUT: a piecewise affine function `h` on `D`.

    We assume that `D` is either a closed discoid, or the full Berkovich line `X`.
    Let `\xi_0` be the *initial point* of the function, which is either the boundary
    point of `D` or, if `D=X`, the Gauss point on `X`.

    The *restrictions* are the restrictions of `h` to proper open subdiscoids
    `D_1` of `D`. It is assumed that `h` is constant, with value `a_0`, on the
    complement of these subdiscoids. The restriction of `h` to `D_1`
    is given by a pair `(h_1, h_2)`, where `h_2` is the restriction of `h`
    to a proper closed subdiscoid `D_2\subset D_1` and `h_1` is the restriction
    of `h` to the open annuloid `D_1\backslash D_2`. It is assumed that `h_1` is
    an *affine* functions, whereas `h_2` is piecewise affine.

    We allow `D_2` to be empty, in which case `h_2` is ``None`` and the domain of
    `h_1` is an open discoid.

    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))

    We can define the "valuative function" of a rational function: ::

        sage: f = (x^2 - 2) / x
        sage: h = valuative_function(X, f)
        sage: h
        piecewise affine function on the Berkovich line, with initial value 0

    A piecewise affine function can be evaluated at any point. ::

        sage: xi = X.point_from_discoid(x, 2)
        sage: h(xi)
        -1
        sage: xi.v(f)
        -1

    A piecewise affine function defines an affininoid subdomain (the point where
    the function takes nonnegative values).

        sage: h.affinoid_domain()
        Affinoid with 1 components:
        Elementary affinoid defined by
        v(1/x) >= -1
        v(x) >= 0

    """

    def __init__(self, D, a0, restrictions):
        from mclf.berkovich.berkovich_line import BerkovichLine
        if isinstance(D, BerkovichLine):
            D = Domain(D, [], [])
        self._domain = D
        self._initial_value = a0
        self._restrictions = restrictions
        self._initial_point = D.minimal_point()

    def __repr__(self):
        return "piecewise affine function on {}, with initial value {}".format(self.domain(), self.initial_value())

    def berkovich_line(self):
        r""" Return the Berkovich line on which this function is defined.
        """
        return self.domain().berkovich_line()

    def initial_point(self):
        r""" Return the initial point of this function.

        This is the minimal point of the domain of this function.
        """
        return self._initial_point

    def domain(self):
        r""" Return the domain of this function.

        """
        return self._domain

    def is_constant(self):
        """ Return whether this function is constant.
        """
        return len(self._restrictions) == 0

    def is_in_domain(self, xi):
        """ Return whether a given point is in the domain of this function.

        """
        return self.domain().is_in(xi)

    def initial_value(self):
        """ Return the value of this function at the initial point.

        """
        return self._initial_value

    def restrictions(self):
        return self._restrictions

    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity).

        """
        assert self.is_in_domain(xi), "xi must lie in the domain of this function"
        if self.is_constant():
            return self.initial_value()
        for h1, h2 in self.restrictions():
            if h1.is_in_domain(xi):
                return h1(xi)
            elif h2 is not None and h2.is_in_domain(xi):
                return h2(xi)
        return self.initial_value()

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the underlying Berkovich line

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to ``eta``.

        NOTE: This needs to be defined in a more precise way.

        """
        # check that eta lies in the domain!
        assert self.is_in_domain(eta), "eta does not lie in the domain"
        for h1, h2 in self.restrictions():
            if h1.is_in_domain(eta):
                return h1.derivative(eta)
            elif h2 is not None and h2.is_in_domain(eta):
                return h2.derivative(eta)
        # the function is constant on the complement of the domains
        # of the restrictions; therefore:
        return 0

    def find_next_zeroes(self, xi0=None):
        r""" Return the next zeroes of this function after a given point.

        INPUT:

        - ``xi0`` (default: ``None``) -- a point in the domain of this function

        OUTPUT: The list of all points in the domain of this function which

        - are zeroes of this function,
        - are not in the constant locus of the function
        - are greater or equal to `\xi_0`, and
        - are minimal with this property.

        If ``xi0`` is ``None`` then the third condition is ignored.

        """
        return self.find_next_points_with_value(0, xi0)

    def find_next_points_with_value(self, a, xi0=None):
        r""" Return the next point where this function takes a given value,
        after a given point.

        INPUT:

        - ``a`` -- a rational number
        - ``xi0`` (default: ``None``) -- a point in the domain of this function

        OUTPUT: The list of all points on the nerf of this function

        - at which this function takes the value `a`,
        - at which the function is not constant,
        - which are strictly greater than `\xi_0`, and
        - which are minimal with this property.

        If ``xi0`` is ``None`` then the second condition is ignored.

        NOTE::

        In this form, the problem is not well defined. Note that the function
        may be constant on pathes of the nerf. If this constant value is equal
        to a, and xi0 lies on this path and ist not the terminal point, then
        there is no minimal next point with value a.

        """
        if xi0 is not None and xi0.is_incomparable(self.initial_point()):
            # no point in the domain of h can be strictly greater than xi0
            return []
        # now we know that xi0 is either None, or comparable to the initial point.

        is_strictly_less = xi0.is_strictly_less(self.initial_point())
        initial_value_is_a = self.initial_value() == a

        ret = []
        for h1, h2 in self.restrictions():
            if (is_strictly_less and not h1.is_in_domain(xi0) and not h2.is_in_domain(xi0)):
                # no point in visiting this branch, since no point there can be
                # strictly less than xi0
                continue
            if h1.is_constant():
                ret += h2.find_next_points_with_value(a, xi0)
                continue
            xi1, _ = h1.next_point_with_value(a)

            if xi1 is None and h2 is not None:
                ret += h2.find_next_points_with_value(a, xi0)
            elif xi1 is not None and xi0.is_strictly_less(xi1):
                ret.append(xi1)
        # if ret is empty this means there are
        if initial_value_is_a and ret == []:
            if xi0 is None or (xi0 is not None and is_strictly_less):
                return [self.initial_point()]
        return ret

    def affinoid_domain(self):
        r""" Return the affinoid domain defined by this function.

        OUTPUT: the affinoid subdomain of the domain of this function `h`,
        defind by the inequality

        .. MATH::

            h(xi) \geq 0.

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
        U = AffinoidDomainOnBerkovichLine(self._affinoid_tree())
        # U.simplify()
        return U

    def _affinoid_tree(self):
        r""" Return the affinoid tree underlying the affinoid domain defined by
        this function.

        This is a helper function for ``rational_domain()`` which works
        recursively.

        OUTPUT: an affinoid tree `T` with the following properties (`h` is this
        valuative function):

        - `T` is the refinement of the tree underlying `h`, obtained by adding
          all zeroes of `h` lying on the interior of an edge
        - the flag ``is_in_affinoid`` is set for each vertex according to the
          value of `h` in this point.

        """
        from mclf.berkovich.affinoid_domain import AffinoidTree
        h = self
        X = h.berkovich_line()
        xi0 = h.initial_point()
        xi0_in = (h(xi0) >= 0)
        subtrees = []
        for h1, h2 in self.restrictions():
            if h2 is not None:
                T1 = h2._affinoid_tree()
                xi2 = h1.find_zero()
                # if xi2 is found, it is an isolated zero on the interior of the
                # path underlying h1
                if xi2 is not None:
                    T2 = AffinoidTree(X, root=xi2, children=[T1], parent=None,
                                      is_in_affinoid=True)
                    subtrees.append(T2)
                    T1.make_parent(T2)
                else:
                    # we may be able to replace T1 be a subtree
                    if T1._is_in_affinoid == xi0_in:
                        while (len(T1.children()) == 1
                               and T1.children()[0]._is_in_affinoid == xi0_in):
                            T1 = T1.children()[0]
                    # or even omit it completely
                    if not(T1._is_in_affinoid == xi0_in and T1.children() == []):
                        subtrees.append(T1)
            else:
                # the terminal point is of type I
                xi1 = h1.terminal_point()
                xi1_in = h1.terminal_value() >= 0
                if xi1_in != xi0_in:
                    xi2 = h1.find_zero()
                    if xi2 is not None:
                        if xi1_in:
                            # since xi2 lies in U, we don't need xi1
                            T1 = AffinoidTree(X, root=xi2, children=[], parent=None,
                                              is_in_affinoid=True)
                            subtrees.append(T1)
                        else:
                            # we need both xi1 and xi2
                            T1 = AffinoidTree(X, root=xi1, children=[], parent=None,
                                              is_in_affinoid=False)
                            T2 = AffinoidTree(X, root=xi2, children=[T1], parent=None,
                                              is_in_affinoid=True)
                            subtrees.append(T2)
                            T1.make_parent(T2)
                    else:
                        # no zeroe on the interior found; one of the endpoints
                        # must be a zero
                        T1 = AffinoidTree(X, root=xi1, children=[], parent=None,
                                          is_in_affinoid=xi1_in)
                        subtrees.append(T1)
        T0 = AffinoidTree(X, root=xi0, children=subtrees, parent=None,
                          is_in_affinoid=xi0_in)
        for T1 in subtrees:
            T1.make_parent(T0)
        return T0


def valuative_function(D, f, T=None):
    r""" A valuative function on a domain in the Berkovich line.

    INPUT:

    - ``D`` -- a domain in the Berkovich line, or the Berkovich line itself
    - ``f`` -- a nonconstant rational function on `X`, or
               a pair `(L, a_0)`, where `L` is
                 a list of pairs `(g, a)` consisting of
                 - a polynomial `g` (element of the function field on `X`)
                 - a nonzero rational number `a`
                and where `a_0` is a rational number
    - ``T`` (default: ``None``) -- a Berkovich tree

    OUTPUT: If `f` is a rational function, then we create the valuative function
    `h` on `D` defined as

    .. MATH::

        h(\xi) := v_K(f(\xi))

    If ``f`` is a pair `(L, a_0)` as above, where `L` is a list of pairs
    `(f_i, a_i)`, then the corresponding valuative function is defined as

    .. MATH::

        h(\xi) := a_0 + \sum_i a_i v(f(\xi)).

    The domain `D` must be either a discoid, or the the full Berkovich line.

    If the Berkovich tree `T` is given, then it is assumed that `T` is the
    *dendrite* of the function `h` on `D`. This means that the root of `T`
    is the minimal point of `D`, and that the restriction of `h` to the edges
    of `T` are affine.

    """
    from mclf.berkovich.berkovich_trees import BerkovichTree
    from mclf.berkovich.berkovich_line import BerkovichLine

    if isinstance(D, BerkovichLine):
        D = Domain(D, [], [])
    X = D.berkovich_line()
    initial_point = D.minimal_point()

    if not isinstance(f, type(())):
        assert f.parent() is X.function_field(), "f must be an element of the function field of X"
        L = [(f, 1)]
        a_0 = 0
    else:
        L, a_0 = f
    L, a_0 = complete_factorization(X, L, a_0)
    initial_value = a_0 + sum([a*initial_point.v(g) for g, a in L])
    assert compute_value(L, a_0, initial_point) == initial_value

    if T is None:
        degree = sum([a*g.numerator().degree() for g, a in L])
        T = BerkovichTree(X, root=initial_point)
        for g, a in L:
            for xi in [xi2 for xi2, m in X.prime_divisor(g)]:
                T, _ = T.add_point(xi)
        if degree != 0:
            T, _ = T.add_point(X.infty())
    restrictions = compute_restrictions(L, a_0, T)
    for h1, _ in restrictions:
        assert h1.initial_point().is_equal(initial_point)
        assert h1.initial_value() == initial_value
    return PiecewiseAffineFunction(D, initial_value, restrictions)


def compute_restrictions(L, a0, T):
    r""" Return the restrictions of a valuative function.

    INPUT:

    - ``L`` -- a list of pairs `(f, a)`, where `f` is an irreducible
      polynomial and `a` a rational number
    - ``a0`` -- a rational number
    - ``T`` -- a Berkovich tree
    - ``degree`` -- an integer

    OUTPUT: a list of pairs `(h_1, h_2)`.

    """
    restrictions = []
    xi0 = T.root()
    for T1 in T.children():
        xi1 = T1.root()
        gamma = DirectedPath(xi0, xi1)
        h1 = restriction_to_path(gamma, L, a0)
        if xi1.type() == "I":
            h2 = None
        else:
            D2 = Discoid(xi1)
            h2 = valuative_function(D2, (L, a0), T=T1)
            assert h1.terminal_point().is_equal(h2.initial_point())
            assert h1.terminal_value() == h2.initial_value(), "h1 = {}, h2 = {}, L = {}, a0 = {}".format(h1, h2, L, a0)
        restrictions.append((h1, h2))
    return restrictions


def restriction_to_path(gamma, L, a0):
    r""" Return the restriction of a valuative function to a directed path.

    INPUT:

    - ``gamma`` -- a directed path
    - ``L`` -- a list of pairs `(f, a)`
    - ``a0`` -- a rational number

    OUTPUT: the valuative function given by `(L, a_0)`, restricted to the
    directed path `\gamma`. It is assumed that this restriction is affine. If it
    is not, an error is raised.

    """
    s = gamma.initial_parameter()
    eta = gamma.tangent_vector(s)
    e = eta.derivative(gamma._phi)
    assert e != 0, "error: gamma = {}, L = {}, s = {}, eta = {}".format(gamma, L, s, eta)
    a = compute_derivative(L, a0, eta)/e
    c = compute_value(L, a0, gamma.initial_point())
    b = c - a*s
    h = AffineFunction(gamma, a, b)
    assert h.initial_value() == c, "a = {}, b = {}, c = {}, gamma ={}, L = {}, a0 = {}".format(a, b, c, gamma, L, a0)
    d = compute_value(L, a0, gamma.terminal_point())
    if a == 0:
        assert d == b, "a = {}, b = {}, c = {}, d ={}, gamma ={}".format(a, b, c, d, gamma)
    else:
        assert d == h.terminal_value(), "a = {}, b = {}, c = {}, d ={}, gamma ={}, L = {}, a0 = {}".format(a, b, c, d, gamma, L, a0)
    return h


def compute_value(L, a0, xi):
    if xi.is_infinity():
        degree = sum([a*f.numerator().degree() for f, a in L])
        if degree < 0:
            return Infinity
        elif degree > 0:
            return -Infinity
        else:
            return a0 + sum([a*xi.v(f.numerator().leading_coefficient()) for f, a in L])
    else:
        return a0 + sum([a*xi.v(f) for f, a in L])


def compute_derivative(L, a0, eta):
    return sum([a*eta.derivative(f) for f, a in L])


# ----------------------------------------------------------------------------
#
#                          Helper functions


def complete_factorization(X, L, a_0):
    r""" refine `(L, a_0)` to a complete factorization.
    """
    v_K = X.base_valuation()
    FField = X.function_field()
    L1 = []
    irreducible_factors = []
    # note that a factor h in irreducible_factor must have the same
    # position as the pair (h, b) in L1
    for f, a in L:
        f = FField(f)
        F = f.factor()
        a_0 = a_0 + a*v_K(F.unit())
        for g, m in F:
            if g in irreducible_factors:
                # the factor g occured before
                i = irreducible_factors.index(g)
                h, b = L1[i]
                assert h == g, "something is wrong!"
                L1[i] = (h, b + a*m)
            else:
                L1.append((g, a*m))
                irreducible_factors.append(g)
    # we have recomputed L and updated a_0 accordingly
    # get rid of trivial factors:
    L1 = [(f, a) for f, a in L1 if a != 0]
    return L1, a_0


def simplify_L(initial_point, L, a_0):
    L1 = []
    for f, a, zeroes in L:
        if all([not initial_point.is_leq(xi) for xi in zeroes]):
            # no root of f lies in the discoid D
            a_0 = a_0 + a*initial_point.v(f)
        else:
            zeroes = [xi for xi in zeroes if initial_point.is_leq(xi)]
            L1.append((f, a, zeroes))
    return L, a_0


def affine_valuative_function(gamma, description):
    r""" Return the affine valuative function with given description.

    INPUT:

    - ``gamma`` -- a directed path
    - ``description`` -- a pair `(L, a_0)` defining a valuative function

    OUTPUT: the valuative function defined by `(L, a_0)`; if it is not affine
    on the path `gamma` then an error is raised.

    """
    L, a_0 = description
