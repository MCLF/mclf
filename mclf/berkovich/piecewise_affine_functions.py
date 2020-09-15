# -*- coding: utf-8 -*-
r"""
Piecewise affine functions on the Berkovich projective line
===========================================================

Let `K` be a field, `v_K` a discrete valuation on `K` and `X=\mathbb{P}^1_K`
the *Berkovich line* over `K`.

A continuous function

.. MATH::

    h: X \to \mathbb{R}\cup\{\pm\infty\}

is called *piecewise affine* if it factors over the retraction map

.. MATH::

    r_T: X \to T

onto a Berkovich subtree `T\subset X`, and the restriction of `h` to the edges
of `T` are affine (with respect to the natural affine structure of a path on a
Berkovich line).

The most important examples of piecewise linear functions are
*valuative functions*. For instance, to any nonzero rational function
`f \in F=K(x)` we associate the function

.. MATH::

    h_f:X \to \mathbb{R}\cup\{\pm\infty\},  \xi \mapsto v_\xi(f).

A general valuative function on `X` is simply a rational multiple of a function
of the form `h_f`. Any such function `h` can be written uniquely in the form

.. MATH::

    h = a_0 + \sum_i a_i\cdot h_{f_i}

where the `f_i` are irreducible polynomials in the parameter `x`,
and the `a_i` are rational numbers, with `a_i \neq 0` for `i > 0`.

Let `h` be a nonconstant piecewise affine function on `X`. Then the subset

.. MATH::

    U := \{ \xi \in X \mid h(\xi) \geq 0 \}

is an affinoid subdomain (unless it is empty, or the full Berkovich line `X`).
If `h=h_f` is the valuative function associated to a rational function `f`, then
`U` is actually a rational domain.


AUTHORS:

- Stefan Wewers (2017-2019)


EXAMPLES::

    sage: from mclf import *
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, QQ.valuation(2))

We can define a valuative function by a rational function on `X`::

    sage: f = (x^2+2*x-2)/(2*x-1)
    sage: h = valuative_function(X, f)

We check that the value of `h` is the valuation of `f`, at several points::

    sage: xi = X.gauss_point()
    sage: h(xi), xi.v(f)
    (0, 0)
    sage: xi = X.infty()
    sage: h(xi), xi.v(f)
    (-Infinity, -Infinity)
    sage: xi = X.point_from_discoid(x, 3)
    sage: h(xi), xi.v(f)
    (1, 1)

We can also define a valuative function by a pair `(L, a_0)`::

    sage: L = [(x - 1, 2/3), (x + 1, 3/2)]
    sage: a_0 = -3
    sage: h = valuative_function(X, (L, a_0))
    sage: xi = X.point_from_discoid(x + 1, 2)
    sage: h(xi)
    2/3

We can compute the affinoid domain given by the inequality `h(\xi)\geq 0`::

    sage: h.affinoid_domain()
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

from sage.all import SageObject, Infinity, cached_method
# from sage.misc.cachefunc import cached_method


class Domain(SageObject):
    r""" A domain in the Berkovich line, defined by inequalities.

    Objects of this class are used as domians of definition of affine and
    piecewise affine functions. Although they may be affinoid domains, this
    class has no relation to the class ``AffinoidDomainOnBerkovichLine``.

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

    @cached_method
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
        """ Return the Berkovich line underlying this domain.
        """
        return self._X

    def inequalities(self):
        """ Return the list of non-strict inequalities which are part of the
        definition of this domain.
        """
        inequalities = ""
        for phi, s in self._inequalities:
            inequalities += + "\n" + ("v(" + str(phi) + ") >= " + str(s))
        return inequalities

    def strict_inequalities(self):
        """ Return the list of strict inequalities which are part of the
        definition of this domain.
        """
        str_inequalities = ""
        for phi, s in self._strict_inequalities:
            str_inequalities += "\n" + ("v(" + str(phi) + ") > " + str(s))
        return str_inequalities

    def is_full_berkovich_line(self):
        """ Return whether this domain is the full Berkovich line.
        """
        return self._inequalities == [] and self._strict_inequalities == []

    def minimal_point(self):
        """ Return the minimal point of this domain.

        Since an arbitrary domain has no minimal point, this method raises
        an error, unless this domain is the full Berkovich line.
        """
        assert self.is_full_berkovich_line(), "an arbitrary domain has no minimal point"
        return self.berkovich_line().gauss_point()

    def contains_infty(self):
        """ Return whether this domain contains the point at infinity.
        """
        if not hasattr(self, "_contains_infty"):
            self._contains_infty = self.is_in(self.berkovich_line().infty())
        return self._contains_infty


class Discoid(Domain):
    r""" Return a closed discoid of the Berkovich line.

    INPUT:

    - ``xi0`` - a point on the Berkovich line `X`
    - ``xi1`` (default: ``None``) -- another point on `X`

    OUTPUT:

    the closed discoid `D` consisting of all point on the Berkovich line which
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
        the closed discoid defined by v(x) >= 0

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
        return "the closed discoid defined by v({}) >= {}".format(self._phi, self._s)

    @cached_method
    def is_in(self, xi):
        r""" Return whether the point xi lies in this closed discoid.

        INPUT:

        - ``xi`` -- a point of type I, II or V on the Berkovich line

        OUTPUT: ``True`` if `\xi` lies in this discoid, ``False`` otherwise.

        """
        point_type = xi.type()
        if point_type == "I" or point_type == "II":
            return xi.v(self._phi) >= self._s
        elif point_type == "V":
            xi0 = xi.boundary_point()
            return xi0.v(self._phi) >= self._s and xi.derivative(self._phi) >= 0

    def minimal_point(self):
        """ Return the minimal point of this closed discoid.
        """
        return self._minimal_point


def open_discoid(xi0, xi1):
    r""" Return an open discoid.

    INPUT:

    - ``xi0``, ``xi1`` -- points on the Berkovich line `X`

    OUTPUT:

    the open discoid `D` with boundary point `xi_0` which contains `\xi_1`.
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

    OUTPUT:

    the open annuloid `A` with boundary points `xi_0` and `\xi_1`.
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
        v(x + 1) > 1
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

    OUTPUT:

    the directed path `\gamma = [\xi_1,\xi_2]`.

    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))

    We can define a path by specifying the initial and the terminal point::

        sage: xi1 = X.point_from_discoid(x, 1)
        sage: xi2 = X.point_from_discoid(x^2 + 4, 5)
        sage: gamma = DirectedPath(xi1, xi2)
        sage: gamma
        path from Point of type II on Berkovich line, corresponding to v(x) >= 1 to Point of type II on Berkovich line, corresponding to v(x^2 + 4) >= 5

    We use the *standard parametrization* for a path; it depends on the discoid
    representation of the terminal point::

        sage: gamma.point(3)
        Point of type II on Berkovich line, corresponding to v(x + 2) >= 3/2

    Given a path `\gamma=[\xi_1,\xi_2]`, we define its *tube* `D` as follows.
    If `\xi_2` is of type II, then `D` is the open annuloid
    with boundary point points `\xi_1` and `\xi_2`. If `\xi_1` is of type I,
    then `D:=D_{\xi_1}` is the discoid with boundary point `\xi_1`.::

        sage: gamma.tube()
        domain defined by
        v(x + 2) > 1
        v(1/(x^2 + 4)) > -5

        sage: gamma.is_in_tube(X.gauss_point())
        False

        sage: gamma.is_in_tube(xi2)
        False

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
        r""" Return the initial parameter of this path.

        OUTPUT:

        a rational number `s_0` such that `\gamma(s_0)` is the initial point
        of this path `\gamma`.

        """
        return self._s1

    def terminal_parameter(self):
        r""" Return the terminal parameter of this path.

        OUTPUT:

        a rational number `s_1` (or `\infty`)` such that `\gamma(s_1)` is the
        terminal point of this path `\gamma`.

        """
        if self.is_limit_path():
            return Infinity
        else:
            return self._s2

    @cached_method
    def is_parameter(self, t, in_interior=False):
        r""" Return whether ``t`` is a valid parameter for this path.

        INPUT:

        - ``t`` -- a rational number, or `\infty`
        - ``in_interior`` -- a boolean (default: ``False``)

        OUTPUT:

        ``True`` if `\gamma(t)` is well defined, else ``False``.

        If ``in_interior`` is ``True`` then we check whether `\gamma(t)` lies
        in the interior of this path (i.e. we exclude the initial and the
        terminal point).

        """
        if in_interior:
            return t > self.initial_parameter() and t < self.terminal_parameter()
        else:
            return t >= self.initial_parameter() and t <= self.terminal_parameter()

    @cached_method
    def point(self, t):
        r""" Return the point on the path with given parameter.

        INPUT:

        - ``t`` -- a rational number, or ``Infinity``

        OUTPUT:

        the point `\xi = \gamma(t)` on this path, with respect to the
        standard parametrization.

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

    @cached_method
    def tangent_vector(self, t):
        r""" Return the tangent vector at a given point.

        INPUT:

        - ``t`` -- a rational number, or `\infty`

        OUTPUT:

        the type-V-point which is the tangent vector at the point
        `\gamma(t)` in the direction of `\gamma`.

        It is assumed that the point `\gamma(t)` does exist and is not the
        terminal point of `\gamma`.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        return TypeVPointOnBerkovichLine(self.point(t), self.terminal_point())

    @cached_method
    def parameter(self, xi):
        r""" Return the parameter of a point on the annulus corresponding to this path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        the parameter `t` such that `\gamma(t)=\xi`. If `\xi` does not lie on
        the path `\gamma` then an error is raised.

        """
        if self.is_limit_path():
            if self.terminal_point().is_equal(xi):
                return Infinity
            else:
                self._improve_approximation(xi)
        t = xi.v(self._phi)
        assert t >= self._s1 and t <= self._s2, "xi does not lie on the annulus"
        return t

    @cached_method
    def retraction(self, xi):
        r""" Return the retraction of a point in the tube onto the path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        the image of the point `\xi` under the retraction map onto the path.

        It is assumed that `\xi` lies in the tube of the path; otherwise an
        error is raised.

        """
        assert self.is_in_tube(xi), "xi must be in the tube"
        return self.point(self.parameter(xi))

    @cached_method
    def is_in_tube(self, xi):
        r""" Return whether a point lies in the tube of this path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        ``True`` is `\xi` lies on the tube of this path, ``False`` otherwise.

        """
        return self.tube().is_in(xi)

    @cached_method
    def is_on_path(self, xi):
        r""" Return whether a point lies on this path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        ``True`` if `\xi=\gamma(t)` for a parameter `t`.
        """
        if not self.is_in_tube(xi):
            return False
        else:
            return xi.is_equal(self.retraction(xi))

    @cached_method
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
        """ Return the slope of this path at the initial point.
        """
        initial_slope = self.initial_tangent_vector().derivative(self._phi)
        if not hasattr(self, "_initial_slope"):
            self._initial_slope = initial_slope
        else:
            if self._initial_slope != initial_slope:
                print("Warning: initial_slope of {} has changed!".format(self))
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

    @cached_method
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

    OUTPUT:

    the affine function `h` on the domain `D` of the path `\gamma = [\xi_1,\xi]`
    defined by `a` and `b`. If `t:D \to \mathbb{R}` is the standard
    parametrization, then

    .. MATH::

            h(\xi) := a\cdot r_\gamma(\xi) + b.

    """

    def __init__(self, gamma, a, b):
        from sage.rings.rational_field import QQ
        self._gamma = gamma
        self._a = QQ(a)
        self._b = QQ(b)

    def __repr__(self):
        return "affine function on the tube of the {}, with initial value {}.".format(self.path(), self.initial_value())

    def berkovich_line(self):
        r""" Return the Berkovich line underlying this affine function.
        """
        return self._initial_point.berkovich_line()

    def path(self):
        r""" Return the path underlying this affine function.
        """
        return self._gamma

    def initial_point(self):
        r""" Return the initial point of the path underlying this affine function.
        """
        return self.path().initial_point()

    def terminal_point(self):
        r""" Return the terminal point of the path underlying this affine function.
        """
        return self.path().terminal_point()

    def domain(self):
        r""" Return the domain of definition of this affine function.
        """
        return self.path().tube()

    def is_in_domain(self, xi):
        r""" Return whether a point is in the domain of definition of this affine function.
        """
        return self.domain().is_in(xi)

    @cached_method
    def __call__(self, xi):
        r""" Return the value of this affine function on a point.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        the value `h(\xi)`, where `h` is this affine function.

        It is assumed that `\xi` lies in the domain of `h`; otherwise an error
        is raised.

        """
        self.path().initial_slope()
        return self._a * self.path().parameter(xi) + self._b

    def initial_value(self):
        r""" Return the initial value of this affine function.
        """
        if not hasattr(self, "_initial_value"):
            self._initial_value = self(self.initial_point())
        return self._initial_value

    def terminal_value(self):
        r""" Return the terminal value of this affine function.
        """
        if not hasattr(self, "_terminal_value"):
            self._terminal_value = self(self.terminal_point())
        return self._terminal_value

    @cached_method
    def derivative(self, eta):
        r""" Return the derivative of this affine function w.r.t. a type V point.

        INPUT:

        - ``eta`` -- a type-V-point on the Berkovich line

        OUTPUT:

        the derivative of this affine function `h` w.r.t. the tangent
        vector corresponding to `\eta`.

        """
        assert self.is_in_domain(eta), "eta must lie in the domain of this function"
        return self._a * self.path().slope(eta)

    def is_constant(self):
        r""" Return whether this affine function is constant.
        """
        return self._a == 0

    def is_increasing(self):
        r""" Return whether this affine function is strictly increasing.
        """
        return self._a > 0

    @cached_method
    def find_zero(self):
        r""" Return an isolated zero of this affine function (if there is one).

        OUTPUT:

        a point `\xi` on the interior of the path underlying this
        function which is an isolated zero.

        If no such zero exists, ``None`` is returned.

        We note that "isolated" implies that the function is not constant if
        `\xi` exists, and therefore there is at most one such point.

        """
        return self.find_point_with_value(0)

    @cached_method
    def find_point_with_value(self, c):
        r""" Return a point where this affine function takes a given value.

        OUTPUT:

        a point `\xi` on the interior of the underlying path such that
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

    OUTPUT:

    a piecewise affine function `h` on `D`.

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
        Elementary affinoid defined by
        v(x) >= 0
        v(1/x) >= -1
        <BLANKLINE>

    """

    def __init__(self, D, a0, restrictions):
        from mclf.berkovich.berkovich_line import BerkovichLine
        from sage.rings.rational_field import QQ
        if isinstance(D, BerkovichLine):
            D = Domain(D, [], [])
        self._domain = D
        self._initial_value = QQ(a0)
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
        r""" Return the restrictions of this piecewise affine functions.

        OUTPUT:

        a list of pairs `(h_1,h_2)`, where `h_1` is an *affine* function which is
        the restriction of this function `h` to an open subannuloid of the domain of
        `h`, and `h_2` is the restriction of `h` to the closed discoid which
        the unique hole of the domain of `h_1`.

        If the domain of `h_1` is an open discoid (so there is no hole), then
        `h_2` is ``None``.

        Together with the initial value, these restrictions define `h`, because
        `h` is constant on the complement of the domains of definitios of these
        restrictions.

        """
        return self._restrictions

    @cached_method
    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity), the value `h(\xi)`.

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

    @cached_method
    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the domain of this function

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to `\eta`.

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

        OUTPUT:

        the affinoid subdomain of the domain of this function `h`,
        defind by the inequality

        .. MATH::

            h(xi) \geq 0.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, QQ.valuation(2))
            sage: h1 = valuative_function(X, 2*x)
            sage: h1.affinoid_domain()
            Elementary affinoid defined by
            v(x) >= -1
            sage: h2 = valuative_function(X, x*(x-1)/2)
            sage: h2.affinoid_domain()
            Affinoid with 2 components:
            Elementary affinoid defined by
            v(x + 1) >= 1
            Elementary affinoid defined by
            v(x) >= 1

        """
        from mclf.berkovich.affinoid_domain import AffinoidDomainOnBerkovichLine
        if not hasattr(self, "_affinoid_domain"):
            self._affinoid_domain = AffinoidDomainOnBerkovichLine(self._affinoid_tree())
        return self._affinoid_domain

    def _affinoid_tree(self):
        r""" Return the affinoid tree underlying the affinoid domain defined by
        this function.

        This is a helper function for ``rational_domain()`` which works
        recursively.

        OUTPUT:

        an affinoid tree `T` with the following properties (`h` is this
        valuative function):

        - `T` is the refinement of the tree underlying `h`, obtained by adding
          all zeroes of `h` lying on the interior of an edge
        - the flag ``is_in`` is set for each vertex according to the
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
                                      is_in=True)
                    subtrees.append(T2)
                    T1.make_parent(T2)
                else:
                    # we may be able to replace T1 be a subtree
                    if T1._is_in == xi0_in:
                        while (len(T1.children()) == 1
                               and T1.children()[0]._is_in == xi0_in):
                            T1 = T1.children()[0]
                    # or even omit it completely
                    if not(T1._is_in == xi0_in and T1.children() == []):
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
                                              is_in=True)
                            subtrees.append(T1)
                        else:
                            # we need both xi1 and xi2
                            T1 = AffinoidTree(X, root=xi1, children=[], parent=None,
                                              is_in=False)
                            T2 = AffinoidTree(X, root=xi2, children=[T1], parent=None,
                                              is_in=True)
                            subtrees.append(T2)
                            T1.make_parent(T2)
                    else:
                        # no zeroe on the interior found; one of the endpoints
                        # must be a zero
                        T1 = AffinoidTree(X, root=xi1, children=[], parent=None,
                                          is_in=xi1_in)
                        subtrees.append(T1)
        T0 = AffinoidTree(X, root=xi0, children=subtrees, parent=None,
                          is_in=xi0_in)
        for T1 in subtrees:
            T1.make_parent(T0)
        return T0


def valuative_function(D, f, T=None, is_factored=False):
    r""" A valuative function on a domain in the Berkovich line.

    INPUT:

    - ``D`` -- a domain in the Berkovich line, or the Berkovich line itself
    - ``f`` -- a nonconstant rational function on `X`, or
               a pair `(L, a_0)`, where `L` is a list of pairs `(g, a)` consisting of

               - a polynomial `g` (element of the function field on `X`)
               - a nonzero rational number `a`

               and where `a_0` is a rational number
    - ``T`` (default: ``None``) -- a Berkovich tree
    - ``is_factored`` -- a boolean (default: ``False``)

    OUTPUT:

    If `f` is a rational function, then we create the valuative function
    `h` on `D` defined as

    .. MATH::

        h(\xi) := v_K(f(\xi))

    If ``f`` is a pair `(L, a_0)` as above, where `L` is a list of pairs
    `(f_i, a_i)`, then the corresponding valuative function is defined as

    .. MATH::

        h(\xi) := a_0 + \sum_i a_i v(f(\xi)).

    The domain `D` must be either a standard closed discoid, or the the full
    Berkovich line.

    If the Berkovich tree `T` is given, then it is assumed that `T` is the
    *dendrite* of the function `h` on `D`. This means that the root of `T`
    is the minimal point of `D`, and that the restriction of `h` to the edges
    of `T` are affine.

    If ``is_factored`` is ``True`` then we assume that `L` is actually a list
    of triples `(f, a, [\xi])`, where the `f` are *irreducible* polynomials,
    and `[\xi]` is the list of all points of type I which are zeroes of `f`.

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
    if not is_factored:
        L, a_0 = _complete_factorization(X, L, a_0)
    else:
        L, a_0 = _simplify_L(D, L, a_0)
    initial_value = a_0 + sum([a*initial_point.v(g) for g, a, zeroes in L])
    assert _compute_value(L, a_0, initial_point) == initial_value

    if T is None:
        degree = sum([a*g.numerator().degree() for g, a, zeroes in L])
        T = BerkovichTree(X, root=initial_point)
        for g, a, zeroes in L:
            for xi in zeroes:
                T, _ = T.add_point(xi)
        if degree != 0 and D.is_in(X.infty()):
            T, _ = T.add_point(X.infty())
    restrictions = _compute_restrictions(L, a_0, T)
    for h1, _ in restrictions:
        assert h1.initial_point().is_equal(initial_point)
        assert h1.initial_value() == initial_value
    h = PiecewiseAffineFunction(D, initial_value, restrictions)
    return h


"""
                         Helper functions
                         ----------------

"""


def _simplify_L(D, L, a_0):
    r""" Return the simplified presentation of a valuative function.

    INPUT:

    - ``D`` -- a domain on the Berkovich line
    - ``L`` -- a list of tripels `(g, m, [\xi])`
    - ``a_0`` -- a rational number

    Here `L`, `a_0` represent a valuative function on a domain containing `D`.

    OUTPUT:

    the simplification of `L`, `a_0` corresponding to the restriction of
    the valuative function to `D`.

    """
    # if D contains infty, then we can't simplify at all:
    if D.contains_infty():
        return L, a_0
    L1 = []
    xi0 = D.minimal_point()
    for g, m, zeroes in L:
        if any(D.is_in(xi) for xi in zeroes):
            L1.append((g, m, zeroes))
        else:
            a_0 += m*xi0.v(g)
    return L1, a_0


def _compute_restrictions(L, a0, T):
    r""" Return the restrictions of a valuative function.

    INPUT:

    - ``L`` -- a list of triples `(f_i, a_i, [\xi])`, where `f_i` is an irreducible
      polynomial, `a_i` a nonzero rational number and `[\xi]` the list of zeroes
      of `f_i`
    - ``a0`` -- a rational number
    - ``T`` -- a Berkovich tree

    OUTPUT:

    a list of pairs `(h_1, h_2)`; these are the *restrictions* of the valuative
    function

    .. MATH::

        h = a_0 + \sum_i a_i\cdot h_{f_i}.

    It is assumed that the Berkovich tree `T` is a dendrite of `h`, i.e. `h`
    factors over the retraction map onto `T` and is affine on the edges of `T`.
    Also, the root of `T` must be the minimal point of the domain of `h`.

    """
    restrictions = []
    xi0 = T.root()
    for T1 in T.children():
        xi1 = T1.root()
        gamma = DirectedPath(xi0, xi1)
        h1 = _restriction_to_path(gamma, L, a0)
        if xi1.type() == "I":
            h2 = None
        else:
            D2 = Discoid(xi1)
            h2 = valuative_function(D2, (L, a0), T=T1, is_factored=True)
            assert h1.terminal_point().is_equal(h2.initial_point())
            assert h1.terminal_value() == h2.initial_value(), "h1 = {}, h2 = {}, L = {}, a0 = {}".format(h1, h2, L, a0)
        restrictions.append((h1, h2))
    return restrictions


def _restriction_to_path(gamma, L, a0):
    r""" Return the restriction of a valuative function to a directed path.

    INPUT:

    - ``gamma`` -- a directed path
    - ``L`` -- a list of pairs `(f, a)`
    - ``a0`` -- a rational number

    OUTPUT:

    the valuative function given by `(L, a_0)`, restricted to the
    directed path `\gamma`. It is assumed that this restriction is affine. If it
    is not, an error is raised.

    """
    s = gamma.initial_parameter()
    eta = gamma.tangent_vector(s)
    e = eta.derivative(gamma._phi)
    assert e != 0, "error: gamma = {}, L = {}, s = {}, eta = {}".format(gamma, L, s, eta)
    a = _compute_derivative(L, a0, eta)/e
    c = _compute_value(L, a0, gamma.initial_point())
    b = c - a*s
    h = AffineFunction(gamma, a, b)
    assert h.initial_value() == c, "a = {}, b = {}, c = {}, gamma ={}, L = {}, a0 = {}".format(a, b, c, gamma, L, a0)
    d = _compute_value(L, a0, gamma.terminal_point())
    if a == 0:
        assert d == b, "a = {}, b = {}, c = {}, d ={}, gamma ={}".format(a, b, c, d, gamma)
    else:
        assert d == h.terminal_value(), "a = {}, b = {}, c = {}, d ={}, gamma ={}, L = {}, a0 = {}".format(a, b, c, d, gamma, L, a0)
    return h


def _compute_value(L, a0, xi):
    if xi.is_infinity():
        degree = sum([a*f.numerator().degree() for f, a, _ in L])
        if degree < 0:
            return Infinity
        elif degree > 0:
            return -Infinity
        else:
            return a0 + sum([a*xi.v(f.numerator().leading_coefficient()) for f, a, _ in L])
    else:
        return a0 + sum([a*xi.v(f) for f, a, _ in L])


def _compute_derivative(L, a0, eta):
    return sum([a*eta.derivative(f) for f, a, _ in L])


def _complete_factorization(X, L, a_0):
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
    L1 = [(g, a) for g, a in L1 if a != 0]
    # compute the zeroes of each factor
    L2 = []
    for g, a in L1:
        zeroes = [xi for xi, m in X.prime_divisor(g)]
        L2.append((g, a, zeroes))
    return L2, a_0
