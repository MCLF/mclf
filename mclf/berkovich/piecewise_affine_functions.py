# -*- coding: utf-8 -*-
r"""
Piecewise affine functions on the Berkovich projective line
===========================================================

Let `K` be a field, `v_K` a discrete valuation on `K` and
`X:=(\mathbb{P}^1_K)^{\rm an}` the *Berkovich line* over `K`.

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

    h_f:X \to \mathbb{R}\cup\{\pm\infty\},  \quad \xi \mapsto v_\xi(f).

A general valuative function on `X` is simply a rational multiple of a function
of the form `h_f`. Any such function `h` can be written uniquely in the form

.. MATH::

    h = a_0 + \sum_i a_i\cdot h_{f_i}

where the `f_i` are irreducible polynomials in the parameter `x`,
and the `a_i` are rational numbers, with `a_i \neq 0` for `i > 0`. We call this
the *prime factorization* of `h`.

Piecewise affine functions are implemented via the class
:class:`PiecewiseAffineFunction`. To construct a valuative function, one can use the
function :meth:`valuative_function`.


Directed paths on the Berkovich line
------------------------------------

The Berkovich line is a *simply connected quasi-polyhedron*. One consequence of
this fact is that for any two points `\xi_1,\xi_2`, there is a unique closed
subset `[\xi_1,\xi_2]\subset X` which is homeomorphic to the closed unit interval
`[0,1]\subset\mathbb{R}` such that `\xi_1,\xi_2` correspond to the two endpoints
of the interval. (If `\xi_1=\xi_2` we set `[\xi_1,\xi_2]:=\{\xi_1\}`.)

For instance, if `T\subset X` is a Berkovich tree, every edge of `T` is the
interval spanned by the two adjacent nodes of `T`.

In the following, we will always assume that the two endpoints are distinct and
comparable with respect to the partial ordering of `X`; we then assume that
`\xi_1 < \xi_2`. The intervall `[\xi_1,\xi_2]` is called a *(directed) path* on
`X`; the points `\xi_1` and `\xi_2` are called  the *initial point* and the
*terminal point* of the path.

The above definition of piecewise affine functions depends on the fact that a
directed path has a natural *affine structure*. By this we mean that there is a
prefered choice of an equivalence class of *parametrizations*, i.e. of order
preserving homeomorphisms

.. MATH ::

    \gamma:[s_1,s_2]\to[\xi_1,\xi_2],

with `s_1,s_2\in\mathbb{Q}\cup\{\infty\}` and `s_1<s_2`. Two such parametrizations
are equivalent if they differ by an affine, strictly increasing isomorphism
between intervals in `\mathbb{R}`.

Throughout we use the *standard parametrization*, defined as follows. (For
simplicity, we assume that `\xi_1,\xi_2` are contained in the standard unit disk.)
If `\xi_2` is a point of type II, then it is the boundary point of a discoid

.. MATH ::

    D_{\xi_2} = D[\phi,s_2] := \{ \xi \mid v_\xi(\phi) \geq s_2 \},

for a monic, irreducible polynomial `\phi\in K[x]` and `s_2\in\mathbb{Q}`,
`s_2\geq 0`. Set `s_1:=v_{\xi_1}(\phi)`. Then

.. MATH::

    \gamma:[s_1,s_2]\to[\xi_1,\xi_2], \quad \gamma(s):=\partial D[\phi, s]

is a parametrization of the path `[\xi_1,\xi_2]`, which does not depend on the
choice of the polynomial. By definition, we have the identity

.. MATH::

    v_{\gamma(s)}(\phi) = s,

valid for all `s\in[s_1,s_2]`.

The above definition can be extended to the case where `\xi_2` is a point of
type one; then `\phi(x)=0` is the defining equation for `\xi_2` and `s_2=\infty`.

We will usually identify the path with its standard parametrization `\gamma`.

Unfortunately, the standard parametrization doesn't have very good 'functorial'
properties. For instance, it is not compatible with restriction to a subinterval
(unless this subinterval has the same terminal point). This creates some
technical problems, e.g.

- if `\xi_2` is a limit point, then we need a sufficiently good
  approximation of `\xi_2` by a discoid `D[\phi,s]` in order to define the
  standard parametrization, even if we only want to study points close to `\xi_1`.
  Luckily, it suffices that `\phi` has maximal degree.
- the stanard parametrization is not compatibel with the derivation of an affine
  function with respect to a type-V-point.

The objects described above are implemented in the module by the class
:class:`DirectedPath`.


Tubes and affine functions
--------------------------

Let `\gamma:[s_1,s_2]\to[\xi_1,\xi_2]` be a directed path, given by its standard
parametrization. Let `\phi` be the irreducible monic polynomial used in the
definition of the parametrization. The *tube* of the path is the open annuloid

.. MATH::

    U_\gamma := \{ \xi \mid s_1 < v_\xi(\phi) < s_2 \}.

Then the map

.. MATH::

    r_\gamma:U_\gamma\to (\xi_1,\xi_2), \quad \xi \mapsto \gamma(v_\xi(\phi)),

is a continous retraction, and does not depend on the choice of the
parametrization.

A continous function `h:U_\gamma\to\mathbb{R}\cup\{\pm\infty\}` is called *affine*
if it factors over the retraction `r_\gamma` in such a way that

.. MATH::

    h(\gamma(t)) = at + b,

for `t\in[s_1,s_2]` and fixed rational numbers `a,b\in\mathbb{Q}`. We see that
tubes (i.e. closed annuloids) are the natural domains of definition for affine
functions, and each affine function can be explicitly determined by two rational
constants `a,b`.

All makes sense if the terminal point of the path `\gamma` is of type I, in which
case we have `s_2=\infty`.

For the implementation of affine functions, see :class:`AffineFunction` and
:func:`create_affine_function`.


Paf domains and general piecewise linear functions
--------------------------------------------------

A subset `D\subset X` is called a *paf domain* if `D=X`, or if `D` is an open or
closed discoid with the property that the boundary point of `D` is also its
infimum. This means that `D=D[\phi,s]` or `D=D(\phi,s)`, where `\phi` is an
irreducible and normalized polynomial, and `s\geq v_0(\phi)`, where `v_0` is the
Gauss valuation.

In our implementation, the domain of a piecewise affine function `h` is always a
paf domain `D`. There are two cases to consider:

- if `D` is *closed* (i.e. the full Berkovich line or a closed discoid)

See :class:`PafDomain` and :class:`PiecewiseAffineFunction`.


Affinoid subdomains defined by piecewise affine functions
---------------------------------------------------------

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

from sage.all import SageObject, Infinity, QQ

# ----------------------------------------------------------------------------

#                            paf domains


class Domain(SageObject):
    r""" A domain in the Berkovich line, defined by inequalities.

    This is a master class for the class :class:`PafDomain`.

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

    If ``inequalities`` and ``strict_inequalities`` are both empty then the
    full Berkovich line is returned.

    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))
        sage: D = Domain(X, [(x, 1)], [(1/x, -2)]); D
        domain defined by
        v(x) >= 1
        v(1/x) > -2
        sage: D.is_in(X.gauss_point())
        False
        sage: D.is_in(X.point_from_discoid(x,1))
        True

    """

    def __init__(self, X, inequalities, strict_inequalities):
        self._X = X
        self._inequalities = inequalities
        self._strict_inequalities = strict_inequalities

    def __repr__(self):
        if self.is_full_berkovich_line():
            return "the Berkovich line"
        else:
            return "domain defined by \n{}\n{}".format(self.inequalities(), self.strict_inequalities())

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

    def contains(self, D):
        r""" check whether this domain contains another one.

        INPUT:

        - ``D`` - a domain on the Berkovich line


        """
        raise NotImplementedError()

    def berkovich_line(self):
        """ Return the Berkovich line underlying this domain.
        """
        return self._X

    def inequalities(self):
        """ Return the list of non-strict inequalities which are part of the
        definition of this domain.
        """
        inequalities = []
        for phi, s in self._inequalities:
            inequalities.append('v({}) >= {}'.format(phi, s))
        return "\n".join(inequalities)

    def strict_inequalities(self):
        """ Return the list of strict inequalities which are part of the
        definition of this domain.
        """
        str_inequalities = []
        for phi, s in self._strict_inequalities:
            str_inequalities.append('v({}) > {}'.format(phi, s))
        return "\n".join(str_inequalities)

    def is_full_berkovich_line(self):
        """ Return whether this domain is the full Berkovich line.
        """
        return self._inequalities == [] and self._strict_inequalities == []

    def contains_infty(self):
        """ Return whether this domain contains the point at infinity.
        """
        if not hasattr(self, "_contains_infty"):
            self._contains_infty = self.is_in(self.berkovich_line().infty())
        return self._contains_infty

    def closed_subdiscoid(self, xi):
        r""" Return the closed subdiscoid of this paf domain.

        INPUT:

        - ``xi`` -- a point on this paf domain

        OUTPUT:

        The closed paf subdomain with boundary point `\xi`.

        This is unique, exept if ``self`` is the full Berkovich line and `\xi`
        is the Gauss point. In this case, we return the full Berkovich line.

        """
        assert self.is_in(xi), "xi must be contained in this domain"
        if not xi.is_gauss_point():
            return ClosedPafDomain(xi)
        else:
            # this can only happen if self is closed and contains the Gauss point
            return self


class PafDomain(Domain):
    r"""

    This is the master class for :class:`ClosedPafDomain` and :class:`OpenPafDomain`.

    """

    def is_full_berkovich_line(self):
        return self._is_full_berkovich_line

    def initial_point(self):
        """ Return the initial point of this domain.
        """
        return self._initial_point

    def is_closed(self):
        raise NotImplementedError()

    def is_open(self):
        raise NotImplementedError()

    def point_in_interior(self):
        r""" Return some point from the interior of this domain.
        """
        X = self.berkovich_line()
        return X.points_from_inequality(self._phi, Infinity)[0]


class ClosedPafDomain(PafDomain):
    r""" Return a closed paf domain of the Berkovich line.

    INPUT:

    - ``xi0`` - a point on the Berkovich line `X`
    - ``xi1`` (default: ``None``) -- another point on `X`

    OUTPUT:

    the closed discoid `D` consisting of all point on the Berkovich line which
    are greater or equal to `\xi_0`. If `\xi_1` is given, then it is checked
    whether `\xi1` lies in `D`.

    If `\xi_0` is the Gauss point, then `D` is taken to be the closed discoid
    with minimal point `\xi_0`, containing `\xi_1`. If `\xi_1` is not given,
    then `D` is taken to be the full Berkovich line.

    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))
        sage: D1 = ClosedPafDomain(X.gauss_point()); D1
        the full Berkovich line
        sage: D2 = ClosedPafDomain(X.gauss_point(), X.point_from_discoid(1/x, 1)); D2
        the closed discoid defined by v(1/x) >= 0
        sage: D1.contains(D2)
        True
        sage: D2.contains(D1)
        False

    """

    def __init__(self, xi0, xi1=None):

        assert xi0.type() == "II", "xi0={} must be a point of type II".format(xi0)
        X = xi0.berkovich_line()
        self._X = X
        self._initial_point = xi0
        if xi1 is None and xi0.is_gauss_point():
            self._is_full_berkovich_line = True
        else:
            self._is_full_berkovich_line = False
            if xi1 is None:
                phi, s = xi0.discoid()
            else:
                assert xi0.is_leq(xi1), "xi1 must be larger then xi0"
                phi, _ = xi1.discoid()
                s = xi0.v(phi)
            self._phi = phi
            self._s = s

    def __repr__(self):
        if self.is_full_berkovich_line():
            return "the full Berkovich line"
        else:
            return "the closed discoid defined by v({}) >= {}".format(self._phi, self._s)

    def is_closed(self):
        return True

    def is_open(self):
        return False

    def is_in(self, xi):
        r""" Return whether the point xi lies in this closed discoid.

        INPUT:

        - ``xi`` -- a point of type I, II or V on the Berkovich line

        OUTPUT: ``True`` if `\xi` lies in this discoid, ``False`` otherwise.

        """
        if self.is_full_berkovich_line():
            return True
        point_type = xi.type()
        if point_type == "I" or point_type == "II":
            return xi.v(self._phi) >= self._s
        elif point_type == "V":
            xi0 = xi.boundary_point()
            return xi0.v(self._phi) >= self._s and xi.derivative(self._phi) >= 0

    def contains(self, D):
        r""" Check whether this paf domain contains another one.

        INPUT:

        - ``D`` - a paf domain on the Berkovich line

        This domain is closed; therefore it contains `D` iff it contains its
        initial point - unless this initial point is the Gauss point.

        If the initial point of `D` is the Gauss point, then we need further checks.

        """
        if not D.initial_point().is_gauss_point():
            return self.is_in(D.initial_point())
        elif not self.initial_point().is_gauss_point():
            return False
        elif self.is_full_berkovich_line():
            return True
        elif D.is_full_berkovich_line():
            return False
        else:
            # self and D must be equal
            raise NotImplementedError()

    def residue_class(self, xi):
        r""" Return the residue class of xi on this closed paf domain.

        INPUT:

        - ``xi`` -- a point in the interior of this closed domain

        OUTPUT:

        the residue class of `\xi`, as an open paf domain.

        """
        if not self.initial_point().is_strictly_less(xi):
            print(self)
            print(xi)
            print(self.initial_point())
        return OpenPafDomain(self.initial_point(), xi)


class OpenPafDomain(PafDomain):
    r""" Return an open paf domain of the Berkovich line.

    INPUT:

    - ``xi0`` -- a point on the Berkovich line `X`
    - ``xi1`` -- another point, strictly greater then `\xi_0`

    OUTPUT:

    the open discoid `D` with infimum `\xi_0` and containing the point `\xi_1`.


    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))
        sage: OpenPafDomain(X.gauss_point(), X.point_from_discoid(x+1, 1))
        the open discoid defined by v(x + 1) > 0

    """

    def __init__(self, xi0, xi1):

        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        assert xi0.type() == "II", "xi0={} must be a point of type II".format(xi0)
        X = xi0.berkovich_line()
        self._X = X
        self._is_full_berkovich_line = False
        self._initial_point = xi0
        assert xi0.is_strictly_less(xi1), "xi0 has to be strictly less than xi1"
        phi, s = TypeVPointOnBerkovichLine(xi0, xi1).open_discoid()
        self._phi = phi
        self._s = s

    def __repr__(self):
        return "the open discoid defined by v({}) > {}".format(self._phi, self._s)

    def is_closed(self):
        return False

    def is_open(self):
        return True

    def is_in(self, xi):
        r""" Return whether the point xi lies in this open discoid.

        INPUT:

        - ``xi`` -- a point of type I, II or V on the Berkovich line

        OUTPUT: ``True`` if `\xi` lies in this discoid, ``False`` otherwise.

        """
        point_type = xi.type()
        if point_type == "I" or point_type == "II":
            return xi.v(self._phi) > self._s
        elif point_type == "V":
            xi0 = xi.boundary_point()
            return xi0.v(self._phi) > self._s and xi.derivative(self._phi) >= 0

    def contains(self, D):
        r""" Check whether this paf domain contains another one.

        INPUT:

        - ``D`` - a paf domain on the Berkovich line

        This domain is open; therefore it contains `D` iff it contains its
        initial point.

        """
        return self.is_in(D.initial_point())

    def initial_tangent_vector(self):
        r""" Return the initial tangent vector of this open discoid.

        """
        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
        return TypeVPointOnBerkovichLine(self.initial_point(), self.point_in_interior())


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

# -----------------------------------------------------------------------------


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

    .. TODO::

        At the moment, computing a point `\gamma(t)` can be quite expensive,
        because every time the representation of `v_{\gamma(t)}` as an augmented
        valuation has to be computed again. This could be improved by remembering
        all augmentation steps of the valuation corresponding to (a sufficient
        approximation of) the terminal point.

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
        and `\xi2` (if `\xi_2` is of type II) or the open discoid with boundary
        point `xi_1` (if `\xi_2` is of type I).

        """
        if hasattr(self, "_tube"):
            return self._tube
        if self.terminal_point().type() == "II":
            tube = open_annuloid(self.initial_point(), self.terminal_point())
        else:
            tube = OpenPafDomain(self.initial_point(), self.terminal_point())
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

    def parameter(self, xi):
        r""" Return the parameter of a point on the annulus corresponding to this path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        the parameter `t` such that `\gamma(t)=\xi`. If `\xi` does not lie on
        the closed tube of the path `\gamma` then an error is raised.

        """
        if self.is_limit_path():
            if self.terminal_point().is_equal(xi):
                return Infinity
            else:
                self._improve_approximation(xi)
        t = xi.v(self._phi)
        assert t >= self._s1 and t <= self._s2, "xi does not lie on the tube of this path"
        return t

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

    def is_in_tube(self, xi):
        r""" Return whether a point lies in the tube of this path.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        ``True`` if `\xi` lies on the tube of this path, ``False`` otherwise.

        """
        return self.tube().is_in(xi)

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
            assert self._initial_slope == initial_slope, "Warning: initial_slope of {} has changed!".format(self)
        return initial_slope

    def _improve_approximation(self, xi=None):
        xi2 = self.terminal_point()
        if xi is None:
            xi2.improved_approximation()
        else:
            xi2.approximation(certified_point=xi)
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

# ------------------------------------------------------------------------------


class DataForPiecewiseAffineFunction(SageObject):
    r""" Data defining a piecewise affine function.

    This is an abstract base class for an object that contains the data defining
    a piecewise affine function. It must provide the following methods:

    - paf:
    - domain:
    - initial_point:
    - initial_value:
    - initial_slope:
    - is_constant:
    - is_increasing:
    - is_decreasing:
    - affine_base:
    - restrictions:

    The idea is that some of this information can be computed without developping
    the whole tree of the function.

    Upon creation, an object of this class stores the data by which it is defined,
    and creates the function itself. The particular class realizing the function
    depends on the given data, more specifically on the domain:

    - if the domain `D` is *closed* (i.e. it is either the full Berkovich line,
      or a closed discoid whose boundary point is also its infimum), then we
      invoke the class :class:`PiecewiseAffineFunctionWithBoundary`
    - if the domain D is an open affinoid then we invoke the class
      :class:`PiecewiseAffineFunctionWithoutBoundary`

    If `D` satisfies neither of these conditions then an error is raised.

    At the moment, the only child class is :class:`DataForValuativeFunction`.

    """


class DataForValuativeFunction(DataForPiecewiseAffineFunction):
    r"""  Data defining a valuative function.

    The data defining a valuative function consists of a domain `D`, a list of
    pairs `(h_i,a_i)`, where the `h_i` represent so-called *prime valuative functions*
    and `a_i` are nonzero rational numbers, and a rational number `a_0`.
    The resulting function is then

    .. MATH::

        h:D\to \mathbb{R}\cup\{\pm\infty\}, \quad \xi \mapsto a_0 + \sum_i a_i h_i.

    The main function of this object is to simplify the data and to compute the
    base and the restrictions of the function `h`. This is done in a lazy way.

    INPUT:

    - ``D`` -- a domain on the Berkovich line
    - ``factors`` -- a list of pairs `(h_i, a_i)`, where `h_i` is a prime valuative
                     function and `a_i` is a nonzero rational number
    - ``a_0`` -- a rational number

    It is assumed that the functions `h_i` are pairwise distinct and nonconstant
    on `D`.

    OUTPUT:

    a lazy implementation of the valuative function

    .. MATH::

        h:D\to \mathbb{R}\cup\{\pm\infty\}, \quad \xi \mapsto a_0 + \sum_i a_ih_i(\xi).

    EXAMPLES::

        sage: from mclf import *
        sage: FX.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(FX, QQ.valuation(2))
        sage: h = PrimeValuativeFunction(X, x^2+x/2+1/2)
        sage: g = DataForValuativeFunctionOnClosedDomain(X, [(h,1/2)], -1); g
        data for a valuative function on the full Berkovich line
        sage: g.critical_subdomains()
        [the open discoid defined by v(1/x) > 0,
         the open discoid defined by v(x + 1) > 0]
        sage: g.is_constant()
        False
        sage: g.initial_value()
        -3/2
        sage: g.restrictions()
        [data for a valuative function on the open discoid defined by v(1/x) > 0,
         data for a valuative function on the open discoid defined by v(x + 1) > 0]
        sage: g.poles()
        [Point of type I on Berkovich space approximated by v(2*x + 1) >= 1, with equation 4*x^2 + 2*x + 2 = 0,
         Point of type I on Berkovich space approximated by v(x + 1) >= 1, with equation 4*x^2 + 2*x + 2 = 0,
         The point at infinity on the Berkovich line]

    """

    def __repr__(self):
        return "data for a valuative function on {}".format(self.domain())

    def paf(self):
        r""" Return the piecewise affine function represented by this data.

        """
        return self._paf

    def domain(self):
        r""" Return the domain of the function represented by this data.

        The output is an instance of the class :class:`PafDomain`.
        """
        return self._domain

    def factors(self):
        r""" Return the factors of the valuative function represented by this data.

        The out put is a list of pairs `(h,a)` where `h` is an instance of
        :class:`PrimeValuativeFunction` and `a` a nonzero rational number.

        """
        return self._factors

    def initial_point(self):
        r""" Return the initial point of the domain of the function represented by this data.
        """
        return self.domain().initial_point()

    def initial_value(self):
        r""" Return the initial value of the function represented by this data.
        """
        if not hasattr(self, "_initial_value"):
            self._initial_value = self._a_0 + sum([a*h.initial_value()
                                                  for h, a in self.factors()])
        return self._initial_value

    def is_constant(self):
        r""" Return whether the function represented by this data is constant.

        """
        # the function is constant iff it has no poles.
        return len(self.poles()) == 0

    def is_increasing(self):
        r""" Return whether the function represented by this data is increasing.

        It is tested whether the multiplicity of every pole of the function is
        positive. Since a valuative function is harmonic, this guarantees that
        is is monotonically increasing.
        """
        return all([a > 0 for xi, a in self.poles(multiplicities=True)])

    def is_decreasing(self):
        r""" Return whether the function represented by this data is decreasing.

        It is tested whether the multiplicity of every pole of the function is
        negative. Since a valuative function is harmonic, this guarantees that
        is is monotonically increasing.
        """
        return all([a < 0 for xi, a in self.poles(multiplicities=True)])

    def poles(self, multiplicities=False):
        r""" Return the list of all poles of this valuative function.

        INPUT:

        - ``multiplicities`` -- a boolean (default: ``False``)

        OUTPUT:

        the list of poles of this valuative function. These are the points `\xi`
        (of type I) in the domain where the function takes the value `\pm\infty`.

        If ``multiplicities`` is ``True`` then the output consists of a list of
        pairs `(\xi,a)`, where `\xi` is a pole and `a` is its *multiplicity*.
        The latter is a nonzero rational number.

        """
        poles = []
        for h, a in self.factors():
            if multiplicities:
                poles += [(xi, a) for xi in h.poles()]
            else:
                poles += [xi for xi in h.poles()]
        b = sum([-a*h.degree() for h, a in self.factors()])
        infty = self.domain().berkovich_line().infty()
        if b != 0 and self.domain().is_in(infty):
            if multiplicities:
                poles.append((infty, b))
            else:
                poles.append(infty)
        return poles

    def restriction(self, D):
        r""" Return the data for the restriction of this function to D.

        INPUT:

        - ``D`` -- a paf domain contained in the domain of this function

        OUTPUT:

        the data corresponding to the restriction of this function to `D`.

        """
        # assert self.domain().contains(D), "D must be contained in the domain of this function"
        factors = [(h.restriction(D), a) for h, a in self.factors()]
        if D.is_closed():
            return DataForValuativeFunctionOnClosedDomain(D, factors, self._a_0)
        else:
            return DataForValuativeFunctionOnOpenDomain(D, factors, self._a_0)

    def affine_base(self):
        raise NotImplementedError()

    def restrictions(self):
        r""" Return the restrictions of this paf.

        The *restrictions* of a piecewise affine function are its restrictions
        to the critical subdomians.

        """
        if not hasattr(self, "_restrictions"):
            critical_subdomains = self.critical_subdomains()
            restrictions = []
            for D in critical_subdomains:
                restrictions.append(self.restriction(D))
            self._restrictions = restrictions
        return self._restrictions


class DataForValuativeFunctionOnClosedDomain(DataForValuativeFunction):
    r""" Data defining a valuative function on a closed paf domain.

    This is a subclass of ``DataForValuativeFunction``.

    INPUT:

    - ``D`` -- a closed paf domain on the Berkovich line
    - ``factors`` -- a list of pairs `(h_i, a_i)`, where `h_i` is a prime valuative
               function and `a_i` is a nonzero rational number
    - ``a_0`` -- a rational number

    It is assumed that the functions `h_i` are pairwise distinct and nonconstant.

    OUTPUT:

    a lazy implementation of the valuative function

    .. MATH::

        h:D\to \mathbb{R}\cup\{\pm\infty\}, \xi \mapsto a_0 + \sum_i a_ih_i(\xi).

    """

    def __init__(self, D, factors, a_0):
        from mclf.berkovich.berkovich_line import BerkovichLine
        if isinstance(D, BerkovichLine):
            D = ClosedPafDomain(D.gauss_point())
        else:
            assert isinstance(D, ClosedPafDomain), "D must be a closed paf domain"
        self._domain = D
        self._factors = factors
        self._a_0 = a_0

        if D.is_closed():
            self._paf = PiecewiseAffineFunctionOnClosedDomain(self)
        else:
            raise ValueError("the domain D is not a closed paf domain")

    def critical_subdomains(self):
        r""" Return the critical subdomains of this paf.

        The *critical subdomains* of a valuativ function on a closed paf domain `D`
        are the distinct residue classes on `D` containing the poles of the function.
        """
        if hasattr(self, "_critical_subdomains"):
            return self._critical_subdomains
        D = self.domain()
        critical_subdomains = []
        for xi in self.poles():
            # test whether xi lies in one of the critical domains already found
            xi_is_in_domain_already_found = False
            for D1 in critical_subdomains:
                if D1.is_in(xi):
                    xi_is_in_domain_already_found = True
                    break
            if not xi_is_in_domain_already_found:
                critical_subdomains.append(D.residue_class(xi))
        self._critical_subdomains = critical_subdomains
        return critical_subdomains


class DataForValuativeFunctionOnOpenDomain(DataForValuativeFunction):
    r""" Data defining a valuative function on an open domain.

    This is a subclass of ``DataForValuativeFunction``.

    INPUT:

    - ``D`` -- an open paf domain
    - ``factors`` -- a list of pairs `(h_i, a_i)`, where `h_i` is a prime valuative
               function on `D` and `a_i` is a nonzero rational number
    - ``a_0`` -- a rational number

    It is assumed that the functions `h_i` are pairwise distinct and nonconstant.
    If the h_i are not pairwise distinct, this may lead to an error!

    OUTPUT:

    a lazy implementation of the valuative function

    .. MATH::

        h:D\to \mathbb{R}\cup\{\pm\infty\}, \xi \mapsto a_0 + \sum_i a_ih_i(\xi).

    """

    def __init__(self, D, factors, a_0):
        assert isinstance(D, OpenPafDomain), "D must be an open paf domain"
        self._domain = D
        self._factors = factors
        self._a_0 = a_0

        if D.is_open():
            self._paf = PiecewiseAffineFunctionOnOpenDomain(self)
        else:
            raise ValueError("the paf domain D is not open")

    def affine_base(self):
        r""" Return the affine base of the valuative function represented by this data.
        """
        if not hasattr(self, "_affine_base"):
            xi1 = self.initial_point()
            c1 = self.initial_value()
            if len(self.critical_subdomains()) > 0:
                xi2 = self.critical_subdomains()[0].initial_point()
                c2 = self.restrictions()[0].initial_value()
            else:
                # this should only happen if the function has exactly one pole
                assert len(self.poles()) == 1, "This should not happen!"
                xi2 = self.poles()[0]
                c2 = self.initial_slope()
            self._affine_base = create_affine_function(xi1, xi2, c1, c2)
        return self._affine_base

    def critical_subdomains(self):
        r""" Return the critical subdomains of the paf represented by this data.

        OUTPUT:

        a list containing all *critical subdomains*; this list can have at most
        one entry.

        If the function is constant, then there are no critical subdomain.
        Otherwise, the *critical domain* of a valuative function on an open
        discoid `D` is the smallest closed subdiscoid `D_1\subset D` containing
        all the poles of the function.

        If the function has exactly one pole, there is also no critical subdomain.

        """
        poles = self.poles()
        if len(poles) == 1:
            return []
        # we compute the infimum of all poles
        inf = poles.pop()
        for xi in poles:
            inf = inf.infimum(xi)
        # we return the closed subdiscoid with boundary point inf
        return [self.domain().closed_subdiscoid(inf)]
        # here an error can occur when inf is of type I
        # this can only happen if the same pole is listed several times;
        # this must not happen!

    def initial_slope(self):
        r""" Return the initial slope of the function represented by this data.

        """
        if not hasattr(self, "_initial_slope"):
            eta = self.domain().initial_tangent_vector()
            self._initial_slope = sum([a*h.derivative(eta)
                                       for h, a in self.factors()])
        return self._initial_slope


class PrimeValuativeFunction(SageObject):
    r""" An object representing an irreducible valuative function.

    Let `D` be a paf domain. A function `h:D\to\mathbb{R}\cup\{\infty\}`
    is called a *prime valuative function* if there exists an irreducible,
    monic polynomial `g\in K[x]` such that

    .. MATH::

        h(\xi) = v_\xi(h).

    By definition, any valuative function can be written as a linear combination
    of the form

    .. MATH::

        a_0 + \sum_i a_i h_i,

    where `h_i` are prime valuative functions and `a_i` are rational numbers.

    EXAMPLES ::

        sage: from mclf import *
        sage: FX.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(FX, QQ.valuation(2))
        sage: h = PrimeValuativeFunction(X, x^2+x/2+1/2)
        sage: h
        data representing an irreducible valuative function on the full Berkovich line

        sage: h.initial_value()
        -1
        sage: h.poles()
        [Point of type I on Berkovich space approximated by v(2*x + 1) >= 1, with equation 4*x^2 + 2*x + 2 = 0,
         Point of type I on Berkovich space approximated by v(x + 1) >= 1, with equation 4*x^2 + 2*x + 2 = 0]

        sage: D1 = ClosedPafDomain(X.point_from_discoid(x, 1))
        sage: h1 = h.restriction(D1)
        sage: h1.initial_value()
        -1
        sage: h1.poles()
        []
        sage: D2 = ClosedPafDomain(X.point_from_discoid(1/x, 1))
        sage: h2 = h.restriction(D2)
        sage: h2.initial_value()
        -2
        sage: h2.poles()
        [Point of type I on Berkovich space approximated by v(2*x + 1) >= 1, with equation 4*x^2 + 2*x + 2 = 0]

    """

    def __init__(self, D, g):
        from mclf.berkovich.berkovich_line import BerkovichLine
        if isinstance(D, BerkovichLine):
            D = ClosedPafDomain(D.gauss_point())
        else:
            assert isinstance(D, PafDomain), "D must be a paf domain"
        X = D.berkovich_line()
        g = X.function_field()(g)
        assert g.numerator().is_monic() and g.denominator().is_one(), "g must be a monic polynomial in x"
        assert g.numerator().is_irreducible(), "g must be irreducible"
        self._domain = D
        self._factor = g

    def __repr__(self):
        return "data representing an irreducible valuative function on {} ".format(self.domain())

    def domain(self):
        return self._domain

    def berkovich_line(self):
        return self.domain().berkovich_line()

    def factor(self):
        return self._factor

    def initial_point(self):
        return self.domain().initial_point()

    def initial_value(self):
        if not hasattr(self, "_initial_value"):
            self._initial_value = self.initial_point().v(self.factor())
        return self._initial_value

    def derivative(self, eta):
        r""" Return the derivative of this valuative function with respect to a type-V-point.

        """
        return eta.derivative(self.factor())

    def poles(self):
        r""" Return the poles of this prime valuative function.

        Here the poles are the zeros of the irreducible polynomial defining the
        the function, as points of type I. The infinity point (where our function
        actually does have a pole) does not count.

        This has to be accounted for when computing the poles of a general
        valuative function.
        """
        if not hasattr(self, "_poles"):
            self._poles = [xi for xi in self.berkovich_line().points_from_inequality(self.factor(), Infinity)
                           if self.domain().is_in(xi)]
        return self._poles

    def degree(self):
        return self.factor().numerator().degree()

    def __call__(self, xi):
        return xi.v(self.factor())

    def restriction(self, D):
        r""" Return the restriction of this prime valuative function to the domain D.

        INPUT:

        - ``D`` -- a paf domain, contained in the domain of this function `h`

        OUTPUT:

        The restriction of `h` to `D`.
        """
        # assert self.domain().contains(D), "D must be contained in the domain of this function"
        return PrimeValuativeFunction(D, self.factor())

# ----------------------------------------------------------------------------


class PiecewiseAffineFunction(SageObject):
    r""" A piecewise affine function on a domain in the Berkovich line.

    An object of this class represents a *piecewise affine* function

    .. MATH::

        h:D\to \mathbb{R}\cup\{\pm\infty\},

    where the domain `D` is a *paf domain*, i.e.\ either the full Berkovich line,
    or a closed or open discoid whose boundary point is also its infimum.

    There are two subclasses:

    If `D` is *closed*, i.e.\ the full Berkovich line, or a closed discoid, then
    `h` is an object of the subclass ``PiecewiseAffineFunctionOnClosedDomain``.
    In this case, `h` is represented by an *initial value* and a list of
    piecewise affine functions `h_1,\ldots,h_n`, where each `h_i` is the
    restriction of `h` to an open discoid `D_i\subset D`.

    The open discoids `D_i` are called the *critical domains*; they are precisely
    the pairwise disjoint residue classes of `D` on which `h` is not constant.
    It follows that `h` is constant on `D-(D_1\cup\ldots\cup D_n)`,
    equal to the initial value.

    If `D` is *open*, i.e. an open discoid, then `h` is an object of the class
    ``PiecewiseAffineFunctionOnOpenDomain``. In this case, `h` is represented
    by its *affine base* and its (unique) *restriction*, defined as follows.

    There exists a closed discoid `D_1\subset D` (called the *critical domain*),
    which is minimal with the property that the restriction of `h` to the open
    annuloid `D-D_1` is *affine*. (In the limit, `D_1` may consists of a single
    point of type I.) The *affine base* is then the restriction of `h` to `D-D_1`,
    and the *restriction* is the restriction of `h` to `D_1`.


    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, QQ.valuation(2))

    The most obvious examples of piecewise affine functions are *valuative functions*.
    We can e.g. define the valuative function of a rational function: ::

        sage: f = (x^2 - 2) / x
        sage: h = valuative_function(X, f)
        sage: h
        piecewise affine function on the full Berkovich line, with initial value 0

    A piecewise affine function can be evaluated at any point. ::

        sage: xi = X.point_from_discoid(x, 2)
        sage: h(xi)
        -1
        sage: xi.v(f)
        -1

    A piecewise affine function defines an affinoid subdomain (the point where
    the function takes nonnegative values). ::

        sage: h.affinoid_domain()
        Elementary affinoid defined by
        v(x) >= 0
        v(1/x) >= -1

    """

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
        return self.domain().initial_point()

    def domain(self):
        r""" Return the domain of this function.

        """
        return self._domain

    def is_constant(self):
        """ Return whether this function is constant.

        If the answer is ``True`` then it is guaranteed that the function is
        constant on its domain.

        But if the answer is `False`` we can't conclude anything.
        """
        return self._data_for_paf.is_constant()

    def is_in_domain(self, xi):
        """ Return whether a given point is in the domain of this function.

        """
        return self.domain().is_in(xi)

    def initial_value(self):
        """ Return the value of this function at the initial point.

        """
        return self._initial_value

    def is_increasing(self):
        r""" Return whether this function is monotonically increasing.

        If the answer is ``True`` then it is guaranteed that the function is
        monotonically increasing on its domain.

        But if the answer is `False`` we can't conclude anything.
        """
        return self._data_for_paf.is_increasing()

    def is_decreasing(self):
        r""" Return whether this function is monotonically decreasing.

        If the answer is ``True`` then it is guaranteed that the function is
        monotonically decreasing on its domain.

        But if the answer is `False`` we can't conclude anything.
        """
        return self._data_for_paf.is_decreasing()

    def affine_base(self):
        r""" Return the affine base of this function.

        The *affine base* is defined only for a piecewise affine function on an
        open diskoid; it is the restriction of the function to the maximal
        subannulus on which it is affine.

        This method must be implemented by the subclass
        ``PiecewiseAffineFunctionOnOpenDomain``.

        """
        raise NotImplementedError()

    def restrictions(self):
        r""" Return the restrictions of this piecewise affine functions.

        The *restrictions* of a piecewise affine function are the restrictions
        to the critical domains.

        If the domain `D` is closed, then the critical domains are the
        residue classes `D_1,\ldots,D_n\subset D` on which the function is not
        constant. It follows that the function is constant on the complement
        `D-(D_1\cup\ldots\cup D_n)`. In particular, the function is constant if
        and only if there are no restrictions.

        If the domain `D` is open then there is exactly one
        restriction, i.e. the restriction of the function to the critical
        domain `D_1\subset D`. This is the minimal closed subdiscoid such
        that the function is affine on the complement `D-D_1`. This includes the
        case where `D_1` consists of a unique point of type I, which is then the
        unique pole of the function.

        The restrictions are computed on demand, by the 'data' underlying this
        piecewise affine function.

        """
        if hasattr(self, "_restrictions"):
            return self._restrictions
        else:
            restrictions = [d.paf() for d in self._data_for_paf.restrictions()]
            self._restrictions = restrictions
            return restrictions

    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity), the value `h(\xi)`.

        This method must be implemented by both subclasses.

        """
        raise NotImplementedError()

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the domain of this function

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to `\eta`.

        NOTE: This needs to be defined in a more precise way.

        This function must be implemented by each subclass.

        """
        raise NotImplementedError()

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
        r""" Return the next points where this function takes a given value,
        after a given point.

        INPUT:

        - ``a`` -- a rational number
        - ``xi0`` (default: ``None``) -- a point in the domain of this function

        OUTPUT: The list of all points on the nerf of this function

        - at which this function takes the value `a`,
        - which are strictly greater than `\xi_0`, and
        - where the function is nonconstant

        If ``xi0`` is ``None`` then the second condition is ignored.

        This function has to be implemented by each subclass. See

        - :meth:`PiecewiseAffineFunctionOnClosedDomain.find_next_points_with_value`
        - :meth:`PiecewiseAffineFunctionOnClosedDomain.find_next_points_with_value`

        NOTE::

            Note that the function may be constant on a path of the nerf. If
            this constant value is equal to a, and xi0 lies on this path, then
            the output will be greater or equal to the terminal point of this path.
            In other words the output is a point which lies on the boundary of
            the closed subset of the nerv where the function takes the value `a`.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, QQ.valuation(2))
            sage: h = valuative_function(X, (x^2 + x + 2)/x)
            sage: h.find_next_points_with_value(0)
            [Point of type II on Berkovich line, corresponding to v(x) >= 0]

        If the second parameter `\xi_0` is given, the output consists of points
        strictly less than `\xi_0`. As the function `h` is constant on the path
        from the Gauss point to the point `v(x)\geq 1`, no point on this path
        is minimal with the required properties. ::

            sage: h.find_next_points_with_value(0, X.gauss_point())
            [Point of type II on Berkovich line, corresponding to v(x) >= 1]
            sage: h.find_next_points_with_value(1)
            [Point of type II on Berkovich line, corresponding to v(x + 2) >= 2,
             Point of type II on Berkovich line, corresponding to v(x + 1) >= 1]
            sage: points = h.find_next_points_with_value(-1)
            sage: points
            [Point of type II on Berkovich line, corresponding to v(x) >= 2,
             Point of type II on Berkovich line, corresponding to v(1/x) >= 1]
            sage: h.find_next_points_with_value(-1, points[0])
            []

        For the moment, the value `a=\infty` does not lead to a correct result. ::

            sage: h.find_next_points_with_value(Infinity)
            []

        """
        raise NotImplementedError()

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
            self._affinoid_domain = AffinoidDomainOnBerkovichLine(self.affinoid_tree())
        return self._affinoid_domain

    def is_contained_in_affinoid(self):
        r""" Return whether the domain of this function is contained in its affinoid domain.

        This means that the function is nonnegative everywhere.

        If the answer is ``True` then it is guaranteed that this actually holds.
        But if the anwer is ``False`` we don't know.
        """
        if hasattr(self, "_is_contained_in_affinoid"):
            return self._is_contained_in_affinoid
        if self.initial_value() >= 0 and self.is_increasing():
            self._is_contained_in_affinoid = True
            return True
        else:
            # we don't know, so we do not set the flag
            return False

    def is_disjoint_from_affinoid(self):
        r""" Return whether the domain of this function is disjoint from its affinoid domain.

        This means that the function is strictly negative everywhere.

        If the answer is ``True` then it is guaranteed that this actually holds.
        But if the anwer is ``False`` we don't know.
        """
        if hasattr(self, "_is_disjoint_from_affinoid"):
            return self._is_disjoint_from_affinoid
        if self.initial_value() < 0 and self.is_decreasing():
            self._is_disjoint_from_affinoid = True
            return True
        else:
            # we don't know, so we do not set the flag
            return False

    def affinoid_tree(self):
        r""" Return the affinoid tree underlying the affinoid domain defined by
        this function.

        This is a helper function for ``affinoid_domain()`` which works
        recursively.

        OUTPUT:

        an affinoid tree `T` with the following properties (`h` is this
        valuative function):

        - `T` is the refinement of the tree underlying `h`, obtained by adding
          all zeroes of `h` lying on the interior of an edge
        - the flag ``is_in`` is set for each vertex according to the
          value of `h` in this point.

        This method must be implemented by the subclasses. See

        - :meth:`PiecewiseAffineFunctionOnClosedDomain.affinoid_tree`
        - :meth:`PiecewiseAffineFunctionOnOpenDomain.affinoid_tree`

        """
        raise NotImplementedError()


class PiecewiseAffineFunctionOnClosedDomain(PiecewiseAffineFunction):
    r""" A piecewise affine function on a closed domain.

    This is the subclass of ``PiecewiseAffineFunction`` representing piecewise
    affine functions defined on a *closed paf domain* `D`, i.e. `D` is either
    the full Berkovich line, or a closed discoid whose boundary point is also
    its infimum.

    """

    def __init__(self, data_for_paf):

        assert data_for_paf.domain().is_closed(), "the domain of this paf must be closed"
        self._data_for_paf = data_for_paf
        self._domain = data_for_paf.domain()
        self._initial_value = data_for_paf.initial_value()

    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity), the value `h(\xi)`.

        """
        assert self.is_in_domain(xi), "xi must lie in the domain of this paf"
        for h in self.restrictions():
            if h.is_in_domain(xi):
                return h(xi)
        # if xi does not lie in one of the critical discoids, the value at xi
        # is equal to the initial value.
        return self.initial_value()

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the domain of this function

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to `\eta`.

        """
        # check that eta lies in the domain!
        assert self.is_in_domain(eta), "eta does not lie in the domain"
        for h in self.restrictions():
            if h.is_in_domain(eta):
                return h.derivative(eta)
        # the function is constant on the complement of the critical discoids;
        # therefore:
        return 0

    def find_next_points_with_value(self, a, xi0=None):
        r""" Return the next points where this function takes a given value,
        after a given point.

        INPUT:

        - ``a`` -- a rational number
        - ``xi0`` (default: ``None``) -- a point in the domain of this function

        OUTPUT: The list of all points on the nerf of this function

        - at which this function takes the value `a`,
        - which are strictly greater than `\xi_0`, and
        - where the function is nonconstant

        If ``xi0`` is ``None`` then the second condition is ignored.

        EXAMPLES::

            sage: from mclf import *
            sage: FX.<x> = FunctionField(QQ)
            sage: v_K = QQ.valuation(2)
            sage: X = BerkovichLine(FX, v_K)
            sage: h = valuative_function(X, (x+2)/x)
            sage: h.find_next_points_with_value(0)
            [Point of type II on Berkovich line, corresponding to v(x) >= 0]
            sage: h.find_next_points_with_value(0, X.gauss_point())
            [Point of type II on Berkovich line, corresponding to v(x) >= 1]

        """

        if xi0 is not None and xi0.is_incomparable(self.initial_point()):
            # no point in the domain of this function can be strictly greater than xi0
            return []
        elif self.initial_value() == a and (xi0 is None or xi0.is_strictly_less(self.initial_point())):
            return [self.initial_point()]
        else:
            ret = []
            for h in self.restrictions():
                ret += h.find_next_points_with_value(a, xi0)
        return ret

    def affinoid_tree(self):
        r""" Return the affinoid tree underlying the affinoid domain defined by
        this piecewise affine function on a closed paf domain.

        This is a helper function for ``affinoid_domain()`` which works
        recursively.

        OUTPUT:

        an affinoid tree `T` corresponding to the affinoid subdomain

        .. MATH::

            U := \{ \xi\in D \mid h(\xi) \geq 0 \},

        or ``None``.

        `T` is defined by the following properties:

        - `T` is the refinement of the tree underlying `h`, obtained by adding
          all zeroes of `h` lying on the interior of an edge
        - the flag ``is_in`` is set for each vertex according to the
          value of `h` in this point.

        If `T` consists only of its root, then the flags ``_is_contained_in_affinoid``
        and ``is_disjoint_from_affonoid`` are set as ``True`` and ``False``,
        depending of whether the initial value is `\geq 0` (which means that the
        domain `D` of `h` is contained in the affinoid `U`) or is `< 0` (which means
        that `D` is disjoint from `U`). Moreover, this method then returns ``None``.

        """
        from mclf.berkovich.affinoid_domain import AffinoidTree
        X = self.berkovich_line()
        initial_value = self.initial_value()
        if self.is_constant():
            if initial_value >= 0:
                self._is_contained_in_affinoid = True
                self._is_disjoint_from_affinoid = False
                return
            else:
                self._is_contained_in_affinoid = False
                self._is_disjoint_from_affinoid = True
                return
        elif initial_value >= 0:
            if all(g.is_contained_in_affinoid() for g in self.restrictions()):
                self._is_contained_in_affinoid = True
                self._is_disjoint_from_affinoid = False
                return
            else:
                T = AffinoidTree(X, root=self.initial_point(), is_in=True)
                for g in self.restrictions():
                    if g.is_disjoint_from_affinoid():
                        # the domain of g is a hole of the affinoid
                        T.make_child(AffinoidTree(X, root=g.affine_base().terminal_point(), is_in=False))
                    elif not g.is_contained_in_affinoid():
                        T.make_child(g.affinoid_tree())
                return T
        else:
            # now the initial value is strictly negative
            if all(g.is_disjoint_from_affinoid() for g in self.restrictions()):
                self._is_contained_in_affinoid = False
                self._is_disjoint_from_affinoid = True
                return
            else:
                T = AffinoidTree(X, root=self.initial_point(), is_in=False)
                for g in self.restrictions():
                    if not g.is_disjoint_from_affinoid():
                        child = g.affinoid_tree()
                        if child is not None:
                            T.make_child(child)
                return T


class PiecewiseAffineFunctionOnOpenDomain(PiecewiseAffineFunction):
    r""" A piecewise affine function on an open domain.

    This is the subclass of ``PiecewiseAffineFunction`` representing piecewise
    affine functions defined on an *open paf domain* `D`, i.e. `D` is an open
    discoid whose boundary point is also its infimum.

    """

    def __init__(self, data_for_paf):

        assert data_for_paf.domain().is_open(), "the domain of this paf must be an open discoid"
        self._data_for_paf = data_for_paf
        self._domain = data_for_paf.domain()
        self._initial_value = data_for_paf.initial_value()

    def affine_base(self):
        r""" Return the affine base of this function.

        The *affine base* is defined only for a piecewise affine function on an
        open diskoid; it is the restriction of the function to the maximal
        subannulus on which it is affine.

        """
        if hasattr(self, "_affine_base"):
            return self._affine_base
        else:
            affine_base = self._data_for_paf.affine_base()
            self._affine_base = affine_base
            return affine_base

    def __call__(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity), the value `h(\xi)`.

        """
        assert self.is_in_domain(xi), "xi must lie in the domain of this paf"
        for h in self.restrictions():
            if h.is_in_domain(xi):
                return h(xi)
        return self.affine_base()(xi)

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the domain of this function

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to `\eta`.

        NOTE: This needs to be defined in a more precise way.

        """
        assert self.is_in_domain(eta), "eta does not lie in the domain"
        for h in self.restrictions():
            if h.is_in_domain(eta):
                return h.derivative(eta)
        return self.affine_base().derivative(eta)

    def find_next_points_with_value(self, a, xi0=None):
        r""" Return the next points where this function takes a given value,
        after a given point.

        INPUT:

        - ``a`` -- a rational number
        - ``xi0`` (default: ``None``) -- a point in the domain of this function

        OUTPUT: The list of all points on the nerf of this function

        - at which this function takes the value `a`,
        - which are strictly greater than `\xi_0`, and
        - where the function is nonconstant

        If ``xi0`` is ``None`` then the second condition is ignored.

        EXAMPLES::

            sage: from mclf import *
            sage: FX.<x> = FunctionField(QQ)
            sage: v_K = QQ.valuation(2)
            sage: X = BerkovichLine(FX, v_K)
            sage: xi0 = X.gauss_point()
            sage: xi1 = X.point_from_discoid(x, 1)
            sage: D = OpenPafDomain(xi0, xi1)
            sage: h = valuative_function(D, (x+2)/x)
            sage: h.find_next_points_with_value(0)
            [Point of type II on Berkovich line, corresponding to v(x) >= 1]
            sage: h.find_next_points_with_value(0, xi1)
            []

        """

        if xi0 is not None and xi0.is_incomparable(self.initial_point()):
            # no point in the domain of this function can be strictly greater than xi0
            return []
        else:
            xi = self.affine_base().find_point_with_value(a)
            if xi is not None and (xi0 is None or xi0.is_strictly_less(xi)):
                return [xi]
            else:
                ret = []
                for h in self.restrictions():
                    ret += h.find_next_points_with_value(a, xi0)
                return ret

    def is_disjoint_from_affinoid(self):
        r""" Return whether the domain of this function is disjoint from its affinoid domain.

        This means that the function is strictly negative everywhere.

        If the answer is ``True` then it is guaranteed that this actually holds.
        But if the anwer is ``False`` we don't know.

        EXAMPLES::

            sage: from mclf import *
            sage: FX.<x> = FunctionField(QQ)
            sage: v_K = QQ.valuation(2)
            sage: X = BerkovichLine(FX, v_K)
            sage: xi0 = X.gauss_point()
            sage: xi1 = X.point_from_discoid(x, 1)
            sage: D = OpenPafDomain(xi0, xi1)
            sage: h = valuative_function(D, 1/x)
            sage: h.is_disjoint_from_affinoid()
            True

        """
        if hasattr(self, "_is_disjoint_from_affinoid"):
            return self._is_disjoint_from_affinoid
        if self.initial_value() < 0 and self.is_decreasing():
            self._is_disjoint_from_affinoid = True
            return True
        elif self.initial_value() == 0 and self.is_decreasing() and self.affine_base().slope() < 0:
            self._is_disjoint_from_affinoid = True
            return True
        else:
            # we don't know, so we do not set the flag
            return False

    def affinoid_tree(self):
        r""" Return the affinoid tree underlying the affinoid domain defined by
        this piecewise affine function on a open paf domain.

        This is a helper function for ``affinoid_domain()`` which works
        recursively.

        OUTPUT:

        an affinoid tree `T` corresponding to the closed subdomain

        .. MATH::

            U := \{ \xi\in D \mid h(\xi) \geq 0 \},

        or ``None``.

        Not that `U` may be empty, or equal to the domain `D`. In this case,
        `U` is not an affinoid domain. Then the flags `is_contained_in_affinoid`
        and `is_disjoint_from_affinoid` are set accordingly, and the output is an
        affinoid tree `T` with just one node, or ``None``. We return ``None`` if
        `U=D` and the initial value is `\geq 0`, or if `U` is empty and the
        initial value is `< 0`. So if `T` is not ``None`` then its root
        must lie inside the domain of this function.

        """
        from mclf.berkovich.affinoid_domain import AffinoidTree
        X = self.berkovich_line()
        initial_value = self.initial_value()
        if self.is_constant():
            if initial_value >= 0:
                # now U=D
                self._is_contained_in_affinoid = True
                self._is_disjoint_from_affinoid = False
                return
            else:
                # now U is empty
                self._is_contained_in_affinoid = False
                self._is_disjoint_from_affinoid = True
                return
        else:
            affine_base = self.affine_base()
            xi = affine_base.find_zero()
            if xi is not None:
                # now xi is an isolated zero on the interior of the path
                T = AffinoidTree(X, root=xi, is_in=True)
                if len(self.restrictions()) > 0:
                    h = self.restrictions()[0]
                    child = h.affinoid_tree()
                    if child is not None:
                        T.make_child(child)
                    elif h.initial_value() < 0:
                        T.make_child(AffinoidTree(X, root=h.initial_point(), is_in=False))
                else:
                    # the terminal point of the affine base is of type I;
                    if affine_base.terminal_value() < 0:
                        child = AffinoidTree(X, root=affine_base.terminal_point(), is_in=False)
                        T.make_child(child)
                return T
            else:
                # there is no isolated zero on the interior of the path
                if len(self.restrictions()) > 0:
                    g = self.restrictions()[0]
                    if self.initial_value() < 0 and g.is_contained_in_affinoid():
                        return AffinoidTree(X, root=g.initial_point(), is_in=True)
                    else:
                        return self.restrictions()[0].affinoid_tree()
                elif self.initial_value() == 0 and affine_base.slope() < 0:
                    # in this case, U is empty, but the initial point is contained in U
                    return AffinoidTree(X, root=affine_base.terminal_point(), is_in=False)
                else:
                    return

# ----------------------------------------------------------------------------


class AffineFunction(SageObject):
    r""" An affine function on an open annuloid or an open discoid.

    INPUT:

    - ``gamma`` -- a directed path on the Berkovich line
    - ``a``, ``b`` -- rational numbers

    OUTPUT:

    the affine function `h` on the tube `D` of the path `\gamma = [\xi_1,\xi_2]`
    defined by `a` and `b`. If `t:D \to \mathbb{R}` is the standard
    parametrization, then

    .. MATH::

            h(\xi) := a\cdot t(\xi) + b.

    """

    def __init__(self, gamma, a, b):
        self._gamma = gamma
        self._a = QQ(a)
        self._b = QQ(b)

    def __repr__(self):
        return "affine function on the tube of the {}, with initial value {}.".format(self.path(), self.initial_value())

    def berkovich_line(self):
        r""" Return the Berkovich line underlying this affine function.
        """
        return self.path().berkovich_line()

    def path(self):
        r""" Return the path underlying this affine function.
        """
        return self._gamma

    def initial_point(self):
        r""" Return the initial point of the path underlying this affine function.
        """
        return self.path().initial_point()

    def initial_tangent_vector(self):
        return self.path().initial_tangent_vector()

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

    def __call__(self, xi):
        r""" Return the value of this affine function on a point.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        the value `h(\xi)`, where `h` is this affine function.

        It is assumed that `\xi` lies in the domain of `h`; otherwise an error
        is raised.

        """
        # self.path().initial_slope()  # ????
        return self._a * self.path().parameter(xi) + self._b

    def slope(self):
        r""" Return the slope of this affine function.

        """
        return self._a

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

    def is_strictly_increasing(self):
        r""" Return whether this affine function is strictly increasing.
        """
        return self._a > 0

    def find_zero(self):
        r""" Return an isolated zero of this affine function (if there is one).

        OUTPUT:

        a point `\xi` on the *interior* of the path underlying this
        function which is an isolated zero.

        If no such zero exists, ``None`` is returned.

        We note that "isolated" implies that the function is not constant if
        `\xi` exists, and therefore there is at most one such point.

        """
        return self.find_point_with_value(0)

    def find_point_with_value(self, c):
        r""" Return a point where this affine function takes a given value.

        OUTPUT:

        a point `\xi` on the *interior* of the underlying path such that
        the function is nonconstant in `\xi` and takes the value `c`.

        If no such point exists, ``None`` is returned.

        """
        a = self._a
        b = self._b
        gamma = self.path()
        if a == 0:
            return None
            # the function is constant on this path
        else:
            t = (c - b)/a
            if gamma.is_parameter(t, in_interior=True):
                xi = gamma.point(t)
                return xi
            else:
                return None


def create_affine_function(xi1, xi2, c1, c2):
    r""" Return the affine function with given boundary values.

    INPUT:

    - ``xi1``, ``xi2`` -- points on the Berkovich line
    - ``c1``, ``c2`` -- rational numbers

    We must have `\xi_1<\xi_2`.

    OUTPUT:

    An affine function `h` on the intervall `[\xi_1,\xi_2]`, determined as follows:

    - if `\xi_2` is of type II, then `h(\xi_1)=c_1` and `h(\xi_2)=c_2`
    - if `\xi_2` is of type I then `h(\xi_1)=c_1` and `h'(\xi_1)=c_2`. Here
      `h'` is the 'natural' derivation of `h`

    """
    assert xi1.is_strictly_less(xi2), "xi1 must be strictly less than xi2"
    gamma = DirectedPath(xi1, xi2)
    if xi2.type() == "II":
        s1 = gamma.initial_parameter()
        s2 = gamma.terminal_parameter()
        a = QQ((c1-c2)/(s1-s2))
        b = c1 - a*s1
    elif xi2.type() == "I":
        s1 = gamma.initial_parameter()
        a = QQ(c2/gamma.initial_slope())
        b = c1 - a*s1
    else:
        raise ValueError()
    return AffineFunction(gamma, a, b)


# ---------------------------------------------------------------------------


def valuative_function(D, f):
    r""" A valuative function on a domain in the Berkovich line.

    INPUT:

    - ``D`` -- a paf domain in the Berkovich line
    - ``f`` -- a nonconstant rational function on `X`, or
               a pair `(L, a_0)`, where `L` is a list of pairs `(g, a)` where
               `g` is a nonconstant rational function and `a`, `a_0` are rational
               numbers

    OUTPUT:

    If `f` is a rational function, then we create the valuative function
    `h` on `D` defined as

    .. MATH::

        h(\xi) := v_K(f(\xi))

    If ``f`` is a pair `(L, a_0)` as above, where `L` is a list of pairs
    `(f_i, a_i)`, then the corresponding valuative function is defined as

    .. MATH::

        h(\xi) := a_0 + \sum_i a_i v(f_i(\xi)).

    """
    from mclf.berkovich.berkovich_line import BerkovichLine
    if isinstance(D, BerkovichLine):
        X = D
        D = ClosedPafDomain(X.gauss_point())
    else:
        X = D.berkovich_line()
    if not isinstance(f, type(())):
        assert f.parent() is X.function_field(), "f must be an element of the function field of X"
        L = [(f, 1)]
        a_0 = 0
    else:
        L, a_0 = f
    # now we turn L into a list of pairs (h_i,a_i), where the h_i are monic,
    # irreducible, and pairwise distinct; note that this may affect a_0 as well
    new_L = []
    v_K = X.base_valuation()
    for f, a in L:
        ff = f.factor()
        a_0 += v_K(ff.unit())*a
        for g, m in ff:
            # check whether g already occurs in L
            g_is_new = True
            for i in range(len(new_L)):
                if g == new_L[i][0]:
                    g_is_new = False
                    new_L[i] = (new_L[i][0], new_L[i][1] + a*m)
                    break
            if g_is_new:
                new_L.append((g, a*m))

    factors = []
    for f, a in new_L:
        h = PrimeValuativeFunction(D, f)
        factors.append((h, a))

    if D.is_closed():
        return DataForValuativeFunctionOnClosedDomain(D, factors, a_0).paf()
    else:
        return DataForValuativeFunctionOnOpenDomain(D, factors, a_0).paf()


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
            D2 = ClosedPafDomain(xi1)
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
        assert d == b, "a = {}, b = {}, c = {}, d ={}, gamma ={}, L = {}, a0 = {}".format(a, b, c, d, gamma, L, a0)
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
