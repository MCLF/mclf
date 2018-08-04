r"""
The Berkovich projective line over a discretely valued field
============================================================

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `F=K(x)`
be a rational function field over `K`. We consider `F` as the function
field of the projective line `X:=\mathbb{P}_K^1` over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. Then a point `\xi` on
`X^{an}` may be identified with a (real valued) pseudo-valuation
`v_\xi` on `F` extending `v_K`.

Note that we do not assume `K` to be complete with respect to `v_K`. Hence we
can work with 'exact' fields, e.g. number fields.

There are only two kind of 'points' which are relevant for us and can be handled
using the mac_lane infrastructure:

- Type I, algebraic: these are the points that come from a closed point on the
  (algebraic) projective line over the completed base field.
- Type II: these are the points which correspond to discrete valuations on the
  function field whose residue field is a function field over the residue base
  field

If `v_\xi(x)\geq 0` we say that `\xi` lies *in the unit disk*. Then the
restriction of `v_\xi` to `K[x]` is a discrete pseudo-valuation which can be
realized either as an inductive valuation, or as a limit valuation.

If `\xi` does not lie in the unit disk, then we use instead the restriction
of `v_\xi` to the polynomial ring `K[x^{-1}]` (internally, we use the ring
`K[x]`, though).

By a result of Berkovich, the topological space `X^{an}` is a *simply connected
quasi-polyhedron*. Among other things this means that for any two points
`\xi_1,\xi_2\in X^{an}` there exists a unique closed subset

.. MATH::      [\xi_1,\xi_2]\subset X^{an}

which is homeomorphic to the unit interval `[0,1]\subset\mathbb{R}` in such a way that
`\xi_1,\xi_2` are mapped to the endpoints `0,1`.

Let `\xi^g\in X^{an}` denote the *Gauss point*, corresponding to the Gauss
valuation on `F=K(x)` with respect to the parameter `x`. Then `X^{an}` has a
unique partial ordering determined by the following two conditions:

- `\xi^g` is the smallest element
- we have `\xi_1<\xi_2` if and only if `\xi_2` lies in a connected component
  of `X^{an}-\{\xi_1\}` which does not contain `\xi^g`.

A point `\xi` of type II has a *discoid representation* as follows. If
`\xi=\xi^g` then `D_\xi` is defined as the closed unit disk. Otherwise,
`D_\xi` is defined of the set of all points `\xi_1\in X^{an}` such that
`\xi\leq\xi_1`. Then `D_\xi` is of the form

.. MATH::    D_\xi = \{ \xi_1 \mid v_{\xi_1}(f) \geq s\},

where `f` is a polynomial in `x`, irreducible over
`\hat{\bar{K}}` (or `f= 1/x`) and `s` is a rational number.
The pair `(f,s)` determines `\xi`, but this representation is not unique. We call
`(f, s)` a *discoid representation* of `\xi`.

Note that we can simply extend the discoid representation to certain points of
type I by allowing `s` to take the value `\infty`.

AUTHORS:

- Stefan Wewers (2017-02-10): initial version


EXAMPLES::

    sage: from mclf import *
    sage: v_2 = QQ.valuation(2)
    sage: F.<x> = FunctionField(QQ)
    sage: X = BerkovichLine(F, v_2)
    sage: X
    Berkovich line with function field Rational function field in x over Rational Field with 2-adic valuation

We define a point of type II via its discoid.::

    sage: xi1 = X.point_from_discoid(x^3 + 2, 3)
    sage: xi1
    Point of type II on Berkovich line, corresponding to v(x^3 + 2) >= 3

If the affinoid `v(f)\geq s` is not irreducible, an error is raised.::

    sage: X.point_from_discoid(x^2-1, 2)
    Traceback (most recent call last):
    ...
    AssertionError: D is not a discoid

We can similarly define points which do not lie on the unit disk.::

    sage: xi2 = X.point_from_discoid(4*x+1, 1)
    sage: xi2
    Point of type II on Berkovich line, corresponding to v(4*x + 1) >= 1

The infimum of a point inside and a point outside the unit disk must be the
Gauss point, corresponding to the unit disk.::

    sage: xi1.infimum(xi2)
    Point of type II on Berkovich line, corresponding to v(x) >= 0
    sage: X.gauss_point()
    Point of type II on Berkovich line, corresponding to v(x) >= 0

Some points of type I are *limit points*, i.e. they can only be approximated
by points of type II. For instance, the zeroes of a polynomial which is
irreducible over the ground field `\mathbb{Q}`, but not over its completion
`\mathbb{Q}_2`.::

    sage: f = 2*x^2 + x + 1
    sage: f.factor()
    (2) * (x^2 + 1/2*x + 1/2)

    sage: D = X.divisor(f)
    sage: D
    [(Point of type I on Berkovich space approximated by v(2*x + 1) >= 1, 1),
     (Point of type I on Berkovich space approximated by v(x + 1) >= 1, 1),
     (The point at infinity on the Berkovich line, -2)]
    sage: xi = D[0][0]
    sage: xi.equation()
    4*x^2 + 2*x + 2

Note that the point `\xi` lies outside and its Galois conjugate point lies inside
of the unit disk. This shows that issue #39 has been fixed (at least as far as
the module ``berkovich_line`` is concerned).

TO DO:

- allow "virtual functions" for the evaluations of valuations (and derivations).
  "Virtual functions" are products of rational functions with possible rational
  exponents.

- use more cached functions; this may improve speed

- more systematic (and explicitly defined) relation between points and their
  discoid representation

- more doctests!


"""

#*****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import SageObject, Infinity, sgn, GaussValuation, ZZ
from sage.rings.valuation.limit_valuation import LimitValuation
from sage.geometry.newton_polygon import NewtonPolygon


class BerkovichLine(SageObject):
    r"""
    The class of a Berkovich projective line over a discretely valued field.

    Let `K` be a field and `v_K` a discrete valuation on `K`. Let `F=K(x)`
    be a rational function field over `K`. We consider `F` a the function
    field of the projective line `X` over `K`. Let `X^{an}` denote the
    `(K,v_K)`-analytic space associated to `X`. Then a point `\xi` on `X^{an}`
    may be identified with a (real valued) pseudo-valuation `v_\xi` on `F`
    extending `v_K`.

    INPUT:

    - ``F`` -- a rational function field over a base field K
    - ``vK`` -- a discrete valuation on the base field K

    """

    def __init__(self, F, vK):

        assert vK.domain() is F.constant_base_field()
        self._F = F
        self._vK = vK
        self._K = vK.domain()

    def __repr__(self):

        return "Berkovich line with function field %s with %s"%(self._F, self._vK)


    def constant_base_field(self):

        return self._F.constant_base_field()


    def base_valuation(self):

        return self._vK


    def function_field(self):

        return self._F


    def polynomial_ring(self):

        return self.function_field()._ring


    def infty(self):
        r"""
        Return the point `\infty`.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: X.infty()
            The point at infinity on the Berkovich line

        """

        R = self._F._ring
        F = self._F
        x = F.gen()
        v0 = GaussValuation(R, self._vK)
        v1 = v0.augmentation(R.gen(), Infinity)
        return TypeIPointOnBerkovichLine(self, (v1, 1/x))


    def gauss_point(self):
        r"""
        Return the Gauss point of self.

        The Gauss point is the type-II-point corresponding to the Gauss
        valuation on `K[x]`. Its discoid is the unit disk.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: X.gauss_point()
            Point of type II on Berkovich line, corresponding to v(x) >= 0

        """
        x = self.function_field().gen()
        return self.point_from_discoid(x, 0)


    def point_from_pseudovaluation_on_polynomial_ring(self, v0, parameter=None):
        r""" Return the point corresponding to a pseudo-valuation on a polynomial ring.

        INPUT:

        - ``v0`` -- a discrete pseudo-valuation on a polynomial ring over the
                base field `K`, extending the base valuation `v_K`
        - ``parameter`` -- a parameter for the function field (default: ``None``)

        OUTPUT:

        The point on this Berkovich line corresponding to ``v0``, with respect
        to ``parameter``. If ``parameter`` is not given, we assume that it is
        the standard parameter `x`.

        """
        if v0.is_discrete_valuation():
            return TypeIIPointOnBerkovichLine(self, (v0, parameter))
        else:
            return TypeIPointOnBerkovichLine(self, (v0, parameter))


    def point_from_pseudovaluation(self, v):
        r"""
        Return the point on the Berkovich line corresponding to the pseudovaluation ``v``.

        INPUT:

        - ``v`` -- a discrete pseudovaluation on the function field of ``self``,
                   extending the base valuation `v_K`

        OUTPUT:

        The point `\xi` on the Berkovich line `X` =``self`` corresponding to
        the pseudo valuation ``v`` on the function field of `X`.
        """

        if v.is_discrete_valuation():
            return TypeIIPointOnBerkovichLine(self, v)
        else:
            return TypeIPointOnBerkovichLine(self, v)


    def point_from_discoid(self, f, s):
        r"""
        Return the point on ``self`` determined by a discoid.

        INPUT:

        - ``f`` -- a nonconstant polynomial in `x`, or `1/x`
        - ``s`` -- a rational number, or `\infty`

        OUTPUT:  a point `\xi` on the Berkovich line which is the unique
        boundary point of the discoid

        .. MATH::

            D := \{ \xi \mid v_\xi(f) \geq s \}.

        Here it is *assumed* that `D` defined as above is a (possibly degenerate)
        diskoid (in particular: irreducible), and that it is either contained in
        or disjoint from the unit disk. If this is not the case,
        an error is raised.

        For the latter condition it is sufficient that  `f` is monic, integral and
        irreducible over `\hat{K}`.

        """

        assert s > -Infinity
        X = self
        F = X.function_field()
        f = F(f)
        x = F.gen()
        vK = X.base_valuation()
        pi = vK.uniformizer()

        if f.denominator().degree()==0:
            # f is a polynomial in x
            f0 = f.numerator().monic()
            v0 = GaussValuation(f0.parent(), vK)
            c = vK.domain().one()
            while v0(f0) < 0:
                f0 = f0(x/pi).numerator().monic()
                c *= pi
            s1 = s + vK(c)*f0.degree() - vK(f.numerator().leading_coefficient()) \
                + vK(f.denominator())
            v1 = valuation_from_discoid(vK, f0, s1)
            if s1 == Infinity:
                xi = TypeIPointOnBerkovichLine(X, (v1, x/c))
            else:
                xi = TypeIIPointOnBerkovichLine(X, (v1, x/c))
        else:
            assert f == 1/x, "f must be either a polynomial, or 1/x"
            assert s > 0, "if f=1/x then s must be positive"
            v0 = GaussValuation(F._ring, vK).augmentation(F._ring.gen(), s)
            xi = TypeIIPointOnBerkovichLine(X, (v0, 1/x))
        assert xi.v(f) == s
        return xi


    def points_from_inequality(self, f, s):
        r"""
        Return the boundary points of the affinoid given by a polynomial inequality.

        INPUT:

        - ``f`` -- a nonconstant polynomial in `x` or in `1/x`
        - ``s`` -- a nonnegative rational number, or `\infty`

        OUTPUT:

        a list of points which are the boundary points of the affinoid given
        by the inequality `v(f) \geq s`. Note that the affinoid is a union
        of finitely many discoids (or of finitely many algebraic points if
        `s=\infty`).

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: v_2 = QQ.valuation(2)
            sage: X = BerkovichLine(F, v_2)
            sage: X.points_from_inequality((x^2-1)*(2*x-1), 4)
            [Point of type II on Berkovich line, corresponding to v(x + 1) >= 3,
             Point of type II on Berkovich line, corresponding to v(x + 7) >= 3,
             Point of type II on Berkovich line, corresponding to v(-2*x + 1) >= 6]
            sage: X.points_from_inequality(2*x^(-2)+x^(-1)+4, 5)
            [Point of type II on Berkovich line, corresponding to v(4*x + 1) >= 3,
             Point of type II on Berkovich line, corresponding to v(x + 2/57) >= 7]
            sage: X.points_from_inequality(2*x^(-2)+x^(-1)+4, Infinity)
            [Point of type I on Berkovich space approximated by v(4*x + 1) >= 3,
             Point of type I on Berkovich space approximated by v(x + 2) >= 4]

        """
        vK = self.base_valuation()
        pi = vK.uniformizer()
        F = self.function_field()
        x = F.gen()
        if s == Infinity:
            # we return the divisor of zeroes of f
            D = self.divisor(f)
            return [xi for xi, m in D if m>0]
        if f.denominator().is_one():
            # f is a polynomial in x
            # by scaling we find a monic integral version of f
            f0 = f.numerator().monic()
            v0 = GaussValuation(f0.parent(), vK)
            c = vK.domain().one()
            while v0(f0) < 0:
                f0 = f0(x/pi).numerator().monic()
                c *= pi
            s0 = s + vK(c)*f0.degree() - vK(f.numerator().leading_coefficient()) \
                + vK(f.denominator())
            V = valuations_from_inequality(vK, f0, s0)
            ret = [TypeIIPointOnBerkovichLine(self, (v0, x/c)) for v0 in V]
            assert all([xi.v(f)==s for xi in ret])
            return ret
        else:
            # f should now be a polynomial in 1/x
            f1 = F.hom([1/x])(f)
            assert f1.denominator().is_one(), 'f is not a polynomial in x or 1/x'
            f0 = f1.numerator().monic()
            v0 = GaussValuation(f0.parent(), vK)
            c = vK.domain().one()
            while v0(f0) < 0:
                f0 = f0(x/pi).numerator().monic()
                c *= pi
            s0 = s + vK(c)*f0.degree() - vK(f1.numerator().leading_coefficient()) \
                + vK(f1.denominator())
            V = valuations_from_inequality(vK, f0, s0)
            ret = [TypeIIPointOnBerkovichLine(self, (v0, c/x)) for v0 in V]
            assert all([xi.v(f)==s for xi in ret])
            return ret


    def find_zero(self, xi1, xi2, f):
        r"""
        Return the point between ``xi1`` and ``xi2`` where ``f`` has valuation `0`.

        INPUT:

        - ``xi1``, ``xi2`` -- points on the Berkovich line such that `\xi_1<\xi2`
        - ``f`` -- a nonconstant rational function; it is assumed that the signs
                   of the valuations of f at `\xi1` and `\xi2` are different

        OUTPUT:

        The smallest point between `\xi1` and `\xi2` where the valuation of `f`
        is zero.

        NOTE:

        We are assuming for the moment that the function

        .. MATH::

             v \mapsto v(f)

        is affine (i.e. has no kinks) on the interval `[\xi_1,\xi_2]`.


        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: xi1 = X.gauss_point()
            sage: xi2 = X.point_from_discoid(x^4+2*x^2+2, 10)
            sage: X.find_zero(xi1, xi2, (x^4+2*x^2+2)/4)
            Point of type II on Berkovich line, corresponding to v(x^4 + 2*x^2 + 2) >= 2

            sage: xi3 = X.point_from_discoid(4*x^4+2*x^2+1, 10)
            sage: f = 2*x^3
            sage: xi1.v(f), xi3.v(f)
            (1, -1/2)
            sage: X.find_zero(xi1, xi3, f)
            Point of type II on Berkovich line, corresponding to v(1/x) >= 1/3


        .. TODO::

             Remove the assumption on the kinks.

        """

        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine

        X = self
        F = X.function_field()
        x = F.gen()

        assert xi1.is_leq(xi2) and not xi2.is_leq(xi1), \
            "xi1 must be strictly smaller than xi2"
        h1 = xi1.v(f)
        h2 = xi2.v(f)
        assert (h1 <= 0 and h2 >= 0) or (h1 >= 0 and h2 <=0),\
            "the values of f at xi1 and xi2 must have different sign"
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
            while sgn(xi2_approx.v(f)) != sgn(h2) and count < 100:
                xi2_approx = xi2.improved_approximation()
                count += 1
            assert count < 100, "could not find sufficient approximation!"

        if xi2.is_in_unit_disk():
            phi, s2 = xi2.discoid()
            s1 = xi1.v(phi)
            # we are looking for t, s1 < t < s2, such that f has zero valuation
            # at the point xi_t: v(phi) >= t.
            eta = TypeVPointOnBerkovichLine(xi1, xi2)
            m = eta.derivative(f)
            n = eta.derivative(phi)
            # now the function t |--> v_t(f) has slope m/n
            t = s1 - n*h1/m
            xi3 = X.point_from_discoid(phi, t)
        else:
            v1 = xi1.pseudovaluation_on_polynomial_ring()
            v2 = xi2.pseudovaluation_on_polynomial_ring()
            phi = v2.phi()
            s1 = v1(phi)
            eta = TypeVPointOnBerkovichLine(xi1, xi2)
            m = eta.derivative(f)
            n = eta.derivative(phi(1/x))
            t = s1 - n*h1/m
            v3 = valuation_from_discoid(self.base_valuation(), phi, t)
            xi3 = TypeIIPointOnBerkovichLine(self, (v3, 1/x))
        assert xi3.v(f) == 0
        return xi3


    def divisor(self, f):
        r"""
        Return the divisor of a rational function `f`.

        INPUT:

        - `f` -- a nonzero element of the function field of self

        OUTPUT:

        the divisor of `f`, as a list of pairs `(\xi, m)`, where `\xi` is
        a point of type I and m is the multiplicity of `\xi`.

        """
        F = f.factor()
        D = []
        for g, e in F:
            D = D + self.prime_divisor(g, e)
        d = f.numerator().degree()-f.denominator().degree()
        if d != 0:
            D.append((self.infty(), -d))
        return D


    def prime_divisor(self, f, e=ZZ(1)):
        r"""
        Return the divisor of zeroes of an irreducible polynomial.

        INPUT:

         - ``f`` -- an irreducible polynomial in the generator of the function
                    field of self
         - ``e`` -- an integer (default=`1`)

        OUTPUT:

        The divisor of zeroes of `f`, multiplied with `e`.

        Note that the polynomial `f` may not be irreducible over the completion
        `\hat{K}` of the base field `K`. So the output is a list of pairs
        `(\xi,m)`, where `\xi` is a point of type I corresponding to an irreducible
        factor of `f` over `\hat{K}`.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: v_2 = QQ.valuation(2)
            sage: X = BerkovichLine(F, v_2)
            sage: f = 2*x^2 + x + 1
            sage: D = X.prime_divisor(f)
            sage: D
            [(Point of type I on Berkovich space approximated by v(2*x + 1) >= 1, 1),
             (Point of type I on Berkovich space approximated by v(x + 1) >= 1, 1)]

        """

        F = self._F
        x = F.gen()
        assert f.parent() is F, "f must lie in the function field of X"
        assert f.denominator().is_one(), "f must be a polynomial"
        f = f.numerator()
        assert f.is_irreducible(), "f is not irreducible"
        assert f.degree() > 0, "f must be nonconstant"
        R = f.parent()
        vK = self.base_valuation()
        v0 = GaussValuation(R, vK)

        NP = NewtonPolygon([(i, vK(f[i])) for i in range(f.degree() + 1)])
        slopes = NP.slopes(False)

        outside_of_unit_disk = (slopes != [] and min(slopes) > 0)
        if outside_of_unit_disk:
            # all roots of f lie outside the unit disk
            f = f.reverse().monic()
            if not v0.is_equivalence_unit(f):
                V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
                if len(V) > 1:
                    V = [LimitValuation(v, f) for v in V]
                D = [(TypeIPointOnBerkovichLine(self, (v, 1/x)), e) for v in V]
            else:
                D = []
        else:
            # some roots of f lie inside the unit disk
            f = f.monic()
            c = f.base_ring().one()
            while True:
                if v0(f)>=0:
                    break
                c *= vK.uniformizer()
                f = f(f.parent().gen()/vK.uniformizer()) * vK.uniformizer()**f.degree()
            if not v0.is_equivalence_unit(f):
                V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
                if len(V)>1:
                    V = [LimitValuation(v, f) for v in V]
                else:
                    v = V[0]
                    while v(f) < Infinity:
                        v = v.mac_lane_step(f)[0]
                    V = [v]
                D = [(TypeIPointOnBerkovichLine(self, (v, x/c)), e) for v in V]
            else:
                D = []

        return D

#-----------------------------------------------------------------------------

#                             points
#                             ======

class PointOnBerkovichLine(SageObject):
    r"""
    A point on a Berkovich projective line.

    We only allow two different types of points:

    - Type I, algebraic: these are the points that come from a closed point
        on the (algebraic) projective line over the completed base field.
    - Type II: these are the points which correspond to discrete valuations
        on the function field whose residue field is a function field over the
        residue base field

    In particular, the Gauss valuation on `F=K(x)` with respect to the parameter
    `x` corresponds t a point `\xi^g` of type II on `X^{an}` which we call
    the *Gauss point*.

    The set `X^{an}` has a canonical partial ordering in which the Gauss point
    is the smallest elements. All point of type I are maximal elements.

    """
    def __init__(self):
        pass   # Initialization depends on the type


    def berkovich_line(self):
        """
        Return the Berkovich line of which this point lies.
        """
        return self._X


    def function_field(self):
        """
        Return the function field of this Berkovich line.
        """
        return self._F


    def base_field(self):
        """
        Return the base field of this Berkovich line.
        """
        return self._X._vK.domain()


    def base_valuation(self):
        """
        Return the valuation on the base field of this Berkovich line.
        """
        return self._X._vK


    def is_strictly_less(self, xi1):
        """ Check whether ``self`` is strictly smaller than ``xi1``.
        """
        return self.is_leq(xi1) and not self.is_equal(xi1)


    def is_incomparable(self, xi):
        """ Check whether this and another point are incomparable.

        Two point on a Berkovich line are called *incomparable* if neither
        of the two is less or equal to the other. Here we use the natural
        ordering for which the Gauss point is the least element.

        """
        return not self.is_leq(xi) or not xi.is_leq(self)


    def parameter(self):
        r""" Return the parameter of the polynomial ring on which ``self`` is defined.

        The point ``self`` corresponds to a discrete pseudo-valuation
        `v` which is the extension of a pseudo-valuation `v_0` on `K[y]`,
        where `y` is the *parameter* in question.

        """
        return self._y


    def inverse_parameter(self):
        r""" Return the inverse parameter of the polynomial ring on which ``self`` is defined.

        Let `\phi:F\to F` be the automorphism of the function field `F=K(x)` such
        that `Y:=\phi(x)` is the *parameter* used to define ``self``.
        Then the inverse parameter is `z:=\phi^{-1}(x)`.

        """
        if not hasattr(self, "_z"):
            from sage.matrix.constructor import matrix
            y = self.parameter()
            F = y.parent()
            x = F.gen()
            K = F.constant_field()
            num = y.numerator()
            denom = y.denominator()
            A = matrix(K, 2, 2, [num[1], num[0], denom[1], denom[0]])
            assert A.is_invertible(), "y is not a generator!"
            B = A.inverse()
            z = (B[0,0]*x + B[0,1])/(B[1,0]*x + B[1,1])
            assert F.hom(y)(z) == x
            self._z = z
            return z
        else:
            return self._z


#-----------------------------------------------------------------------------

#                    points of type I
#                    ================

class TypeIPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    An algebraic point of type I.

    INPUT:

    - ``X`` -- a Berkovich projective line over a valued field `K`
    - ``v`` -- an infinite discrete pseudovaluation on the function field `F=K(x)`

    OUTPUT: a point of type I on ``X``

    Here the point `\xi` on `X` corresponds to the discrete pseudo-valuation `v` on
    the function field `F=K(x)`.

    Alternatively, ``v`` can be a pair `(v_0,y)`, where `v_0` is an infinite
    discrete pseudo-valuation on a polynomial ring over `K` and `y` is a generator
    of the function field `F`. Then `v` is the infinite discrete pseudo-valuation
    of `F` whose restriction to the subring ring `K[y]`
    is equal to `v_0`.

    """
    def __init__(self, X, v):

        self._X = X
        F = X._F
        x = F.gen()

        if isinstance(v, tuple):
            assert len(v)==2
            v0, y = v
            assert v0.is_discrete_pseudo_valuation()
            assert not v0.is_discrete_valuation()
            # if v were a true valuation, it would correspond to a type II point
            assert y in F, "y must be an element of F"
            assert is_generator(y), "y must be a generator of the function field"
            v1 = F.valuation(v0)
            v = F.valuation((v1, F.hom(y), F.hom(inverse_generator(y))))
        else:
            v0 = v._base_valuation
            if hasattr(v, "_from_base"):
                y = v._from_base(x)
                v0 = v0._base_valuation
            else:
                y = x
        self._F = F
        self._v = v
        self._v0 = v0
        self._y = y
        if v(x) >= 0:
            self._is_in_unit_disk = True
        else:
            self._is_in_unit_disk = False


    def __repr__(self):

        if self.is_inductive():
            if not self.is_infinity():
                return "Point of type I on Berkovich line given by %s = 0"%self.equation()
            else:
                return "The point at infinity on the Berkovich line"
        else:
            f,s = self.approximation().discoid()
            return "Point of type I on Berkovich space approximated by v(%s) >= %s"%(f,s)


    def  type(self):
        """ Return the type of self
        """
        return "I"


    def is_gauss_point(self):
        """ Return True if self is the Gauss point.
        """
        return False   #  self is of type I


    def is_infinity(self):
        """ Check whether ``self`` is the point at infinity."""

        return self.v(self.function_field().gen()) == -Infinity


    def is_in_unit_disk(self):
        r"""
        True is self is contained in the unit disk.
        """
        return self._is_in_unit_disk


    def v(self, f):
        r"""
        Evaluate the pseudo-valuation corresponding to self on ``f``.

        INPUT:

        - ``f`` -- an element of the function field `K(x)`
                   (or of the polynomial ring `K[x]`).

        OUTPUT:

        The value `v(f)`, where v is the pseudo-valuation corresponding to ``self``.

        """
        F = self.function_field()
        return self._v(F(f))


    def pseudovaluation(self):
        r"""
        Return the pseudovaluation corresponding to this point.

        OUTPUT:

        a discrete pseudovaluation on the rational function field of the
        Berkovich line of which ``self`` is a point.
        """
        return self._v


    def pseudovaluation_on_polynomial_ring(self):
        r""" Return the pseudovaluation representing ``self``.

        OUTPUT:

        A discrete pseudovaluation on a polynomial subringring `K[y]`
        from which ``self`` is induced.
        It is either inductive or a limit valuation.

        """
        return self._v0


    def equation(self):
        r""" Return an equation for the Galois orbit of this point.

        OUTPUT: An element `f` of the function field of `X` which is either
        an irreducible polynomial in the standard generator `x`, or is equal to
        `1/x`, and such that `v_\xi(f)=\infty`.

        """
        if self.is_inductive():
            g, s = self.discoid()
            assert s == Infinity
        else:
            # xi is a limit point
            g = self.pseudovaluation_on_polynomial_ring()._G
            g = g(self.inverse_parameter())
        # in both cases, g=0 is a monic irreducible equation for xi
        assert self.v(g) == Infinity
        return g


    def function_field_valuation(self):
        r"""
        Return the function field valuation corresponding to this point

        OUTPUT:

        the discrete valuation on the function field `F=K(x)` which
        corresponds to the image of this point on `X=\mathbb{P}^1_K` (which is,
        by hypothesis, a closed point).

        """
        return self.function_field().valuation(self.equation())


    def is_inductive(self):
        r"""
        Check whether this points corresponds to an inductive valuation.
        """
        return not self.is_limit_point()


    def is_limit_point(self):
        r"""
        Check whether this point corresponds to a limit valuation.
        """
        return hasattr(self.pseudovaluation_on_polynomial_ring(), "_approximation")


    def approximation(self, certified_point=None):
        r"""
        Return an approximation of this point.

        INPUT:

        - ``certified point`` (default=None) -- a point on the Berkovich line

        OUTPUT:

        A a point which is inductive and approximates ``self``, in such a way that
        we can distinguish ``self`` from ``certified point``.

        If ``self`` is an inductive point, then ``self`` is returned. Otherwise,
        ``self`` is a limit point, and the output is a point of type II greater
        or equal to ``self`` (i.e. corresponding to a discoid containing ``self``).
        If ``certified_point`` is not None and distinct from ``self``, then
        the output is not greater or equal to ``certified_point``.

        .. TODO::

            We should also make sure that the approximation has the same degree
            as the point itself. If the point is generated as part of the support of
            a principal divisor, then this should be ok, because of the default
            "require_final_EF=True" in "vK.approximants(f)".

        """
        if not certified_point:
            certified_point = self.berkovich_line().gauss_point()

        if self.is_inductive():
            return self
        else:
            while True:
                w = self.pseudovaluation_on_polynomial_ring()
                y = self.parameter()
                # w is the restriction of self.v to the subring K[y]
                wa = w._approximation
                xi = TypeIIPointOnBerkovichLine(self.berkovich_line(), (wa, y))
                if xi.is_incomparable(certified_point):
                    return xi
                w._improve_approximation()


    def improved_approximation(self):
        r"""
        Return an improved approximation of ``self``.
        """
        if self.is_inductive():
            return self
        w = self.pseudovaluation_on_polynomial_ring()
        y = self.parameter()
        w._improve_approximation()
        wa = w._approximation
        return TypeIIPointOnBerkovichLine(self.berkovich_line(), (wa, y))


    def is_equal(self, xi):
        r"""
        Return ``True`` is self is equal to ``xi``.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)

        We test whether we can distinguish three Galois conjugate points::

            sage: f = 2*x^3 + x^2 + 2*x + 8
            sage: D = X.prime_divisor(f)
            sage: xi1 = D[0][0]
            sage: xi2 = D[1][0]
            sage: xi3 = D[2][0]
            sage: xi1.is_equal(xi2)
            False
            sage: xi2.is_equal(xi3)
            False
            sage: xi3.is_equal(xi1)
            False
            sage: xi1.is_equal(xi1)
            True

        """
        if xi.type() != "I":
            # self is of type I, hence:
            return False
        # now both self and xi are of type I
        if self.is_in_unit_disk() != xi.is_in_unit_disk():
            return False
        if self.is_inductive() != self.is_inductive():
            return False
        if self.v(xi.equation()) < Infinity:
            return False
        elif self.is_inductive():
            # self and xi are both inductive and Galois conjugate,
            # hence they are equal
            return True
        else:
            # now self and xi are Galois conjugate limit points
            # we assume that the actual approximations separate the points
            # in the Galois orbit, see ..
            # this doesn't work, because the may be equal as points but have been created
            # at different moment.
            xi0a = self.approximation()
            xia = xi.approximation(xi0a)
            return xi0a.is_leq(xia)


    def is_leq(self, xi):
        r"""
        Return ``True`` if ``self`` is less or equal to ``xi``.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        ``True`` if self is less or equal to ``xi`` (w.r.t. the natural
        partial order on `X` for which the Gauss point is the smallest element).
        Since self is a point of type I and hence maximal, this is never true
        unless ``xi`` is equal to self.

        """
        return self.is_equal(xi)


    def discoid(self, certified_point=None):
        r"""
        Return a representation of a discoid approximating ``self``.

        INPUT:

        - ``certified_point`` (default=None) -- a point of type II

        OUTPUT:

        A pair `(f, s)`, where `f` is a polynomial in the generator `x` of the
        function field of `X` which is irreducible over `\hat{K}`, or `f=1/x`,
        and where `s` is a nonrational number, or is equal to `\infty`.
        This data represents a (possibly degenerate) discoid `D` via the condition
        `v_\xi(f)\geq s`.

        `D` as above is either the degenerate discoid with `s=\infty` which has
        ``self`` as the unique point, or `D` is an approximation of ``self``
        (this simply means that ``self`` is contained in `D`). If
        ``certified_point`` is given and is not equal to ``self`` then it is
        guaranteed that it is not contained in `D`.

        We further demand that the discoid `D` is either contained in the closed
        unit disk, or is disjoint from it. Such discoids correspond one-to-one
        to points of type II.

        """
        x =  self.function_field().gen()
        if self.is_limit_point():
            xi = self.approximation(certified_point)
            return xi.discoid()
        elif self.is_infinity():
            return 1/x, Infinity
        else:
            v0 = self.pseudovaluation_on_polynomial_ring()
            y = self.parameter()
            f = v0.phi()(y).numerator().monic()(x)
            return f, Infinity


    def infimum(self, xi2):
        r"""
        Return the infimum of self and `\xi_2`.

        INPUT:

        - ``xi2`` -- a point of type I or II on the Berkovich line

        OUTPUT: The infimum of self and `\xi_2`. Unless self or `\xi_2` are equal,
        this is a point of type II.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: D = X.divisor(4*x^4+x^3+x^2+2*x+8)
            sage: for i in range(len(D)):
            ....:     for j in range(i, len(D)):
            ....:         xi1 = D[i][0]
            ....:         xi2 = D[j][0]
            ....:         xi3 = xi1.infimum(xi2)
            ....:         assert xi3.is_leq(xi1)
            ....:         assert xi3.is_leq(xi2)

        """
        X = self.berkovich_line()
        x = X.function_field().gen()
        xi1 = self
        if xi2.type() == "II":
            return xi2.infimum(xi1)
        if xi1.is_leq(xi2):
            return xi1
        if xi2.is_leq(xi1):
            return xi2

        # now both points are of type I and uncomparable;
        # the infimum must be of type II
        # we replace them by approximations which are incomparable
        xi1 = xi1.approximation(xi2)
        xi2 = xi2.approximation(xi1)
        assert xi1.is_incomparable(xi2)

        if xi1.is_in_unit_disk() != xi2.is_in_unit_disk():
            return X.gauss_point()

        # now the point lie both inside or outside the unit disk
        f1, s1 = xi1.discoid()
        f2, s2 = xi2.discoid()
        if f1 == 1/x:
            return X.point_from_discoid(f1, xi2.v(f1))
        else:
            return X.point_from_discoid(f2, xi1.v(f2))


#----------------------------------------------------------------------------

#                  points of type II
#                  =================

class TypeIIPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    A point of type II on a Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line over a valued field K
    - ``v`` -- a discrete valuation on the function field of X extending the base valuation

    OUTPUT: the type-II-point `\xi` on `X` corresponding to `v`.

    It is also possible to replace ``v`` by a pair ``(v0, y)``, where ``v0``
    is a discrete valuation on a polynomial ring `K[x]`, and ``y`` is a parameter
    for the function field of the Berkovich line. Then `\xi` is the point
    corresponding to the valuation `v` on the function field `F=K(x)` which pulls
    back to `v_0` via the inclusion `K[x]\to F` that sends `x` to `y`.

    """
    def __init__(self, X, v):
        self._X = X
        F = X._F
        x = F.gen()
        vK = X.base_valuation()

        if isinstance(v, tuple):
            # instaed of v we have gotten a pair (v0, y); we need to create v
            assert len(v)==2
            v0, y = v
            assert v0.is_discrete_valuation()
            # if v were a not true valuation, it would correspond to a type I point
            assert y in F, "y must be an element of F"
            assert is_generator(y), "y must be a generator of the function field"
            z = inverse_generator(y)
            v = F.valuation(v0)
            v = F.valuation((v, F.hom(y), F.hom(z)))
        else:
            # create a pair (v0, y) from y
            assert v.domain() is F, "the domain of v is not the function field of X"
            assert v.is_discrete_valuation(), "v must be a discrete valuation"
            is_in_unit_disk = (v(x) >= 0)
            if hasattr(v, "_from_base"):
                y = v._from_base(x)
                z = inverse_generator(y)
                v0 = v._base_valuation._base_valuation
            else:
                y = x
                z = x
                v0 = v._base_valuation

        # create a standard discoid representation for v
        is_in_unit_disk = (v(x)>=0)
        if is_in_unit_disk:
            f = v0.phi()(z).numerator().monic()
            s = v(f(x))
            v0 = valuation_from_discoid(vK, f, s)
            v = F.valuation(v0)
            y = x
        else:
            f = v0.phi()(z)
            if f.numerator()[0] == 0:
                f = x.numerator()
                s = -v(x)
            else:
                f = F.hom(1/x)(f).numerator().monic()
                s = v(f(1/x))
            v0 = valuation_from_discoid(vK, f, s)
            v = F.valuation(v0)
            v = F.valuation((v, F.hom(1/x), F.hom(1/x)))
            y = 1/x

        self._v = v
        self._is_in_unit_disk = is_in_unit_disk
        self._v1 = v0
        self._y = y
        self._F = F
        self._X = X


    def __repr__(self):
        return "Point of type II on Berkovich line, corresponding to v(%s) >= %s"%self.discoid()


    def type(self):
        """ Return the type of self.
        """
        return "II"


    def is_gauss_point(self):
        """ Return True if self is the Gauss point.
        """
        x = self._X.function_field().gen()
        if self.v(x) != 0:
            return False

        v1 = self._v1
        while not hasattr(self._v1, "is_gauss_valuation"):
            v1 = v1._base_valuation
        return v1.is_gauss_valuation()


    def is_infinity(self):
        """ Check whether ``self`` is the point at infinity."""

        return False  # self is of type II


    def is_in_unit_disk(self):
        r"""
        True is self is contained in the unit disk.
        """
        return self._is_in_unit_disk


    def v(self, f):
        r"""
        Evaluate element of the function field on the valuation corresponding to self.

        INPUT:

        - ``f`` -- an element of the function field of the underlying projective line

        OUTPUT:

        the value `v(f)`, where `v` is the valuation corresponding to self
        """
        return self._v(f)


    def is_inductive(self):
        r""" True if ``self`` corresponds to an inductive pseud-valuation.
        This is always true for points of type II.
        """
        return True


    def is_limit_point(self):
        r""" True is ``self`` corresponds to a limit valuation.
        This is never true for points of type II.
        """
        return False


    def pseudovaluation(self):
        r"""
        Return the pseudovaluation corresponding to this point.

        OUTPUT:

        Since ``self`` is a point of type II, the output is a discrete
        valuation on the function field of the underlying Berkovich line.

        """
        return self._v


    def valuation(self):
        r"""
        Return the valuation corresponding to this point.

        OUTPUT:

        The discrete valuation on the function field of the underlying Berkovich
        line corresponding to this point.

        """
        return self._v


    def pseudovaluation_on_polynomial_ring(self):
        r""" Return the pseudo-valuation on the polynomial ring 'K[y]'
        corresponding to ``self``, where `y` is either `x` or `1/x` depending
        on whether self lies in the standard closed unit disk or not.
        """
        # if self.is_in_unit_disk() or self.is_gauss_point():
        #     return self._v._base_valuation
        # else:
        #    return self._v._base_valuation._base_valuation
        return self._v1


    def parameter(self):
        r""" Return the parameter with respect to which this point is defined.

        This is either `x` (if the point lies in the unit disk) or `1/x` otherwise.

        """
        x = self.berkovich_line().function_field().gen()
        if self.is_in_unit_disk():
            return x
        else:
            return 1/x


    def approximation(self):
        r""" Return an approximation of ``self``.
        For a point of type II, ``self`` is already an approximation of itself.
        """
        return self


    def improved_approximation(self):
        r""" Return an improved approximation of ``self``.

        This is meaningless for type-II-points, so self is returned.
        """
        return self


    def discoid(self, certified_point=None):
        r"""
        Return a representation of the discoid of which ``self`` is the
        unique boundary point.

        INPUT:

        - ``certified_point`` (default=None) -- this argument is not used
           for type-II-points

        OUTPUT:

        A pair `(f, s)`, where `f` is a polynomial in the generator `x` of the
        function field of `X` which is irreducible over `\hat{K}`, or `1/x`,
        and where `s` is a nonnegative rational number. This data represents a
        discoid `D` via the condition `v_\xi(f)\geq s`.

        Then ``self`` is the unique boundary point of `D`, and if, moreover,
        ``self`` is not the Gauss point then `D` contains precisely the points
        `\xi` which are greater or equal to ``self``. If ``self`` is the Gauss
        point then `D` is the standard closed unit disk, `f=x` and `s=0`.

        """
        xi = self
        x = xi.function_field().gen()
        if xi.is_gauss_point():
            return x, 0
        v = xi.pseudovaluation_on_polynomial_ring()
        phi = v.phi()
        if self.is_in_unit_disk():
            f = phi(x)
            s = xi.v(f)
            return f, s
        else:
            if phi[0] == 0:
                f = 1/x
            else:
                f = phi(1/x).numerator()(x)
            s = xi.v(f)
            return f, s


    def is_equal(self, xi):
        r"""
        Return ``True`` if self is equal to ``xi``.
        """
        if xi.type() != "II":
            return False
        return self.is_leq(xi) and xi.is_leq(self)


    def is_leq(self, xi):
        r"""
        Return ``True`` if self is less or equal to ``xi``.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT: ``True`` if self is less or equal to ``xi`` (w.r.t. the natural
        partial order on `X`), ``False`` otherwise.

        If ``self`` is the Gauss point, then we return ``True``.
        Otherwise we check whether ``xi`` is contained in the discoid `D`
        corresponding to ``self``.

        """
        if self.is_gauss_point():
            return True      # the Gauss point is the least element of X
        if self.is_in_unit_disk() != xi.is_in_unit_disk():
            return False
        else:
            f, s = self.discoid()
            return xi.v(f) >= s


    def infimum(self, xi2):
        r"""
        Return the infimum of self and ``xi2``.

        INPUT:

        - ``xi2`` -- a point of type I or II on the Berkovich line

        OUTPUT:

        The infimum of self and `\xi_2` (w.r.t. to the natural partial ordering).
        Unless `\xi_2=\infty` or self is equal to `\xi_2`,
        the result is a point of type II.

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: xi = [X.point_from_discoid(x^2+2, 3)]
            sage: xi.append(X.point_from_discoid(x, 2))
            sage: xi.append(X.point_from_discoid(2*x+1, 3))
            sage: xi.append(X.infty())
            sage: for i in range(4):
            ....:     for j in range(i, 4):
            ....:         xi1 = xi[i]
            ....:         xi2 = xi[j]
            ....:         xi3 = xi1.infimum(xi2)
            ....:         assert xi3.is_leq(xi1)
            ....:         assert xi3.is_leq(xi2)

        """
        X = self.berkovich_line()
        x = X.function_field().gen()
        xi1 = self
        if xi1.is_leq(xi2):
            return xi1
        if xi2.is_leq(xi1):
            return xi2
        # now the points are uncomparable, and the infinum is a point of type II

        if xi1.is_in_unit_disk() != xi2.is_in_unit_disk():
            return X.gauss_point()
        # now the point lie both inside or outside the unit disk
        f1, s1 = xi1.discoid()
        f2, s2 = xi2.discoid()
        if f1 == 1/x:
            return X.point_from_discoid(f1, xi2.v(f1))
        else:
            return X.point_from_discoid(f2, xi1.v(f2))


    def point_in_between(self, xi1):
        r"""
        Return a point in between ``self`` and ``xi1``.

        INPUT:

        - ``xi1`` -- a point which is strictly larger than ``self``

        OUTPUT: a point which lies strictly between ``self`` and ``xi1``

        EXAMPLES::

            sage: from mclf import *
            sage: v_2 = QQ.valuation(2)
            sage: F.<x> = FunctionField(QQ)
            sage: X = BerkovichLine(F, v_2)
            sage: xi0 = X.gauss_point()
            sage: xi1 = X.point_from_discoid(x,1)
            sage: xi2 = X.point_from_discoid(x^2 - 8, 4)
            sage: xi3 = X.point_from_discoid(2*x-1, 2)
            sage: xi4 = X.infty()
            sage: xi0.point_in_between(xi1)
            Point of type II on Berkovich line, corresponding to v(x) >= 1/2
            sage: xi0.point_in_between(xi2)
            Point of type II on Berkovich line, corresponding to v(x) >= 1
            sage: xi0.point_in_between(xi3)
            Point of type II on Berkovich line, corresponding to v(-2*x + 1) >= 1
            sage: xi0.point_in_between(xi4)
            Point of type II on Berkovich line, corresponding to v(1/x) >= 1
            sage: xi1.point_in_between(xi2)
            Point of type II on Berkovich line, corresponding to v(x) >= 3/2

        """
        xi0 = self
        X = xi0.berkovich_line()
        assert xi0.is_leq(xi1) and not xi0.is_equal(xi1), "xi1 must be strictly larger than self"
        f1, s1 = xi1.discoid()
        s0 = xi0.v(f1)
        assert s0 < s1, "strange: s0>=s1, but xi0 < xi1"
        if s1 == Infinity:
            s2 = s0 + 1
        else:
            s2 = (s0+s1)/2
        xi2 = X.point_from_discoid(f1, s2)
        assert xi0.is_leq(xi2) and not xi0.is_equal(xi2), "xi0 is not less than xi2!"
        assert xi2.is_leq(xi1) and not xi2.is_equal(xi1), "xi2 is not less than xi1!"
        return xi2



#-------------------------------------------------------------------------

#                        auxiliary functions
#                        ===================


def valuation_from_discoid(vK, f, s):
    r""" Return the inductive valuation corresponding to a discoid.

    INPUT:

    - ``vK`` -- a discrete valuation on a field `K`
    - ``f`` -- a nonconstant monic integral polynomial over `K`
    - ``s`` -- a nonnegative rational number, or `\infty`

    OUTPUT:

    an inductive valuation ``v`` on the domain of ``f``, extending ``vK``,
    corresponding to the discoid `D` defined by `w(f)\geq s`. In other words,
    this means that `D` defined above is irreducible (and hence a discoid),
    and `v` is its unique boundary point.

    If `D` is not irreducible, an error is raised.
    """

    R = f.parent()
    K = R.base_ring()
    assert K is vK.domain()
    v0 = GaussValuation(R, vK)
    assert f.is_monic()
    assert v0(f) >= 0
    assert s >= 0, "f = %s, s = %s"%(f, s)
    v = v0
    while v(f) < s:
        V = v.mac_lane_step(f)
        assert len(V) == 1, "D is not a discoid"
        v = V[0]
    if v(f) == s:
        return v
    else:
        # now v is an inductive valuation such that v(f) > s
        for v0 in v.augmentation_chain():
            if v0(f) <= s:
                break
            else:
                v = v0
        if v0(f) == s:
            return v0
        # now v0 is an inductive valuation such that v0(f) < s,
        # and v is an augmentation of v0 such that v(f) > s.
        # We test this:
        assert v0(f) < s
        assert v(f) > s
        assert v._base_valuation == v0
        a = [v0(c) for c in v.coefficients(f)]
        t = max([(s-a[i])/i for i in range(1,len(a)) ])
        v = v0.augmentation(v.phi(), t)
        assert v(f) == s
        return v


def valuations_from_inequality(vK, f, s, v0=None):
    r"""
    Return the list of inductive valuations corresponding to the given inequlities.

    INPUT:

    - ``vK`` -- a discrete valuation on a field `K`
    - ``f`` -- a nonconstant monic integral polynomial over `K`
    - ``s`` -- a nonnegative rational number, or `\infty`
    - ``v0`` -- an inductive valuation on the parent of ``f`` (default: ``None``)

    OUTPUT:

    a list of inductive valuations on the domain of ``f``, extending ``vK``,
    corresponding to the boundary points of the irreducible components of the
    affinoid defined by the condition `v(f)\geq s`. Note that these components
    are all discoids.

    If `v_0` is given then the output only includes the valuations greater or
    equal to `v_0`.

    """
    R = f.parent()
    K = R.base_ring()
    assert K is vK.domain()
    if v0 == None:
        v0 = GaussValuation(R, vK)
    else:
        assert f in v0.domain()
    assert f.is_monic()
    assert v0(f) >= 0
    assert s >= 0
    V = [v0]
    V_new = []
    ret = []
    while len(V) > 0:
        # V contains all valuations which still need to be developped
        V_new = []
        for v in V:
            vf = v(f)
            if vf < s:
                V_new += v.mac_lane_step(f)
            elif vf == s:
                if all([not v == w for w in ret]):
                    ret.append(v)
            else:
                # now v is an inductive valuation such that v(f) > s
                for v0 in v.augmentation_chain():
                    if v0(f) <= s:
                        break
                    else:
                        v = v0
                if v0(f) == s:
                    if all([not v == w for w in ret]):
                        ret.append(v0)
                # now v0 is an inductive valuation such that v0(f) < s,
                # and v is an augmentation of v0 such that v(f) > s.
                # We test this:
                assert v0(f) < s
                assert v(f) > s
                assert v._base_valuation == v0
                a = [v0(c) for c in v.coefficients(f)]
                t = max([(s-a[i])/i for i in range(1,len(a)) ])
                v = v0.augmentation(v.phi(), t)
                assert v(f) == s
                if all([not v == w  for w in ret]):
                    ret.append(v)
        V = V_new
    return ret


def is_generator(y):
    r""" Test whether an element is a generator of a rational function field.

    INPUT:

    - ``y`` - an element of a rational function field `F=K(x)`

    OUTPUT: ``True`` if `F=K(y)`, ``False`` otherwise.

    """

    n = y.numerator().degree()
    m = y.denominator().degree()
    return not y.is_zero() and max([n,m]) == 1


def inverse_generator(y):
    r""" Return the inverse generator of a given generator of a rational function field.

    INPUT:

    - ``y`` - a generator of a rational function field `F=K(x)`

    OUTPUT: the inverse generator for `y`. So if `\phi:F\to F` is the automorphism
    of `F` such that `\phi(x)=y` then `z:=\phi^{-1}(x)` is the inverse generator.

    """

    from sage.matrix.constructor import matrix

    F = y.parent()
    x = F.gen()
    K = F.constant_field()
    num = y.numerator()
    denom = y.denominator()
    A = matrix(K, 2, 2, [num[1], num[0], denom[1], denom[0]])
    assert A.is_invertible(), "y is not a generator!"
    B = A.inverse()
    z = (B[0,0]*x + B[0,1])/(B[1,0]*x + B[1,1])
    assert F.hom(y)(z) == x
    return z
