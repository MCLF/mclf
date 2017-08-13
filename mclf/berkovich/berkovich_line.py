r"""
The Berkovich projective line over a discretely valued field.
=============================================================

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
    - Type I, algebraic: these are the points that come from a closed point
      on the (algebraic) projective line over the completed base field.
    - Type II: these are the points which correspond to discrete valuations
      on the function field whose residue field is a function field over the
      residue base field
For both these kind of points, the corresponding pseudovaluation on `F` are
directly realizable inside the ``mac_lane`` infrastructure.

If `v_\xi(x)\geq 0` we say that `\xi` lies *in the unit disk*. Then the
restriction of `v_\xi` to `K[x]` is a discrete pseudo-valuation which can be
realized either as an inductive valuation, or as a limit valuation.

If `\xi` does not lie in the unit disk, then we use instead the restriction
of `v_\xi` to the polynomial ring `K[x^{-1}]` (internally, we use the ring
`K[x]`, though).

By a result of Berkovich, the topological space `X^{an}` is a *simply connected
quasi-polyhedron*. Among other things this means that for any two points
`\xi_1,\xi2\in X^{an}` there exists a unique closed subset

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

where `f` is a polynomial in `x` or in `x^{-1}`, irreducible over
`\hat{\bar{K}}` and `s` is a nonnegativ rational number.
The pair `(f,s)` determines `\xi`, but this representation is not unique.

Note that we can simply extend the discoid representation to points of type I
by allowing `s` to take the value `\infty`.

AUTHORS:

- Stefan Wewers (2017-02-10): initial version


EXAMPLES::

<Lots and lots of examples>


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
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.structure.sage_object import SageObject
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import Infinity
from sage.functions.generalized import sgn
from sage.geometry.newton_polygon import NewtonPolygon
from mac_lane import *


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

        return PolynomialRing(self.constant_base_field(), self.function_field().variable_name())

    def make_polynomial(self, f, in_unit_disk=True):
        r""" Turn ``f`` into a polynomial.

        INPUT:

        - ``f`` -- an element of `F=K(x)` or of `K[x]`
        - ``in_unit_disk`` -- boolean

        OUTPUT:

        Either `f` of `f(1/x)`, considered as a polynomial in `K[x]`,
        and depending on whether ``in_unit_disk`` is true or false.
        """

        R = self.polynomial_ring()
        if f.parent() is R:
            return f
        F = self.function_field()
        x = F.gen()
        if in_unit_disk:
            # return R(f)
            assert f.denominator().is_one(), "f is not a polynomial in x"
            return f.numerator()
        else:
            f = F.hom([1/x])(f)
            assert f.denominator().is_one(), "f is not a polynomial in x"
            return f.numerator()


    def infty(self):
        r"""
        Return the point `\infty`.
        """

        R = self._F._ring
        F = self._F
        x = F.gen()
        v0 = GaussValuation(R, self._vK)
        v1 = v0.augmentation(R.gen(), Infinity)
        v1 = FunctionFieldValuation(F, v1)
        v1 = FunctionFieldValuation(F, (v1, F.hom([1/x]), F.hom([1/x])))
        return TypeIPointOnBerkovichLine(self, v1)

    def gauss_point(self):
        r"""
        Return the Gauss point of self.

        The Gauss point is the type-II-point corresponding to the Gauss
        valuation on `K[x]`.
        """

        v0 = GaussValuation(self._F._ring, self._vK)
        v0 = FunctionFieldValuation(self._F, v0)
        return TypeIIPointOnBerkovichLine(self, v0)

    def point_from_polynomial_pseudovaluation(self, v, in_unit_disk=True):
        r""" Return the point corresponding to a pseudo-valuation on a poylnomial ring.

        INPUT:

        - ``v`` -- a discrete pseudo-valuation on the polynomial ring `K[x]`,
                extending the base valuation `v_K`
        - ``in_unit_disk`` (default=True) -- boolean

        OUTPUT:

        The point on the unit disk corresponding to ``v`` (if ``in_unit_disk``
        is true), or the point on the inverse unit disk corresponding to ``v``.
        """

        F = self.function_field()
        x = F.gen()
        v = FunctionFieldValuation(F, v)
        if not in_unit_disk:
            v = FunctionFieldValuation(F, (v, F.hom([1/x]), F.hom([1/x])))
        return self.point_from_pseudovaluation(v)


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


    def point_from_discoid(self, phi, s, in_unit_disk=True):
        r"""
        Return the point on ``self`` determined by a discoid.

        INPUT:

        - ``phi`` -- a monic and integral polynomial in `K[x]`
        - ``s`` -- a nonnegative rational number, or `\infty`
        - ``in_unit_disk`` -- a boolean (default: True)

        OUTPUT:

        a point `\xi` on the Berkovich line ``self`` which is the unique
        boundary point of the discoid `D` determined as follows: if
        ``in_unit_disk`` is true then `D` is the set of valuations `v` on
        `K[x]` such that `v(\phi)\geq s`. Otherwise, it is the image of this
        point under the automorphism `x\to 1/x`.

        If `D` defined above is not irreducible (and hence not a discoid) then
        an error is raised.
        """

        phi = self.make_polynomial(phi)
        F = self.function_field()
        x = F.gen()
        v = valuation_from_discoid(self._vK, phi, s)
        v = FunctionFieldValuation(F, v)
        if not in_unit_disk and s>0:
            assert v(x) > 0, "The point does lie in the unit disk"
            v = FunctionFieldValuation(F, (v, F.hom([1/x]), F.hom([1/x])))
        return self.point_from_pseudovaluation(v)

    def points_from_inequality(self, f, s):
        r"""
        Return the boundary points of the affinoid given an inequality.

        INPUT:

        - ``f`` -- a monic and integral polynomial in `x` or in `1/x`
        - ``s`` -- a nonnegative rational number, or `\infty`

        OUTPUT:

        a list of points which are the boundary points of the affinoid given
        by the inequality `v(f) \geq s`. Note that the affinoid is a union
        of finitely many discoids (or of finitely many algebraic points if
        `s=\infty`).

        .. NOTE::

            For the moment we have to assume that if `f=g(1/x)`, then all the
            roots of `g` have strictly positive valuations.

        """
        vK = self.base_valuation()
        F = self.function_field()
        x = F.gen()
        if f.denominator().is_one():
            # f is a polynomial in x
            f = f.numerator()
            V = valuations_from_inequality(vK, f, s)
            V = [FunctionFieldValuation(F, v) for v in V]
            return [self.point_from_pseudovaluation(v) for v in V]
        else:
            # f should now be a polynomial in 1/x
            f = F.hom([1/x])(f)
            assert f.denominator().is_one(), 'f is not a polynomial in x or 1/x'
            g = f.numerator()
            assert all( [ vK(g[i]) > 0 for i in range(g.degree())]), \
                "the roots of g must have negative valuation"
            V = valuations_from_inequality(vK, g, s)
            V = [FunctionFieldValuation(F, v) for v in V]
            V = [FunctionFieldValuation(F, (v, F.hom([~x]), F.hom([~x]))) for v in V]
            return [self.point_from_pseudovaluation(v) for v in V]


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

        NOTE::

        We are assuming for the moment that the function

        .. MATH::

             v \mapsto v(f)

        is affine (i.e. has no kinks) on the interval `[\xi_1,\xi_2]`.

        """

        from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine

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
        xi2_approx = xi2.approximation()
        count = 0
        while sgn(xi2_approx.v(f)) != sgn(h2) and count < 20:
            xi2_approx = xi2.improved_approximation()
            count += 1
        assert count < 20, "could not find sufficient approximation!"

        phi, s2 = xi2.discoid()
        s1 = xi1.v(phi)
        # we are looking for t, s1 < t < s2, such that f has zero valuation
        # at the point xi_t: v(phi) >= t.
        eta = TypeVPointOnBerkovichLine(xi1, xi2)
        m = eta.derivative(f)
        n = eta.derivative(phi)
        # now the function t |--> v_t(f) has slope m/n
        t = s1 - n*h1/m
        if xi2.is_in_unit_disk():
            xi3 = xi1._X.point_from_discoid(phi, t)
        else:
            # phi should be a monic polynomial in 1/x
            x = self.function_field().gen()
            phit= self._F.hom([1/x])(phi)
            phi1 = phit.numerator()
            assert phit.denominator().is_one()
            xi3 = xi1._X.point_from_discoid(phi1, t, in_unit_disk=False)
        assert xi3.v(f) ==0, "got the wrong point xi3!"
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
            D = D + self.polynomial_divisor(g, e)
        d = f.numerator().degree()-f.denominator().degree()
        if d != 0:
            D.append((self.infty(), -d))
        return D

    def polynomial_divisor(self, f, m):
        r"""
        Return the divisor of zeroes of a squarefree polynomial.


        INPUT:

         - ``f`` -- a squarefree polynomial in the generator of the function
                    field of self
         - ``m`` -- an integer

        OUTPUT:

        The divisor of `f`, multiplied with `m`.

        NOTE:

        At the moment, we must require that the Newton polygon of `f` has
        either only nonpositive or only positive slopes. So the zeroes of
        `f` lie all inside the closed unit disk, or all outside.

        """

        F = self._F
        x = F.gen()
        assert f.parent() is F, "f must lie in the function field of X"
        assert f.denominator().is_one(), "f must be a polynomial"
        f = f.numerator()
        assert f.is_squarefree(), "f is not squarefree"
        R = f.parent()
        vK = self._vK
        v0 = GaussValuation(R, vK)

        # we check that the additional conditon on f holds, and
        # decide whether the roots lie inside or outside the unit disk
        NP = NewtonPolygon([(i, vK(f[i])) for i in range(f.degree() + 1)])
        slopes = NP.slopes()
        assert slopes == [] or max(slopes) <= 0 or min(slopes) >0,\
            "all roots of f must either lie inside or outside the unit disk"
        is_in_unit_disk = (slopes == [] or max(slopes) <= 0)


        # this is the part inside the unit disk
        if is_in_unit_disk:
            f = f.monic()
            if not v0.is_equivalence_unit(f):
                V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
                V = [LimitValuation(v, f) for v in V if not v.is_gauss_valuation()]
                V = [FunctionFieldValuation(F, v) for v in V]
                D = [(TypeIPointOnBerkovichLine(self, v), m) for v in V]
            else:
                D = []
        else:
            # the part outside the unit disk
            f = f.reverse().monic()
            if not v0.is_equivalence_unit(f):
                V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
                V = [LimitValuation(v, f) for v in V]
                V = [v for v in V if v(x) > 0]
                V = [FunctionFieldValuation(F, v) for v in V]
                V = [FunctionFieldValuation(F, (v, F.hom([1/x]), F.hom([1/x]))) for v in V]
                D = [(TypeIPointOnBerkovichLine(self, v), m) for v in V]
            else:
                D = []

        # some points may only be approximations; we want to make sure that
        # these are sufficiently precise to distinguish all points of D
        for i in range(len(D)):
            xi = D[i][0]
            if xi.is_limit_point():
                for j in range(len(D)):
                    if i != j:
                        xi.approximation(D[j][0].approximation())
        return D

#-----------------------------------------------------------------------------

#                   generic points
#                   ==============

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


    def make_polynomial(self, f):
        r""" Return the polynomial corresponding to ``f``.

        INPUT:

        - ``f`` -- an element of `F=K(x)`

        OUTPUT:

        If ``f`` is an element of the function field `F=K(x)` the we return
           - f as an element of `K[x]` if possible and ``self`` lies in the unit disk
           - f(1/x) as an element of `K[x]` if possible and ``lies outside the unit disk
        Otherwise an error is raised.

        This function is useful to converting elements of the function field to
        elements of the domain of the MacLane valuation underlying ``self``.
        """

        R = self._v._base_valuation.domain()
        if f.parent() is self.berkovich_line().function_field() and not self.is_in_unit_disk():
            print "f =", f
            return R(f(1/self.berkovich_line().function_field().gen()))
        else:
            return R(f)

#-----------------------------------------------------------------------------

#                    points of type I
#                    ================

class TypeIPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    An algebraic point of type I.

    INPUT:

    - `X` -- a Berkovich projective line over a valued field `K`
    - `v` -- an infinite pseudo-valuation on the function field of `X`


    OUTPUT:

    The point on `X` corresponding to `v`.
    """

    def __init__(self, X, v):

        self._X = X
        F = X._F
        K = F.constant_base_field()
        x = F.gen()
        assert v.is_discrete_pseudo_valuation()
        assert not v.is_discrete_valuation()
        # if v were a true valuation, it would correspond to a type II point
        self._v = v
        x = F.gen()
        if v(x) >= 0:
            self._is_in_unit_disk = True
            self._v1 = v._base_valuation
        else:
            self._is_in_unit_disk = False
            self._v1 = v._base_valuation._base_valuation


    def __repr__(self):
        f, s = self.discoid()
        if s == Infinity:
            return "Point of type I on Berkovich line given by %s = 0"%f
        else:
            return "Point of type I on Berkovich space approximated by %s >= %s"%(f,s)

    def  type(self):
        """ Return the type of self
        """
        return "I"


    def is_gauss_point(self):
        """ Return True if self is the Gauss point.
        """
        return False   #  self is of type I


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
        If `f` is in `K[x]` then we take for `v` the MacLane pseudo-valuation
        corresponding to ``self``.

        """
        if f.parent() is self.berkovich_line().function_field():
            return self._v(f)
        else:
            return self.pseudovaluation_on_polynomial_ring()(f)


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

        A discrete pseudovaluation on the polynomial ring `K[x]` representing ``self``.
        It is either inductive or a limit valuation.
        """
        if self._is_in_unit_disk:
            return self._v._base_valuation
        else:
            return self._v._base_valuation._base_valuation


    def function_field_valuation(self):
        r"""
        Return the function field valuation corresponding to this point

        OUTPUT:

        the discrete valuation on the function field `F=K(x)` of `X^{an}` which
        corresponds to the image of this point on `X=\mathbb{P}^1_K` (which is,
        by hypothesis, a closed point).

        """
        F = self.berkovich_line().function_field()
        if self.is_inductive():
            g, s = self.discoid()
            if not self.is_in_unit_disk():
                if not g.numerator().is_one():
                    # xi is not in the unit disk, and is not infty
                    g = g.numerator().monic()
                else:
                    # xi is infty
                    g = 1/F.gen()
            # now g=0 is a monic irreducible equation for xi
        else:
            # xi is a limit point
            g = self.pseudovaluation_on_polynomial_ring()._G
            if not self.is_in_unit_disk():
                g = g.reverse().monic()
        # in both cases, g=0 is a mnic irreducible equation for xi
        return FunctionFieldValuation(F, g)


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
        if self.is_inductive():
            return self
        w = self.pseudovaluation_on_polynomial_ring()
        wa = w._approximation
        if certified_point != None and not self.is_equal(certified_point) and self.is_in_unit_disk() == certified_point.is_in_unit_disk():
            # we have to make sure that our approximation is good enough
            # to not include certified_point
            w1 = certified_point.pseudovaluation_on_polynomial_ring()
            while wa <= w1:
                w._improve_approximation()
                wa = w._approximation
        X = self._X
        return X.point_from_polynomial_pseudovaluation(wa, self.is_in_unit_disk())


    def improved_approximation(self):
        r"""
        Return an improved approximation of ``self``.
        """
        if self.is_inductive():
            return self
        w = self.pseudovaluation_on_polynomial_ring()
        w._improve_approximation()
        X = self._X
        return X.point_from_polynomial_pseudovaluation(w._approximation, self.is_in_unit_disk())


    def is_equal(self, xi):
        r"""
        Return ``True`` is self is equal to ``xi``.
        """
        if xi.type() != "I":
            return False
        if self.is_in_unit_disk() != xi.is_in_unit_disk():
            return False
        elif not self.is_in_unit_disk():
            v1 = self._v._base_valuation
            v2 = xi._v._base_valuation
            return equality_of_pseudo_valuations(v1, v2)
        else:
            return equality_of_pseudo_valuations(self._v, xi._v)


    def is_leq(self, xi):
        r"""
        Return ``True`` if ``self`` is less or equal to ``xi``.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        ``True`` if self is less or equal to ``xi`` (w.r.t. the natural
        partial order on `X` for which the Gauss pont is the smallest element).
        Since self is a point of type I and hence maximal, this is never true
        unless `xi` is equal to self.

        """
        return self.is_equal(xi)


    def discoid(self, certified_point=None):
        r"""
        Return a representation of a discoid approximating ``self``.

        INPUT:

        - ``certified_point`` (default=None) -- a point of type II

        OUTPUT:

        A pair `(f, s)`, where `f` is a polynomial in the generator `x` of the
        function field of `X`, or `f=1/x`, and where `s` is a nonrational number,
        or is equal to `\infty`.
        This data represents a (possibly degenerate) discoid `D` via the condition
        `v_\xi(f)\geq s`.

        `D` as above is either the degenerate discoid with `s=\infty` which has
        ``self`` as the unique point, or `D` is an approximation of ``self``
        (this simply means that ``self`` is contained in `D`). If
        ``certified_point`` is given then it is guaranteed that it is not
        contained in `D`.
        """
        if self.is_limit_point():
            xi = self.approximation(certified_point)
        else:
            xi = self
        v = xi.pseudovaluation_on_polynomial_ring()
        phi = v.phi()
        if self.is_in_unit_disk():
            f = phi(self._X._F.gen())
            s = xi.v(f)
            return f, s
        else:
            x = self._X._F.gen()
            if phi[0] == 0:
                f = 1/x
            else:
                # f = x**(phi.degree())*phi(1/x)  this may lead to errors
                f = phi(1/x)
            s = xi.v(f)
            return f, s


    def infimum(self, xi2):
        r"""
        Return the infimum of self and `\xi_2`.

        INPUT:

        - ``xi2`` -- a point of type I or II on the Berkovich line

        OUTPUT:

        The infimum of self and `\xi_2`. Unless self or `\xi_2` are equal,
        this is a point of type II.
        """
        if xi2.type() == "II":
            return xi2.infimum(self)
        if self.is_leq(xi2):
            return self
        if xi2.is_leq(self):
            return xi2

        # now both points are of type I and uncomparable;
        # the infimum must be of type II
        if self.is_in_unit_disk() and xi2.is_in_unit_disk():
            v1 = self._v._base_valuation
            v2 = xi2._v._base_valuation
            R = v1.domain()
            assert v2.domain() is R

            # we have to find an approximation of v1 which is incomparable to v2
            if hasattr(v1, "_approximation"):
                w1 = v1._approximation
            else:
                w1 = v1
            if hasattr(v2, "_approximation"):
                w2 = v2._approximation
            else:
                w2 = v2
            # the current approximations should work, because we have tested
            # whether v1 <= v2 and v2 <= v1!
            assert w1(w1.phi()) > w2(w1.phi()), "bad approximation: w1 <= w2"
            assert w2(w2.phi()) > w1(w2.phi()), "bad approximation: w2 <= w1"
            w3 = mac_lane_infimum(w1, w2)
            v3 = FunctionFieldValuation(self._X._F, w3)
            return TypeIIPointOnBerkovichLine(self._X, v3)
        if (not self.is_in_unit_disk()) and (not xi2.is_in_unit_disk()):
            v1 = self.pseudovaluation_on_polynomial_ring()
            v2 = xi2.pseudovaluation_on_polynomial_ring()
            R = v1.domain()
            assert v2.domain() is R
            # we have to find an approximation of v1 which is incomparable to v2
            if hasattr(v1, "_approximation"):
                w1 = v1._approximation
            else:
                w1 = v1
            if hasattr(v2, "_approximation"):
                w2 = v2._approximation
            else:
                w2 = v2
            # the current approximations should work, because we have tested
            # whether v1 == v2!
            w3 = mac_lane_infimum(w1, w2)
            F = self._X._F
            x = F.gen()
            v3 = FunctionFieldValuation(F, w3)
            v3 = FunctionFieldValuation(F, (v3, F.hom([1/x]), F.hom([1/x])))
            assert v3.is_discrete_valuation()
            return TypeIIPointOnBerkovichLine(self._X, v3)

        return self._X.gauss_point()


#----------------------------------------------------------------------------

#                  points of type II
#                  =================

class TypeIIPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    A point of type II on a Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line over a valued field K
    - ``v`` -- a discrete valuation on the function field of X extending the base valuation

    """
    def __init__(self, X, v):
        self._X = X
        F = X._F
        K = X._K
        vK = X._vK

        # to do: test v
        assert v.domain() is F
        assert v.is_discrete_valuation()

        self._v = v
        x = F.gen()
        if v(x) >= 0:
            self._is_in_unit_disk = True
            self._v1 = v._base_valuation
        else:
            self._is_in_unit_disk = False
            self._v1 = v._base_valuation._base_valuation


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

    def is_in_unit_disk(self):
        r"""
        True is self is contained in the unit disk.
        """
        return self.v(self._X._F.gen()) >= 0

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
        function field of `X`, or a polynomial in `1/x`, and where `s` is a
        nonnegative rational number. This data represents a discoid `D` via
        the condition `v_\xi(f)\geq s`.

        Then ``self`` is the unique boundary
        point of `D`, and if, moreover, ``self`` is not the Gauss point then
        `D` contains precisely the points `\xi` which are greater or equal to
        ``self``. If ``self`` is the Gauss point then `D` is the standard
        closed unit disk, `f=x` and `s=0`.
        """
        xi = self
        if xi.is_gauss_point():
            return xi._X._F.gen(), 0
        v = xi.pseudovaluation_on_polynomial_ring()
        phi = v.phi()
        if self.is_in_unit_disk():
            f = phi(self._X._F.gen())
            s = xi.v(f)
            return f, s
        else:
            x = self._X._F.gen()
            if phi[0] == 0:
                f = 1/x
            else:
                f = phi(1/x)
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

        OUTPUT:

        True if self is less or equal to ``xi`` (w.r.t. the natural
        partial order on `X`)
        """
        if self.is_gauss_point():
            return True      # the Gauss point is the least element of X
        if self.is_in_unit_disk() != xi.is_in_unit_disk():
            return False
        else:
            v1 = self.pseudovaluation_on_polynomial_ring()
            v2 = xi.pseudovaluation_on_polynomial_ring()
            return v1(v1.phi()) <= v2(v1.phi())


    def infimum(self, xi2):
        r"""
        Return the infimum of self and ``xi2``.

        INPUT:

        - ``xi2`` -- a point of type I or II on the Berkovich line

        OUTPUT:

        The infimum of self and `\xi_2` (w.r.t. to the natural partial ordering).
        Unless `\xi_2=\infty` or self is equal to `\xi_2`,
        the result is a point of type II.
        """
        if self.is_leq(xi2):
            return self
        if xi2.is_leq(self):
            return xi2
        # now the points are uncomparable, and the infinum is a point of type II

        if self.is_in_unit_disk() and xi2.is_in_unit_disk():
            v1 = self.pseudovaluation_on_polynomial_ring()
            v2 = xi2.pseudovaluation_on_polynomial_ring()
            v3 = mac_lane_infimum(v1, v2)
            v3 = FunctionFieldValuation(self._X._F, v3)
            return TypeIIPointOnBerkovichLine(self._X, v3)
        if (not self.is_in_unit_disk()) and (not xi2.is_in_unit_disk()):
            v1 = self.pseudovaluation_on_polynomial_ring()
            v2 = xi2.pseudovaluation_on_polynomial_ring()
            v3 = mac_lane_infimum(v1, v2)
            F = self._X._F
            x = F.gen()
            v3 = FunctionFieldValuation(F, v3)
            v3 = FunctionFieldValuation(F, (v3, F.hom([1/x]), F.hom([1/x])))
            return TypeIIPointOnBerkovichLine(self._X, v3)
        return self._X.gauss_point()


    def point_in_between(self, xi1):
        r"""
        Return a point in between ``self`` and ``xi1``.

        INPUT:

        - ``xi1`` -- a point which is strictly smaller than ``self``

        OUTPUT: a point which lies strictly between ``self`` and ``xi1``

        """
        xi0 = self
        assert xi0.is_leq(xi1) and not xi0.is_equal(xi1), "xi1 must be strictly smaller than self"
        in_unit_disk = xi1.is_in_unit_disk()
        v0 = self.pseudovaluation_on_polynomial_ring()
        v1 = xi1.pseudovaluation_on_polynomial_ring()
        if hasattr(v1, "_approximation"):
            v1 = v1._approximation
        phi = v1.phi()
        s0 = v0(phi)
        s1 = v1(phi)
        assert s0 < s1, "strange: s0>=s1, but xi0 < xi1"
        if s1 == Infinity:
            s2 = s0 + 1
        else:
            s2 = (s0+s1)/2
        xi2 = X.point_from_discoid(phi, s2, in_unit_disk)
        assert xi0.is_leq(xi2) and not xi0.is_equal(xi2), "xi0 is not less than xi2!"
        assert xi2.is_leq(xi1) and not xi2.is_equal(xi1), "xi2 is not less than xi1!"
        return xi2



#-------------------------------------------------------------------------

#               auxiliary functions



# is this still used?
def normalized_reduction(v, f):
    """ Return the normalized reduction of f with respect to v.

    INPUT:

    - v -- type II valuation on a rational function field F = K(x)
    - f -- a strongly irreducible polynom in K[x], or 1/x

    OUTPUT:

    a nonzero element fb in the residue field of v ???
    Precise definition needed!
    """

    F = v.domain()
    R = F._ring
    x = F.gen()
    r = v(f)
    m = abs(r.denominator())
    v1 = v._base_valuation
    if hasattr(v1, 'equivalence_unit'):
        fl = v.reduce(f^m*F(v1.equivalence_unit(-m*r))).factor()
        if len(fl)>0:
            return fl[0][0]^sign(fl[0][1])
        else:
            return 1/v.residue_field().gen()
    else:
        v1 = v1._base_valuation
        g = v1.equivalence_unit(-m*r)(1/x)
        fb = v.reduce(f^m*F(g)).factor()
        if len(fb) > 0:
            return fb[0][0]^sign(fb[0][1])
        else:
            return 1/v.residue_field().gen()

def mac_lane_infimum(v1, v2):
    r"""
    Return the infimum of `v_1` and `v_2`.

    INPUT:

    -``v1``, ``v2`` -- MacLane valuations on `K[x]``

    OUTPUT:

    on the set of all MacLane valuations on `K[x]`.
    """
    R = v1.domain()
    assert v2.domain() is R
    if v1.is_gauss_valuation():
        return v1
    V = v1.augmentation_chain()
    for i in range(1,len(V)):
        v0 = V[i]
        phi1 = V[i-1].phi()
        s = v2(phi1)
        assert v0.is_key(phi1)
        if v0(phi1) < s:
            return v0.augmentation(phi1,s)
        if v0(phi1) == s:
            return v0
    # now v0 should be the Gauss valuation
    assert v0.is_gauss_valuation()
    return v0

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
    assert s >= 0
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

def valuations_from_inequality(vK, f, s):
    r"""
    Return the list of inductive valuations corresponding to the given inequlities.

    INPUT:

    - ``vK`` -- a discrete valuation on a field `K`
    - ``f`` -- a nonconstant monic integral polynomial over `K`
    - ``s`` -- a nonnegative rational number, or `\infty`

    OUTPUT:

    a list of inductive valuations on the domain of ``f``, extending ``vK``,
    corresponding to the boundary points of the irreducible components of the
    affinoid defined by the condition `v(f)\geq s`. Note that these components
    are all discoids.

    """
    R = f.parent()
    K = R.base_ring()
    assert K is vK.domain()
    v0 = GaussValuation(R, vK)
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
                ret.append(v)
            else:
                # now v is an inductive valuation such that v(f) > s
                for v0 in v.augmentation_chain():
                    if v0(f) <= s:
                        break
                    else:
                        v = v0
                if v0(f) == s:
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
                ret.append(v)
        V = V_new
    return ret


def equality_of_pseudo_valuations(v1, v2):
    r""" Decide whether two pseudo-valuations are equal.

    INPUT:

    - ``v1``, ``v2`` -- two pseudo-valuations on the same rational
                        function field `F=K(x)`
    OUTPUT:

    True if ``v1`` is equal to ``v2``, False otherwise.

    We actually assume that the restriction of ``v1`` and ``v2`` to the
    constant base field are equal.

    """

    F = v1.domain()
    assert F is v2.domain()
    if v1(F.gen()) != v2(F.gen()):
        return False
    # now v1, v2 should both be inside or outside the unit disk
    w1 = v1._base_valuation
    w2 = v2._base_valuation
    # w1, w2 are valuations on K[x]
    # we check whether w1==w2
    if w1.is_discrete_valuation():
        if w2.is_discrete_valuation():
            return w1 <= w2 and w2 <= w1
        else:
           return False
    else:
        if w2.is_discrete_valuation():
            return False
    # now w1 and w2 are both infinite valuations
    if hasattr(w1, "_approximation"):
        if hasattr(w2, "_approximation"):
            # now w1 and w2 are both limit valuations
            if w1(w2._G) < Infinity or w2(w1._G) < Infinity:
                return False
            wa2 = w2._approximation
            wa1 = w1._approximation
            return w1(wa2.phi()) >= wa2(wa2.phi()) and w2(wa1.phi()) >= wa1(wa1.phi())
        else:
            return w2(w1._G) == Infinity
    else:
        if hasattr(w2, "_approximation"):
            return w1(w2._G) == Infinity
        else:
            return w1(w2.phi()) == Infinity
