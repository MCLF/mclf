r"""
The Berkovich projective line over a discretely valued field.

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `F=K(x)`
be a rational function field over `K`. We consider `F` as the function
field of the projective line `X` over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. Then a point `\xi` on `X^{an}`
may be identified with a (real valued) pseudo-valuation `v_\xi` on `F`
extending `v_K`.

Note that we do not assume `K` to be complete with respect to `v_K`. Hence we
can work with 'exact' fields, e.g. number fields.

There are three kind of 'points' which are relevant for us and can be handled
 using the mac_lane infrastructure:
    - Type I, algebraic: these are the points that come from a closed point
        on the (algebraic) projective line over the completed base field.
    - Type II: these are the points which correspond to discrete valuations
        on the function field whose residue field is a function field over the
        residue base field
    - Type V: these correspond to a pair `(v,\bar{v})`, where `v` corresponds
       to a type II point and `\bar{v}` is a discrete valuation on the residue
       field of `v`. Actually these are not points on `X^{an}`, properly
       speaking, but rather points on the associated adic space.

AUTHORS:

- Stefan Wewers (2017-02-10): initial version


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

    def constant_base_field(self):

        return self._F.constant_base_field()

    def base_valuation(self):

        return self._vK

    def function_field(self):

        return self._F

    def infty(self):
        r"""
        Return the point `\infty`.
        """

        R = self._F._ring
        v0 = GaussValuation(R, self._vK)
        v1 = v0.augmentation(R.gen(), Infinity)
        return TypeIPointOnBerkovichLine(self, v1, 1/self._F.gen())

    def gauss_point(self):
        r"""
        Return the Gauss point of self.

        The Gauss point is the type-II-point corresponding to the Gauss
        valuation on `K[x]`.
        """

        v0 = GaussValuation(self._F._ring, self._vK)
        v0 = FunctionFieldValuation(self._F, v0)
        return TypeIIPointOnBerkovichLine(self, v0)

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

         - ``f`` -- a squarefree polynomial in the generator of the function field of self
         - ``m`` -- an integer

        OUTPUT:

        The divisor of `f`, multiplied with `m`.
        """

        F = self._F
        x = F.gen()
        R = F._ring
        vK = self._vK
        v0 = GaussValuation(R, vK)
        f = R(f).monic()
        assert f.is_squarefree(), "f is not squarefree"

        # this is the part inside the unit disk
        if not v0.is_equivalence_unit(f):
            V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
            V = [LimitValuation(v, f) for v in V if not v.is_gauss_valuation()]
            D = [(TypeIPointOnBerkovichLine(self, v, x), m) for v in V]
        else:
            D = []

        # the part outside the unit disk
        f = f.reverse().monic()
        if not v0.is_equivalence_unit(f):
            V = vK.mac_lane_approximants(f, require_incomparability=True, required_precision=1)
            V = [LimitValuation(v, f) for v in V]
            V = [v for v in V if v(x) > 0]
            D = D + [(TypeIPointOnBerkovichLine(self, v, 1/x), m) for v in V]
        return D


class PointOnBerkovichLine(SageObject):
    r"""
    A point on a Berkovich projective line.

    We only allow three different types of points:

    - Type I, algebraic: these are the points that come from a closed point
        on the (algebraic) projective line over the completed base field.
    - Type II: these are the points which correspond to discrete valuations
        on the function field whose residue field is a function field over the
        residue base field
    - Type V: these correspond to a pair `(v,\bar{v})`, where `v` corresponds
       to a type II point and `\bar{v}` is a discrete valuation on the residue
       field of `v`. Actually these are not points on `X^{an}` properly
       speaking, but rather points on the associated adic space.

    In particular, the Gauss valuation on `F=K(x)` with respect to the parameter
    `x` corresponds t a point `\xi^g` of type II on `X^{an}` which we call
    the *Gauss point*.

    The set `X^{an}` has a canonical partial ordering in which the Gauss point
    is the smallest elements. All point of type I are maximal elements.

    """
    def __init__(self):
        pass

    def median(xi1, xi2, xi3):
        """ Find the median of self=xi1, xi2, v3.

        INPUT:

        - xi2, xi3 -- points of type I or II. It is assumed that xi1, xi2
          and xi3 are pairwise distinct.

        OUTPUT:

        The median xi of xi1, xi2, xi3.
        This means that xi lies on the interval between any two of
        the three points xi1, xi2, xi3. In particular, if one
        of the three points lies between the other two, then it is
        equal to xi.
        """

        if xi1.is_leq(xi2):
            if xi3.is_leq(xi1):
                return xi1   # xi1 lies between xi2 and xi3
            elif xi1.is_leq(xi3) and xi3.is_leq(xi2):
                return xi3   # xi3 lies between xi1 and xi2
            elif xi2.is_leq(xi3):
                return xi2   # xi2 lies between xi1 and xi3
            else:
                xi4 = xi2.infimum(xi3)
                if xi4.is_leq(xi1):
                    return xi1
                else:
                    return xi4
        elif xi2.is_leq(xi1):
            if xi3.is_leq(xi2):
                return xi2   # xi2 lies between xi1 and xi3
            elif xi2.is_leq(xi3) and xi3.is_leq(xi1):
                return xi3   # xi3 lies between xi2 and xi1
            elif xi1.is_leq(xi3):
                return xi1   # xi1 lies between xi2 and xi3
            else:
                xi4 = xi1.infimum(xi3)
                if xi4.is_leq(xi2):
                    return xi2
                else:
                    return xi4
        else:
            if xi1.is_leq(xi3):
                return xi1
            elif xi2.is_leq(xi3):
                return xi2
            elif xi3.is_leq(xi1) and not xi3.is_leq(xi2):
                return xi3
            elif xi3.is_leq(xi2) and not xi3.is_leq(xi1):
                return xi3
            else:
                # return maclane_infimum(xi2, xi3) looks wrong!
                return xi1.infimum(xi2)



class TypeIPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    An algebraic point of type I.

    INPUT:

    - `X` -- a Berkovich projective line over a valued field `K`
    - `v_1` -- an infinite pseudo-valuation on `K[x]`
    - `x_1` -- a generator of the function field of `X`

    Let `F=K(x)` be the function field of `X`. We consider `v_1` as a pseudo-valuation
    on the subring `K[x_1]` of `F=K(x)`. The unique extension `v` of `v1` to `F`
    is then the pseudo-valuation corresponding to self. In other words,
    `v(f) = v_1(A(f))`, where `A:F\to F` is the automorphism such that
    `A(x_1)=x`.

    At the moment, to be consistent with the realization of points of type II,
    one must take `x_1=x` if the point lies in the closed unit disk,
    and `x_1=1/x` otherwise.

    """

    def __init__(self, X, v1, x1):

        self._X = X
        F = X._F
        K = F.constant_base_field()
        x = F.gen()
        assert x1 == x or x1 == 1/x, "x1 must be equal to x or 1/x."
        assert x1 == x or v1(v1.domain().gen()) > 0, "If the point lies in the closed unit disk then x1 must be equal to x."
        self._parameter = x1
        self._is_in_unit_disk = (x1 == x)

        # to do: test v1

        A = F.hom([x1])                # sends x to x1
        B = inverse_automorphism(x1)   # sends x1 to x
        # self._v = FunctionFieldPseudoValuation(F,(v1,B,A))
        # this is not yet possible
        self._A = A
        self._B = B
        self._v1 = v1

    def __repr__(self):

        return "Point of type I on Berkovich line corresponding to %s, w.r.t. to parameter %s"%(self._v1, self._parameter)


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
        Evaluate the pseudo-valuation corresponding to self on function field element.

        INPUT:

        - ``f`` -- an element of the function field of the underlying Berkovich line

        OUTPUT:

        the value `v(f)`, where v is the pseudo-valuation corresponding to self

        """

        f1 = self._B(f)
        return self._v1(f1.numerator())-self._v1(f1.denominator())

    def is_equal(self, xi):
        r"""
        Return True is self is equal to ``xi``.
        """

        if xi.type() != "I":
            return False
        if self.is_in_unit_disk() != xi.is_in_unit_disk():
            return False
        return self._v1 == xi._v1

    def is_leq(self, xi):
        r"""
        Return True is self is less or equal to xi.

        INPUT:

        - ``xi`` -- a point of type I or II

        OUTPUT:

        True if self is less or equal to ``xi`` (w.r.t. the natural
        partial order on `X` for which the Gauss pont is the smallest element).
        Since self is a point of type I and hence maximal, this is never true
        unless `xi` is equal to self.

        """

        return self.is_equal(xi)

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
            v1 = self._v1
            v2 = xi2._v1
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
            # print "w1 =", w1
            # print "w2 =", w2
            w3 = mac_lane_infimum(w1, w2)
            # print "w3 =", w3
            v3 = FunctionFieldValuation(self._X._F, w3)
            return TypeIIPointOnBerkovichLine(self._X, v3)
        if (not self.is_in_unit_disk()) and (not xi2.is_in_unit_disk()):
            v1 = self._v1
            v2 = xi2._v1
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
            return TypeIIPointOnBerkovichLine(self._X, v3)
        return self._X.gauss_point()


class TypeIIPointOnBerkovichLine(PointOnBerkovichLine):
    r""" A point of type II on a Berkovich line.
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

        self._v = v
        x = F.gen()
        if v(x) >= 0:
            self._v1 = v._base_valuation
        else:
            self._v1 = v._base_valuation._base_valuation

    def __repr__(self):

        return "Point of type II on Berkovich line, corresponding to %s"%self._v


    def type(self):
        """ Return the type of self.
        """
        return "II"

    def is_gauss_point(self):
        """ Return True is self is the Gauss point.
        """

        return self._v1.is_gauss_valuation()

    @cached_method
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

    @cached_method
    def discoid_representation(self):  # is not used anymore !
        r"""
        Return a discoid representation for the point self.

        Let `\xi` be a point of type II, and let `D` be the unique closed
        discoid with boundary point `\xi` which
        does not contain the point `\infty`. A *discoid representation*
        of `\xi` is a pair `(\phi,s)`, where `\phi` is a key polynomial for self
        and `s=v_\xi(\phi)`. Then

              ` D = \{ \eta | v_\eta(\phi) >= s \}`.

        A *key polynomial* for the point `\xi` of type II is a polynomial
        `\phi\in K[x]` with the property that

              `D = \{ \eta | v_\eta(\phi) >= v_\xi(\phi) \}`.

        """

        v = self._v
        x = self._X._F.gen()
        if v(x) >= 0:
            phi = v.domain()(v._base_valuation.phi())
            return phi, v(phi)
        else:
            phi = v._base_valuation._base_valuation.phi()
            if phi[0].is_zero():
                return x, v(x)
            else:
                phi = x^phi.degree()*phi(1/x)
                return phi, v(phi)

    def is_equal(self, xi):
        r"""
        Return True if self is equal to ``xi``.
        """

        if xi.type() != "II":
            return False
        return self.is_leq(xi) and xi.is_leq(self)


    def is_leq(self, xi):
        r"""
        Return True if self is less or equal to xi.

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
            v1 = self._v1
            v2 = xi._v1
            return v1(v1.phi()) <= v2(v1.phi())

    def infimum(self, xi2):
        r"""
        Return the infimum of self and xi2.

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
            v1 = self._v1
            # print "v1 = ", v1
            v2 = xi2._v1
            # print "v2 = ", v2
            v3 = mac_lane_infimum(v1, v2)
            # print "v3 = ", v3
            v3 = FunctionFieldValuation(self._X._F, v3)
            return TypeIIPointOnBerkovichLine(self._X, v3)
        if (not self.is_in_unit_disk()) and (not xi2.is_in_unit_disk()):
            v1 = self._v1
            v2 = xi2._v1
            v3 = mac_lane_infimum(v1, v2)
            F = self._X._F
            x = F.gen()
            v3 = FunctionFieldValuation(F, v3)
            v3 = FunctionFieldValuation(F, (v3, F.hom([1/x]), F.hom([1/x])))
            return TypeIIPointOnBerkovichLine(self._X, v3)
        return self._X.gauss_point()

class TypeVPointOnBerkovichLine(PointOnBerkovichLine):
    r"""
    A point of type V on the Berkovich line.

    A 'point' `\eta` of type V on the Berkovich line `X^{an}` corresponds to a pair
    `(v,\bar{v})`, where `v` is a type-II-valuation and `\bar{v}` is a function
    field valuation on the residue field of `v`.  We call `v` the *major
    valuation* and `\bar{v}` the *minor valuation* associated to `\eta`.

    Note that `\eta` is not, properly speaking, a point on the analytic space
    `X^{an}`, but rather a point on the adic space `X^{ad}`.

    Equivalent ways to describe `\eta` are:
    - the rank-2-valuation given as the composition of `v` and `\bar{v}`
    - a *residue class* on `X^{an}`; more precisely, `\eta` corresponds to
      a connected component of `X^{an}-\{\xi\}`, where `\xi` is the TypeIIPointOnBerkovichLine
      corresponding to `v`.

    Let `\xi_1` be a point of type II, and `\xi_2` a point of type I or II.
    Then we can define the point of type V `\eta:=d(\xi_1,\xi_2)` as the unique
    residue class with boundary point `\xi_1` containing `\xi_2`.

    INPUT:

    - X -- a Berkovich line with function field `F=K(x)`
    - xi1 -- a point of type II on X
    - xi2 -- a point of type I or II on X

    OUTPUT:

    the point of type V denoted `d(\xi1,xi2)` and defined above

    """

    def __init__(self, X, xi1, xi2):

        self._X = X               # the underlying Berkovich line
        assert xi1._X is X
        assert xi1.type() == "II"
        assert xi2.type() == "I" or xi2.type() == "II"
        assert xi2._X is X
        self._v = xi1._v          # the major valuation of eta
        # to do: define minor valuation vb
        k1 = xi1._v.residue_field()
        if xi1.is_leq(xi2):
            assert not xi2.is_leq(xi1), "xi1 and xi2 are equal"
            phi2 = xi2.key_polynomial()
            psi = normalized_reduction(xi1_v, phi2)
            self._vb = FunctionFieldValuation(k1, psi)
        else:
            self._vb =  FunctionFieldValuation(k1, 1/k1.gen())

#-------------------------------------------------------------------------

#               auxiliary functions


def inverse_automorphism(x1):
    r"""
    Return automorphism of function field sending `x_1` to standard generator.

    INPUT:

    - ``x1`` -- a generator of a rational function field `F=K(x)`

    OUTPUT:

    a field automorphism `A:F\to F` such that `A(x1)=x`
    """

    F = x1.parent()
    K = F.constant_base_field()
    x = F.gen()
    num = x1.numerator()
    denom = x1.denominator()
    assert num.degree() <= 1 and denom.degree() <= 1
    a = num[1]
    b = num[0]
    c = denom[1]
    d = denom[0]
    assert not (a*d-b*c).is_zero()
    A = (d*x-b)/(-c*x+a)
    return F.hom([A])


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

    # print "call mac_lane_infimum with %s and %s"%(v1, v2)
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
