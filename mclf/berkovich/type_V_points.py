# -*- coding: utf-8 -*-
r"""
Points of type V on the Berkovich line
======================================

Let `X^{an}` be a Berkovich line over a discretely valued field `K`.
A "point" `\eta` of type V on `X^{an}` corresponds to a
pair `(v,\bar{v})`, where `v` is a type-II-valuation and `\bar{v}` is a
function field valuation on the residue field of `v`.  We call `v` the
"major valuation" and `\bar{v}` the "minor valuation" associated to `\eta`.

Note that `\eta` is not, properly speaking, a point on the analytic space
`X^{an}`, but rather a point on the adic space `X^{ad}`.

Equivalent ways to describe `\eta` are:

- the rank-2-valuation given as the composition of `v` and `\bar{v}`
- a "residue class" on `X^{an}`; more precisely, `\eta` corresponds to
  a connected component of `X^{an}-\{\xi\}`, where `\xi` is the
  type-II-point corresponding to `v` (and then `\xi` is the unique boundary
  point of the residue class)
- an "open discoid": more precise, a pair `(\phi,s)`, where `\phi` is
  a rational function such that the open discoid

  .. MATH::

         D = \{ v \mid v(\phi) > s \}

  is the residue class corresponding to `\eta`. Moreover, either `\phi`
  of `1/\phi` is a monic, integral and irreducible polynomial in `x`
  or in `1/x`.
- a "tangent vector" on `X^{an}`; more precisely a group homomorphism

  .. MATH::

      \partial: K(x)^* \to \mathbb{Z}

with the following properties: let `(\phi,s)` be the discoid representation
of `\eta`. We define, for `t\geq s`, the valuation `v_t` as the valuation
corresponding to the boundary point of the open discoid `v(\phi)>t`. Then
`\partial(f)` is the right derivative at `t=s` of the function

.. MATH::

    t \mapsto v_t(f).


The most convenient way to determine a point of type V is as follows. Let
`\xi_1` be a point of type II and `\xi_2` be of type I or II, distinct from
`\xi_1`. Then

.. MATH::

        \eta = \eta(\xi_1,\xi_2)

is the point of type V corresponding to the connected component of
`X-\{\xi_1\}` containing `\xi_2`. We call `\eta` the *direction*
from `\xi_1` towards `\xi_2`.


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


class TypeVPointOnBerkovichLine(SageObject):
    r"""
    A point of type V on the Berkovich line.


    Let `\xi_1` be a point of type II, and `\xi_2` a point of type I or II.
    Then we can define the point of type V `\eta:=\eta(\xi_1,\xi_2)` as the unique
    residue class with boundary point `\xi_1` containing `\xi_2`.

    INPUT:

    - ``xi0`` -- point of type II
    - ``xi1`` -- arbitrary point of X, distinct from xi0

    OUTPUT:

    The type-V-point corresponding to the connected component
    of `X^{an}-{\xi0}`` which contains `\xi1`.


    EXAMPLES:

    ::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: xi1 = X.point_from_discoid(x,1)
        sage: xi2 = X.point_from_discoid(x^2+4,3)
        sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)

    We see that ``eta`` represents an open disk inside the closed unit disk.
    ::

        sage: eta
        Point of type V given by residue class v(x + 2) > 1

    Here is an example of a type-V-point representing an open disk in the
    complement of the closed unit disk:
    ::

        sage: xi0 = X.gauss_point()
        sage: xi3 = X.point_from_discoid(2*x+1, 2)
        sage: eta = TypeVPointOnBerkovichLine(xi0, xi3)
        sage: eta
        Point of type V given by residue class v(1/x) > 0

    We check that ``xi0`` lies outside the open disk and ``xi3`` inside:
    ::

        sage: eta.is_in_residue_class(xi0)
        False
        sage: eta.is_in_residue_class(xi3)
        True

        sage: xi4 = X.point_from_discoid(2*x+1, 4)
        sage: TypeVPointOnBerkovichLine(xi3, xi4)
        Point of type V given by residue class v((2*x + 1)/x) > 3
        sage: TypeVPointOnBerkovichLine(xi4, xi3)
        Point of type V given by residue class v(1/2*x/(x + 1/2)) > -5

    The following example shows that the minor valuation is computed correctly ::

        sage: xi5 = X.point_from_discoid(1/x,1)
        sage: eta = TypeVPointOnBerkovichLine(xi0,xi5)
        sage: eta
        Point of type V given by residue class v(1/x) > 0
        sage: eta.minor_valuation()
        Valuation at the infinite place

    """

    def __init__(self, xi0, xi1):

        # the internal representation of self is via these attributes:
        #
        # self._xi0 = the boundary point
        # self._v : the major valuation
        # self._kv : the residue field of the major valuation
        # self._vb : the minor valuation
        # self._phi, self._s : a discoid representation of self
        # self._phi_pol: the last key polynomial of the inductive valuation
        #                from which self._v is induced
        # it is crucial that self._v is induced from an inductive valuation
        # on the polynomial subring K[x] (if xi0 lies inside the unit disk)
        # or K[1/x] (if xi0 lies outside the unit disk)

        X = xi0.berkovich_line()
        x = X.function_field().gen()
        self._X = X
        assert xi0.type() == "II", "xi0 must be a point of type II"
        assert not xi0.is_equal(xi1), "xi0 and xi1 must be distinct"
        # the boundary point:
        self._xi0 = xi0
        # the major valuation
        self._v = xi0.valuation()
        v0 = xi0.pseudovaluation_on_polynomial_ring()
        # the residue field of the major valuation
        # we can't take self._v.residue_field because this does
        # not give a true function field
        k_v = v0.residue_field()
        self._k_v = k_v
        if not xi1.is_inductive():
            xi1 = xi1.approximation(xi0)
        # now we compute a discoid representation of self
        # i.e. we set the attributes self._phi, self._s, self._type
        v1 = xi1.pseudovaluation_on_polynomial_ring()
        if xi0.is_leq(xi1):
            # the Gauss point is not contained in the residue class
            # corresponding to eta
            if xi1.is_in_unit_disk():
                # now self represents an open discoid strictly contained in
                # the standard closed unit disk
                phi_pol = v0.equivalence_decomposition(v1.phi())[0][0]
                # phi_pol is a key polynomial for v_0
                self._phi_pol = phi_pol
                phi = phi_pol(x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "contained_in_unit_disk"
            else:
                # now self represents an open discoid in the complement
                # of the closed unit disk
                phi_pol = v0.equivalence_decomposition(v1.phi())[0][0]
                self._phi_pol = phi_pol
                phi = phi_pol(1/x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "disjoint_from_unit_disk"
        else:
            if xi0.is_in_unit_disk():
                # now self represents the complement of a closed discoid
                # properly contained in the standard closed unit disk.
                # In particular, the residue class contains Infinity,
                # and 0 lies in its complement.
                phi_pol = v0.phi()
                self._phi_pol = phi_pol
                phi = 1/phi_pol(x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "overlaps_with_unit_disk"
            else:
                # now self represents an open discoid which properly contains
                # the standard closed unit disk
                phi_pol = v0.phi()
                self._phi_pol = phi_pol
                phi = 1/phi_pol(1/x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "contains_unit_disk"
        # we test that the discoid representation is correct.
        assert self._v(self._phi) == self._s, "xi1 must not lie in the residue class!"
        assert self.is_in_residue_class(xi1), "xi2 must lie in the residue class!"

    def __repr__(self):
        return "Point of type V given by residue class v({}) > {}".format(self._phi, self._s)

    def _cache_key(self):
        r""" Return a cache key for this point.

        Note: this is very experimental.
        """
        if not hasattr(self, "_cache_key_value"):
            self._cache_key_value = hash(str(self))
        return self._cache_key_value

    def berkovich_line(self):
        """
        Return the Berkovich line underlying the point.
        """
        return self._X

    def type(self):
        return "V"

    def boundary_point(self):
        """ Return the boundary point of the type-V-point. """
        return self._xi0

    @cached_method
    def point_inside_residue_class(self):
        """
        Return some point inside the residue class corresponding to the point.

        """
        from mclf.berkovich.berkovich_line import valuation_from_discoid
        X = self.berkovich_line()
        F = X.function_field()
        x = F.gen()
        vK = X.base_valuation()

        phi, s = self.open_discoid()
        if self._type == "contained_in_unit_disk":
            v0 = valuation_from_discoid(vK, self._phi_pol, Infinity)
            xi = self.berkovich_line().point_from_pseudovaluation(F.valuation(v0))
        elif self._type == "disjoint_from_unit_disk":
            v0 = valuation_from_discoid(vK, self._phi_pol, Infinity)
            v = F.valuation(v0)
            v = F.valuation((v, F.hom(1/x), F.hom(1/x)))
            xi = self.berkovich_line().point_from_pseudovaluation(v)
        elif self._type == "overlaps_with_unit_disk":
            xi = self.berkovich_line().infty()
        else:
            xi = self.berkovich_line().gauss_point()
        assert self.is_in_residue_class(xi), "xi does not lie in the residue class"
        return xi

    def major_valuation(self):
        return self._v

    def minor_valuation(self):
        r""" Return the minor valuation of this type V point.

        """
        if hasattr(self, "_vb"):
            return self._vb
        f, s = self.open_discoid()
        v = self.major_valuation()
        Fb = self._k_v
        # a function field into which the residue field of v coerces
        pi = self.berkovich_line().base_valuation().uniformizer()
        v = v.scale(1/v(pi))
        assert v(pi) == 1
        s = v(f)
        fb = Fb(v.reduce(f**s.denominator()/pi**s.numerator()))
        if fb.numerator().degree() > 0:
            vb = Fb.valuation(fb.numerator().factor()[0][0])
        else:
            vb = Fb.valuation(1/Fb.gen())
        return vb

    @cached_method
    def is_in_residue_class(self, xi):
        r""" Test whether ``xi`` lies in the residue class of ``self``.

        INPUT:

        - ``xi`` -- a point on the Berkovich line underlying the type-V-point

        OUTPUT:

        ``True`` if ``xi`` lies in the residue class corresponding to ``self``

        EXAMPLES:

::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi1 = X.point_from_discoid(x,1)
            sage: xi2 = X.point_from_discoid(x^2+4,3)
            sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)
            sage: eta.is_in_residue_class(xi2)
            True
            sage: eta.is_in_residue_class(xi1)
            False


        """
        phi, s = self.open_discoid()
        if xi.type() == "V":
            return self.boundary_point().v(phi) >= s and self.derivative(phi) > 0
        else:
            return xi.v(phi) > s

    @cached_method
    def is_leq(self, xi):
        r""" Return whether this point is less or equal another point.

        INPUT:

        - ``xi`` -- a point of type I, II or V

        OUTPUT: ``True`` is this point `\eta` is less than or equal to `\xi`.

        This is equivalent to `\xi` lying inside the residue class defined by
        `\eta`.

        """
        return self.is_in_residue_class(xi)

    @cached_method
    def is_equal(self, xi):
        r"""
        Return ``True`` is self is equal to ``xi``.

        """
        if not xi.type() == "V":
            return False
        return self.is_leq(xi) and xi.is_leq(self)

    @cached_method
    def is_strictly_less(self, xi1):
        """ Check whether ``self`` is strictly smaller than ``xi1``.
        """
        return self.is_leq(xi1) and not self.is_equal(xi1)

    def open_discoid(self):
        r""" Return the representation of self as an open discoid.

        INPUT:

        - self: a point of type V on a Berkovich line

        OUTPUT:

        a pair `(\phi, s)`, where `\phi` is a rational function and `s` a
        rational number is such that

        .. MATH::

               D = \{ v\in X \mid v(\phi) > s \}

        is the open discoid representing the type-V-point ``self``.

        Either `\phi` of `1/\phi` is a monic, integral and strongly irreducible
        polynomial in `x` or in `1/x`.

        """
        return self._phi, self._s

    # this function is maybe not so useful..
    def point_inside_discoid(self, t):
        r"""
        Return the point inside the residue class at the value `t`.

        The type-V-point corresponds to an open discoid defined by

        .. MATH::

                  v(\phi) > s.

        For for a rational number `t>s` we can define the type-II-point
        `\xi_t` corresponding to the closed discoid defined by

        .. MATH::

                 v(\phi) >= t.

        If `t=\infty` we obtain the type-I-point corresponding to `\phi=0`.

        INPUT:

        - ``t`` -- a rational number or Infinity

        OUTPUT:

        The point `\xi_t` inside the residue class corresponding to the closed
        discoid defined by `v(\phi) >= t`.

        If `t <= s` then an error is raised.

        """

        eta = self
        X = eta.berkovich_line()
        phi, s = eta.open_discoid()
        assert t > s, "t must be > s"

        if eta._type == "contained_in_unit_disk":
            return X.point_from_discoid(eta._phi_pol, t)
        elif eta._type == "disjoint_from_unit_disk":
            return X.point_from_discoid(eta._phi_pol, t, in_unit_disk=False)
        else:
            raise NotImplementedError

    @cached_method
    def derivative(self, f):
        r"""
        Return the "derivative" of ``f`` with respect to ``self``.

        Here we interpret the type-V-point as a 'tangent vector', more precisely
        as a homomorphism

        .. MATH::

                    \partial: K(x)^* \to \mathbb{Z}

        with the following property. Assume that `\eta=` ``self`` is represented
        by the open discoid `D_\eta = \{ v \mid v(\phi)> s \}`. Set

        .. MATH::

               v_t = [v, v_t(\phi) = t],

        for `t\geq s`.  Then `\partial(f)` is the right derivative
        at `t=s` of the function

        .. MATH::

            t \mapsto v_t(f),

        for all `f \in K(x)`.

        Alternative, we have that

        .. MATH::

            \partial(f) = \deg_\eta(f)/\deg_\eta(\phi),

        where `\deg_\eta(f)` denotes the degree of the divisor of `f`
        restricted to the open discoid `D_\eta`.

        WARNING: the following is not quite true; the formula has to be
        corrected by some ramification index:

        We remark that for rational functions `f` such that `v(f)=0` we have

        .. MATH::

             \partial(f) = \bar{v}(\bar{f}).

        Here `(v,\bar{v})` is the pair of valuations corresponding to `\eta`.


        INPUT:

        - ``f`` -- a nonzero element of the function field `K(x)`

        OUTPUT:

        The "right derivative" of the valuative function `v\mapsto v(f)`
        at ``self``.

        EXAMPLES:

        ::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi1 = X.point_from_discoid(x^2+2, 1)
            sage: xi2 = X.point_from_discoid(x^2+2, 2)
            sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)
            sage: eta
            Point of type V given by residue class v(x^2 + 2) > 1
            sage: eta.derivative(x^2+2)
            1
            sage: eta.derivative(x^4+4)
            2

        """

        eta = self
        X = eta._X
        F = X.function_field()
        x = F.gen()
        xi_g = X.gauss_point()
        assert f.parent() is F, "f must lie in the function field of X"
        assert not f.is_zero(), "f must not be zero"

        phi, s = eta.open_discoid()
        if not eta.is_in_residue_class(xi_g):
            # now phi should be a monic polynomial in x or in 1/x
            if phi.denominator().is_one():
                # now eta corresponds to an open discoid properly contained
                # in the closed unit disk
                return self.derivative_of_polynomial(f.numerator())-self.derivative_of_polynomial(f.denominator())
            else:
                # now eta corresponds to an open discoid inside the complement
                # of the closed unit disk
                f = F.hom([1/x])(f)
                return self.derivative_of_polynomial(f.numerator())-self.derivative_of_polynomial(f.denominator())
        else:
            # now D_eta contains the Gauss point
            if eta.major_valuation()(x) >= 0:
                # now D_eta is the complement of a closed disk properly
                # contained in the unit disk
                v0 = eta._xi0.pseudovaluation_on_polynomial_ring()
                return -v0.effective_degree(f.numerator()) + v0.effective_degree(f.denominator())
            else:
                # now D_eta is the complement of a closed disk disjoint from
                # the unit disk
                f = F.hom([1/x])(f)
                v0 = eta._xi0.pseudovaluation_on_polynomial_ring()
                return - v0.effective_degree(f.numerator()) + v0.effective_degree(f.denominator())

    def derivative_of_polynomial(self, f):

        v = self._xi0.pseudovaluation_on_polynomial_ring()
        w = v.augmentation(self._phi_pol, v(self._phi_pol), check=False)
        v_list = w.valuations(f)
        val, pos = min((val, pos) for (pos, val) in enumerate(v_list))
        # now pos is the index of the first item in v_list where the minimum is attained
        return pos

    @cached_method
    def left_derivative(self, f):
        r"""
        Return the left derivative of ``f`` with respect to ``self``.

        INPUT:

        - ``f`` -- an element of the polynomial ring `K[x]` or of
                the function field `K(x)`

        OUTPUT:

        The left derivative of the valuative function

        .. MATH::

                H_f: v \mapsto v(f)

        at `\eta=` ``self``. If \eta` lies in the closed unit disk and `f`
        is a polynomial in `x` then this left derivative is equal to the
        'effective degree' of `f` with respect to the major valuation of `\eta`,
        as defined by MacLane.

        """
        if hasattr(f, "numerator"):
            return self.left_derivative_of_polynomial(f.numerator()) - self.left_derivative_of_polynomial(f.denominator())
        else:
            return self.left_derivative_of_polynomial(f)

    def left_derivative_of_polynomial(self, f):

        v = self._xi0.pseudovaluation_on_polynomial_ring()
        return v.effective_degree(f)

# --------------------------------------------------------------------------
