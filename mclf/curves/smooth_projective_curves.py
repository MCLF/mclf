# -*- coding: utf-8 -*-
r"""
Smooth projective curves over a field
=====================================

Let `k` be a field and `F/k` a finitely generated field extension of transcendence
degree one (i.e. a 'function field over `k`'). Then there exists a smooth projective
curve `X` over `Spec(k)` with function field `F`, unique up to unique isomorphism.
The set of closed points on `X` are in natural bijection with the set of discrete
valuations on `F` which are trivial on `k`. See

- R. Hartshorne, *Algebraic Geometry*, Theorem I.6.9.

The classes in this module provide the definition and some basic functionality for
such curves.

A curve `X` is defined via its function field `F_X`. Points are represented by
the corresponding valuations on `F_X`, and no smooth projective model of `X` is
actually computed. However, we do compute a list of 'coordinate functions'
`x_1,..,x_n` which separate all points, meaning that the closure of the rational
map from `X` to projective space of dimension `n` is injective. Then a (closed)
point `x` on `X` can also be represented by the tupel `(f_1(x),..,f_n(x))`. This
is useful to test for equality of points.

A function field in Sage is always realized as a simple separable extension of a
rational function field. Geometrically, this means that the curve `X` is implicitly
equipped with a finite separable morphism `\phi:X\to\mathbb{P}^1_k`
to the projective line over the base field `k`. We call `\phi` the
*structure morphism* of the curve.

The base field `k` is called the *constant base field* of the curve, and it is
part of the data. We do not assume that the extension `F_X/k` is regular (i.e.
that `k` is algebraically closed in `F_X`). Geometrically this means that the
curve `X` may not be absolutely irreducibel as a `k`-scheme. The *field of
constants* of `X` is defined as the algebraic closure of `k` inside `F_X`.
It is a finite extension `k_c/k`. If we regard `X` as a curve over its fields of
constants then it becomes absolute irreducible.

It would be interesting to have an efficient algorithm for computing the field
of constants, but it seems that this has not been implemented in Sage yet.
To compute the genus of `X` it is necessary to know at least the degree `[k_c:k]`.
If `k` is a finite field, it is actually easy to compute `k_c`. If `k` is a
number field we use a probabilistic algorithm for computing the degree `[k_c:k]`,
by reducing the curve modulo several small primes.

Currently, the function field `F` defining a smooth projective curve must be a
simple finite extension of a rational function field, i.e. of the form

.. MATH::

    F = k(x)[y]/(G)

where `G` is an irreducible polynomial over `k(x)`. If not explicitly stated
otherwise, it is assumed that `k` is the constant base field of the curve `X`.
If `k` is a finite field, then one may also declare any subfield `k_0` of `k`
to be the constant base field. Geometrically, this means that we consider `X`
as a curve over `{\rm Spec}(k_0)`. In any case, the field of constants of `X`
is a finite extension of `k`.


AUTHORS:

- Stefan Wewers (2016 - 2021)


EXAMPLES::

    sage: from mclf import *
    sage: K = GF(2)
    sage: FX.<x> = FunctionField(K)
    sage: R.<T> = FX[]
    sage: FY.<y> = FX.extension(T^2+x^2*T+x^5+x^3)
    sage: Y = SmoothProjectiveCurve(FY)
    sage: Y
    the smooth projective curve with Function field in y defined by y^2 + x^2*y + x^5 + x^3
    sage: Y.genus()
    1
    sage: Y.zeta_function()
    (2*T^2 + T + 1)/(2*T^2 - 3*T + 1)

Over finite fields, we are allowed to specify the constant base field: ::

    sage: K = GF(4)
    sage: F.<x> = FunctionField(K)
    sage: X = SmoothProjectiveCurve(F, k=GF(2))
    sage: X
    the smooth projective curve with Rational function field in x over Finite Field in z2 of size 2^2 and constant base field Finite Field of size 2
    sage: X.field_of_constants()
    Finite Field in z2 of size 2^2

A curve may also be defined by an irreducible bivariate polynomial: ::

    sage: A.<x,y> = QQ[]
    sage: X = SmoothProjectiveCurve(y^2 - x^3 - 1)
    sage: X
    the smooth projective curve with Function field in y defined by y^2 - x^3 - 1

If the curve is defined over a number field, we can find a prime of good
reduction, and compute the reduction: ::

    sage: v_p = X.prime_of_good_reduction()
    sage: v_p
    5-adic valuation

The result is a discrete (p-adic) valuation on the constant base field. The
reduction is a smooth projective curve of the same genus: ::

    sage: Xb = X.good_reduction(v_p)
    sage: Xb
    the smooth projective curve with Function field in y defined by y^2 + 4*x^3 + 4
    sage: Xb.genus()
    1

.. TODO::

    - allow to specify the constant base field in a more flexible way
    - write more doctests !!
    - implement a general and deterministic algorithm for computing the field of
      constants (and not just the degree)
    - the residue field of a point should be explicitly an extension of
      the constant base field.
    - treat the base curve `X` as a *curve*, not just as a function field
    - realize morphisms between curves, in particular the canonical map to `X`

"""

# *****************************************************************************
#       Copyright (C) 2016-2021 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************

from sage.all import lcm, SageObject, Infinity, ZZ, PolynomialRing, randint, PowerSeriesRing


class SmoothProjectiveCurve(SageObject):
    r"""
    Return the smooth projective curve with function field `F`.

    INPUT:

    - ``F`` -- a function field, or an irreducible  bivariate polynomial over a field
    - ``k`` -- a field which has a natural embedding into the constant
      base field of `F`, such that the constant base field is a finite
      extension of k (or ``None``).
    - ``assume_regular`` -- a boolean (default: ``False``)

    OUTPUT:

    the smooth projective curve `X` with function field `F`. If `F` is an
    irreducible bivariate polynomial, we use the function field with two
    generators and relation `F`.

    If `k` is given, then `X` is considered as a `k`-scheme. If `k` is not given
    then we use the field of constants of `F` instead.

    NOTE:

    At the moment, `k` should only be different from the constant base field of
    `F` if `k` is finite (because it is then easy to compute the degree of the
    degree of the constant base field of `F` over `k`).
    """

    def __init__(self, F, constant_base_field=None, assume_regular=False):

        from sage.rings.ring import Field
        from sage.rings.function_field.constructor import FunctionField
        from mclf.field_extensions.standard_field_extensions import standard_field_extension

        if not isinstance(F, Field):
            # F should be a bivariate polynomial; we turn it into a function field
            A = F.parent()
            k = A.base_ring()
            F0 = FunctionField(k, A.variable_names()[0])
            R = PolynomialRing(F0, A.variable_names()[1])
            G = R(F(F0.gen(), R.gen()))
            assert G.degree() > 0, "the polynomial F must have positive degree in y"
            assert G.is_irreducible(), "the polynomial F must be irreducible"
            F = F0.extension(G.monic(), A.variable_names()[1])

        if k is not None:
            k1 = F.constant_base_field()
            assert k.is_subring(k1), "k must be a subfield of the field of constants of F"
        else:
            k = F.constant_base_field()
        self._function_field = standard_field_extension(k.hom(F))

        # self._coordinate_functions = self.coordinate_functions()
        if assume_regular:
            self._field_of_constants_degree = ZZ(1)
        else:
            self._field_of_constants_degree = self.field_of_constants_degree()
        self.compute_separable_model()

    def __repr__(self):
        if self._extra_extension_degree == 1:
            return "the smooth projective curve with {}".format(self.function_field())
        else:
            return "the smooth projective curve with {} and constant base field {}".format(
                self.function_field(), self.constant_base_field())

    def constant_base_field(self):
        r"""
        Return the constant base field.
        """
        return self._function_field.constant_base_field()

    def point(self, v):
        r""" Returns the point on the curve corresponding to ``v``.

        INPUT:

        - ``v`` -- a discrete valuation on the function field of the curve

        OUTPUT:

        The point on the curve corresponding to ``v``. The valuation `v` must be
        trivial on the constant base field.

        """
        assert v.restriction(self.constant_base_field()).is_trivial(), \
            "the restriction of v to the constant base field must be trivial"
        return PointOnSmoothProjectiveCurve(self, v)

    def singular_locus(self):
        r""" Return the singular locus of the affine model of the curve.

        OUTPUT:

        a list of discrete valuations on the base field `k(x)` which represent
        the `x`-coordinates of the points where the affine model of the curve
        given by the defining equation of the function field *may* be singular.

        """
        F = self.function_field()
        F0 = F.base_field()
        if F is F0:
            # the curve is the projective line
            return []
        f = F.polynomial()
        # this is the defining equation, as a polynomial over F0 = k(x)
        # the coefficients may not be integral; we have to multiply f by
        # the lcm of the denominators of the coefficients
        c = lcm([f[i].denominator() for i in range(f.degree()+1)])
        f = c*f
        f = f.map_coefficients(lambda c: c.numerator(), F0._ring)
        y = f.parent().gen()
        x = f.base_ring().gen()
        # now f is a polynomial in y over the polynomial ring in x
        if f.derivative(y) == 0:
            # F/F0 is inseparable
            g = f.derivative(x)
            D = f.resultant(g)
        else:
            Dy = f.discriminant().numerator()
            fx = f.derivative(x)
            if not fx.is_zero():
                Dx = f.resultant(fx)
                D = Dx.gcd(Dy)
            else:
                D = Dy
        return [F0.valuation(h.monic()) for h, m in D.factor()]

    def field_of_constants(self):
        r""" Return the field of constants of this curve.

        If `F` is the function field of the curve and `k` the constant base field,
        then the *field of constants* is the algebraic closure of `k` in `F`.

        For the moment, this is implemented only if the constant base field
        is a finite field.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(GF(2))
            sage: R.<y> = F[]
            sage: G = (y+x)^4 + (y + x) + 1
            sage: F1.<y> = F.extension(G)
            sage: Y1 = SmoothProjectiveCurve(F1)
            sage: Y1.field_of_constants()
            Finite Field in z4 of size 2^4

        """
        if hasattr(self, "_field_of_constants"):
            return self._field_of_constants
        if not self.constant_base_field().is_finite():
            raise NotImplementedError('Computation of field of constants only implemented for finite fields.')
        F = self.function_field()
        if F.degree() == 1:
            self._field_of_constants = F.constant_base_field()
            return self._field_of_constants
        else:
            G = F.polynomial().monic()
            self._field_of_constants = field_of_constant_degree_of_polynomial(G, return_field=True)
            return self._field_of_constants

    def field_of_constants_degree(self):
        r""" Return the degree of the field of constants over the constant base field.

        If `F` is the function field of the curve and `k` the constant base field,
        then the *field of constants* `k_c` is the algebraic closure of `k` in `F`.

        If `k` is a finite field then we actually compute the field of constants,
        and the result is provably correct. If `k` is a number field, then we use
        a heuristic method: we find at least `10` different primes of `k` for which
        the reduction of the defining equation remains irreducible, and then we
        apply the method for finite fields to the reduced equation. The result
        is very likely the true degree of the field of constants, and if the
        result is equal to `1` then it is provably correct.

        EXAMPLES::

            sage: from mclf import *
            sage: k = GF(2^3)
            sage: F.<x> = FunctionField(k)
            sage: R.<y> = F[]
            sage: G = (y+x)^4 + (y+x) + 1
            sage: F1.<y> = F.extension(G)
            sage: Y1 = SmoothProjectiveCurve(F1, GF(2))
            sage: Y1.field_of_constants_degree()
            12
            sage: F.<x> = FunctionField(QQ)
            sage: R.<y> = F[]
            sage: G = y^4 + x*y + 1
            sage: F2.<y> = F.extension(G)
            sage: Y2 = SmoothProjectiveCurve(F2)
            sage: Y2.field_of_constants_degree()
            1
            sage: R.<y> = F[]
            sage: G = (y+x)^3 + (y+x) + 1
            sage: F3.<y> = F.extension(G)
            sage: Y3 = SmoothProjectiveCurve(F3)
            sage: Y3.field_of_constants_degree()
            3
            sage: Y3.genus()
            0


        .. TODO::

            - implement a deterministic algorithm for number fields

        """
        if hasattr(self, "_field_of_constants_degree"):
            return self._field_of_constants_degree
        F = self.function_field()
        if F.degree() == 1:
            return self._extra_extension_degree
        else:
            G = F.polynomial().monic()
            return field_of_constant_degree_of_polynomial(G)*self._extra_extension_degree

    def covering_degree(self):
        r"""
        Return the degree of this curve as a covering of the projective line.

        """
        return self._covering_degree

    def function_field(self):
        """
        Return the function field of the curve ``self``.

        """
        return self._function_field.codomain()

    def rational_function_field(self):
        r"""
        Return the rational function field underlying the function field of `X`.

        By definition, the function field `F_X` of the curve `X` is a finite
        separable extension of a rational function field `k(x)`, where `k` is
        the base field of `X`.

        """
        return self._function_field.rational_function_field()

    def structure_map(self):
        r""" Return the canonical map from this curve to the projective line.

        """
        if hasattr(self, "_structure_map"):
            return self._structure_map
        else:
            from mclf.curves.morphisms_of_smooth_projective_curves import\
                                               MorphismOfSmoothProjectiveCurves
            X = SmoothProjectiveCurve(self.rational_function_field())
            self._structure_map = MorphismOfSmoothProjectiveCurves(self, X)
            return self._structure_map

    def coordinate_functions(self):
        r""" Return a list of coordinate functions.

        By 'list of coordinate functions' we mean elements `f_i` in
        the function field, such that the map

        .. MATH::

              x \mapsto (f_1(x),\ldots, f_n(x))

        from `X` to `(\mathbb{P}^1)^n` is injective.

        Note that this map may not be an embedding, i.e. image of this map may
        not be a smooth model of the curve.

        """
        if hasattr(self, "_coordinate_functions"):
            return self._coordinate_functions

        F = self.function_field()
        F0 = F.base_field()
        if F0 is F:
            self._coordinate_functions = [F.gen()]
            return [F.gen()]

        # F is an extension of a rational ff F0
        ret = [F0.gen(), F.gen()]     # the coordinates of the affine plane model
        v0 = F0.valuation(~F0.gen())
        V = v0.extensions(F)          # list of points at infinity
        separate_points(ret, V)       # make sure they are separated
        V0 = self.singular_locus()
        for v0 in V0:
            separate_points(ret, v0.extensions(F))
            # separate all intersection points of the affine plane model
        self._coordinate_functions = ret
        return ret

    def random_point(self):
        """
        Return a random closed point on the curve.

        """
        F = self.function_field()
        F0 = self.rational_function_field()
        R = F0._ring
        f = R.random_element(degree=(1, 3)).factor()[0][0](F0.gen())
        v0 = F0.valuation(f)
        V = v0.extensions(F)
        v = V[randint(0, len(V)-1)]
        return PointOnSmoothProjectiveCurve(self, v)

    def principal_divisor(self, f):
        r""" Return the principal divisor of ``f``.

        INPUT:

        - ``f`` -- a nonzero element of the function field of ``self``

        OUTPUT:  the principal divisor `D =(f)`. This is a list of pairs `(P, m)`,
        where `P` is a point and `m` is an integer.

        """
        F = self.function_field()
        F0 = F.base_field()
        is_rational = (F is F0)
        D = []
        for g, m in f.norm().factor():
            v0 = F0.valuation(g)
            if is_rational:
                P = PointOnSmoothProjectiveCurve(self, v0)
                D.append((P, P.order(f)))
            else:
                for v in v0.extensions(F):
                    P = PointOnSmoothProjectiveCurve(self, v)
                    D.append((P, P.order(f)))
        v0 = F0.valuation(F0.gen()**(-1))
        if is_rational:
            P = PointOnSmoothProjectiveCurve(self, v0)
            D.append((P, P.order(f)))
        else:
            for v in v0.extensions(F):
                P = PointOnSmoothProjectiveCurve(self, v)
                D.append((P, P.order(f)))
        assert self.degree(D) == 0, "Something is wrong: the degree of (f) is not zero!"
        return D

    def divisor_of_zeroes(self, f):
        r""" Return the divisor of zeroes of ``f``.
        """
        D = self.principal_divisor(f)
        ret = []
        for x, m in D:
            if m > 0:
                ret.append((x, m))
        return ret

    def divisor_of_poles(self, f):
        r""" Return the divisor of poles of ``f``.
        """
        D = self.principal_divisor(f)
        ret = []
        for x, m in D:
            if m < 0:
                ret.append((x, -m))
        return ret

    def degree(self, D):
        r""" Return the degree of the divisor ``D``.

        Note that the degree of `D` is defined relative to the
        field of constants of the curve.
        """
        deg = ZZ.zero()
        for P, m in D:
            deg += m*P.degree()
        return deg

    def separable_model(self):
        r"""
        Return the separable model of this curve.

        OUTPUT: a smooth projective curve over the same constant base field

        The *separable model* of this curve `Y` is a curve `Y_s` defined over the
        same constant base field and whose defining equation realizes `Y_s`
        as a finite *separable* cover of the projective line. It comes equipped
        with a finite, purely inseparable morphism `Y\to Y_s`. In particular,
        `Y_s` has the same genus as `Y`.

        The inclusion of function fields `\phi:F(Y_s)\to F(Y)` can be accessed
        via the method ``phi()``, the degree of the extension `Y/Y_s` via the
        method ``degree_of_inseparability``.

        """
        if self.is_separable():
            return self
        else:
            return self._separable_model

    def is_separable(self):
        r"""
        Check whether this curve is represented as a separable cover of the projective line.

        """
        if not hasattr(self, "_is_separable"):
            self.compute_separable_model()
        return self._is_separable

    def phi(self):
        r""" Return the natural embedding of the function field of the separable
        model into the function field of this curve.

        OUTPUT: a field homomorphism

        """
        if self.is_separable():
            F = self.function_field()
            y = F.gen()
            return F.hom([y])
        else:
            return self._phi

    def degree_of_inseparability(self):
        r"""
        Return the degree of inseparability of this curve.

        OUTPUT: positive integer, which is a power of the characteristic of the
        function field of this curve.

        """
        if self.is_separable():
            return ZZ(1)
        else:
            return self._degree_of_inseparability

    def compute_separable_model(self):
        r"""
        Compute a separable model of the curve (if necessary).

        OUTPUT: ``None``

        This function only has to be called only once. It then decides whether
        or not the function field of the curve is given as a separable extension
        of the base field or not. If it is not separable then we compute a
        separable model, which is a tripel `(Y_1,\phi, q)` where

        - `Y_1` is a smooth projective curve over the same constant base field
          `k` as the curve `Y` itself, and which is given by a separable extension,
        - `\phi` is a field homomorphism from the function field of `Y_1` into
          the function field of `Y` corresponding to a purely inseparable extension,
        - `q` is the degree of the extension given by `\phi`, i.e. the degree of
          inseparability of the map `Y\to Y_1` given by `\phi`.
          Note that `q` is a power of the characteristic of `k`.

        """
        F = self.function_field()
        p = F.characteristic()
        if p == 0:
            self._is_separable = True
            return
        F0 = F.base_field()
        if F is F0:
            self._is_separable = True
            return
        G = F.polynomial()
        q = ZZ(1)
        while q < G.degree():
            if all([G[i].is_zero() for i in range(G.degree()+1) if not (p*q).divides(i)]):
                q = q*p
            else:
                break
        # now q is the degree of inseparability
        if q.is_one():
            self._is_separable = True
            return
        # now q>1 and hence F/F_0 is inseparable
        self._is_separable = False
        self._degree_of_inseparability = q
        R1 = PolynomialRing(F0, F.variable_name()+'_s')
        G1 = R1([G[q*i] for i in range((G.degree()/q).floor()+1)])
        F1 = F0.extension(G1, R1.variable_name())
        self._separable_model = SmoothProjectiveCurve(F1)
        self._phi = F1.hom([F.gen()**q])
        self._degree_of_inseparability = q

    def canonical_divisor(self):
        pass

    def plane_equation(self):
        r""" Return the plane equation of this curve.

        OUTPUT:

        A polynomial in two variables over the constant base field which defines
        the plane model of this curve, where the first variable corresponds to
        the base field F0.

        """
        FY = self.function_field()
        K = self.constant_base_field()
        A = PolynomialRing(K, ['x', 'y'])
        x, y = A.gens()
        G = FY.polynomial()
        h = lcm([G[i].denominator() for i in range(G.degree()+1)])
        G = G*h
        ret = A.zero()
        for i in range(G.degree() + 1):
            ret = ret + G[i].numerator()(x)*y**i
        return ret

    def prime_of_good_reduction(self):
        r""" Return a prime ideal where this curve has good reduction.

        OUTPUT:

        We assume that the constant base field `K` is a number field. We return
        a discrete valuation `v` on `K` such that the following holds:

        - all the coefficients of the plane equation `G(x,y)=0` of this curve
          are `v`-integral
        - the reduction of `G` to the residue field of `v` is irreducible and
          defines a plane curve with the same genus as the original curve.

        Note that this implies that `v` is inert in the field of constants of
        the curve.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<T> = QQ[]
            sage: K.<zeta> = NumberField(T^2+T+1)
            sage: A.<x,y> = K[]
            sage: X = SmoothProjectiveCurve(y^3 - y - x^2 + 1 + zeta)
            sage: X.prime_of_good_reduction()
            5-adic valuation
            sage: X.good_reduction(_)
            the smooth projective curve with Function field in y defined by y^3 + 4*y + 4*x^2 + u1 + 1

        """
        from sage.rings.number_field.number_field import NumberFields
        from sage.misc.misc_c import prod
        from sage.rings.fast_arith import prime_range
        from sage.rings.rational_field import QQ

        K = self.constant_base_field()
        assert K in NumberFields(), "the constant base fields has to be a number field"
        G = self.plane_equation()
        n = self.covering_degree()
        # we find an integer N which is divided by any prime we need to avoid
        # first we exclude primes wrt which G is not integral
        N = lcm([c.norm().denominator() for c in G.coefficients()])
        D = G.discriminant(G.parent().gens()[1]).univariate_polynomial()
        factors = D.factor()
        N = N*factors.unit().norm().numerator()
        N = N.radical()
        if len(factors) > 0:
            N = N*prod([f for f, m in factors]).discriminant().norm().numerator()
        # N = N.radical()
        for p in prime_range(n+1, 100):
            if not p.divides(N):
                for v_p in QQ.valuation(p).extensions(K):
                    Gb = G.map_coefficients(v_p.reduce, v_p.residue_field())
                    if len(Gb.factor()) == 1:
                        return v_p

    def good_reduction(self, v_p):
        r""" Return the reduction of this curve at a prime of good reduction.

        INPUT:

        - ``v_p`` -- a discrete valuation on the constant base field `K`

        OUTPUT: the reduction of this curve with respect to `v_p`, assuming
        that this is again a smooth projective curve of the same genus.
        Otherwise, an error is raised.

        Note that we just reduce the plane equation for this curve with respect
        to `v_p`. This is a very naive notion of good reduction. If it works,
        then the curve does indeed have good reduction at `v_p`, and the result
        is correct.

        """
        G = self.plane_equation()
        assert all(v_p(c) >= 0 for c in G.coefficients()), "the plane equation is not integral wrt. v_p"
        Gb = G.map_coefficients(v_p.reduce, v_p.residue_field())
        return SmoothProjectiveCurve(Gb)

    def potential_branch_divisor(self):
        r""" Return list of valuations containing the branch locus.

        OUTPUT:

        A list of pairs `(v,d)', where `v` runs over a list of valuations of the
        base field `F_0 = K(x)` containing all the valuations corresponding to a
        branch point of the cover of curves, and `d` is the degree of `v`.

        """
        FY = self.function_field()
        FX = self.rational_function_field()
        if FX is FY:
            return []
        # We return a list V of valuations of FX containing the branch locus
        # first we add the valuation at infinity
        V = [(FX.valuation(1/FX.gen()), 1)]
        # now we use the plane equation and compute the discriminant wrt x
        G = self.plane_equation()
        R = PolynomialRing(self.constant_base_field(), 'x')
        D = R(G.discriminant(G.parent().gens()[1]))
        for f, m in D.factor():
            V.append((FX.valuation(FX(f)), f.degree()))
        return V

    def ramification_divisor(self):
        r""" Return the ramification divisor of self.

        OUTPUT:

        The ramification divisor of the curve, if the curve is given by
        a separable model. Otherwise, an error is raised.

        So the function field of of the curve is a finite separable extension
        of a rational function field. Geometrically, this means that
        the curve `X` is represented as a separable cover of
        the projective line. The ramification divisor of this cover
        is supported in the set of ramification points of this cover.
        Sheaf theoretically, the divisor represents the sheaf of relative
        differentials. See:

        - Hartshorne, *Algebraic Geometry*, Definition IV.2.

        """
        if not self._is_separable:
            raise Exception("Y is not separable, hence the ramification divisor is not defined")
        if hasattr(self, "_ramification_divisor"):
            return self._ramification_divisor

        FY = self._function_field
        FX = FY.base_field()
        R = []
        if FX is FY:
            return R   # the cover is trivial, hence R=0
        supp = []      # compute the support of R
        D = FY.polynomial().discriminant()
        for f, m in D.factor():
            supp += FX.valuation(f).extensions(FY)
        supp += FX.valuation(~FX.gen()).extensions(FY)
        for v in supp:
            P = PointOnSmoothProjectiveCurve(self, v)
            t = v.uniformizer()
            F = t.minimal_polynomial('T')
            Ft = F.derivative()(t)
            x = FX.gen()
            dx = FX.derivation()
            if P.order(x) < 0:
                der = lambda f: -x**2*dx(f)
            else:
                der = dx
            Fx = F.map_coefficients(der)(t)
            m = P.order(Ft) - P.order(Fx)
            R.append((P, m))
        self._ramification_divisor = R
        return R

    def genus(self, use_reduction=True):
        r""" Return the genus of the curve.

        INPUT:

        - ``use_reduction`` -- a boolean (default: ``True``)

        OUTPUT: the genus of this curve.

        The genus of the curve is defined as the dimension of
        the cohomology group `H^1(X,\mathcal{O}_X)`, as a vector space
        *over the field of constants `k_c`*.

        The genus `g` of the curve `X` is computed using the Riemann-Hurwitz
        formula, applied to the cover `X\to\mathbb{P}^1` corresponding to the
        underlying realization of the function field of `X` as a finite
        separable extension of a rational function field. See:

        - Hartshorne, *Algebraic Geometry*, Corollary IV.2.4

        If the constant base field is finite, we compute the degree of the
        'ramification divisor'. If it is not, we assume that the characteristic
        is zero, and we use the 'tame' Riemann Hurwitz Formula.

        If the curve is defined over a number field, and ``use_reduction`` is
        ``True`` (the default) then the genus of a reduction of this curve to
        some prime of good reduction is computed. This may be consderably
        faster.

        EXAMPLES::

            sage: from mclf import *
            sage: F0.<x> = FunctionField(GF(2))
            sage: R.<T> = F0[]
            sage: G = T^2 + T + x^3 + x + 1
            sage: F.<y> = F0.extension(G)
            sage: Y = SmoothProjectiveCurve(F)
            sage: Y.genus()
            1
            sage: G = T^2 + x^3 + x + 1
            sage: F.<y> = F0.extension(G)
            sage: Y = SmoothProjectiveCurve(F)
            sage: Y.genus()
            0

        """
        from sage.categories.number_fields import NumberFields
        if hasattr(self, "_genus"):
            return self._genus
        if not self._is_separable:
            self._genus = self.separable_model().genus()
            return self._genus
        FY = self.function_field()
        FX = self.rational_function_field()
        if FX is FY:
            self._genus = 0
            return 0
        n = self.covering_degree()/self.field_of_constants_degree()
        K = self.constant_base_field()

        if K.is_finite() and K.characteristic() <= n:
            r = self.degree(self.ramification_divisor())
            # if the characteristic is not larger than the covering degree,
            # we can't use the 'tame' RHF
            g = ZZ(-n + r/2 + 1)
        elif K in NumberFields() and use_reduction:
            # we use reduction to compute the genus
            v_p = self.prime_of_good_reduction()
            g = self.good_reduction(v_p).genus()
        elif K.characteristic() > n:
            # we can use the tame RHF
            V = self.potential_branch_divisor()
            r = 0
            for v, d in V:
                v = v/v(v.uniformizer())
                W = v.extensions(FY)
                for w in W:
                    e, f = e_f_of_valuation(w)
                    r += d*f*(e-1)
            g = ZZ(-n + r/2 + 1)
        else:
            raise NotImplementedError("constant base field must be finite or have characteristic zero")

        self._genus = g
        return g

    def count_points(self, d):
        r""" Return number of points of degree less or equal to ``d``.

        INPUT:

        - ``d`` -- an interger `\geq 1`

        OUTPUT:

        a list ``N``, where ``N[i]`` is the number of points on self
        of *absolute* degree `i`, for `i=1,..,d`.

        Recall that the absolute degree of a point is the degree of
        the residue field of the point over the constant base field
        (*not* over the field of constants).

        This is a very slow realization and should be improved at some point.
        """
        F = self._function_field
        F0 = F.base_field()
        K = self._constant_base_field
        assert K.is_finite(), "Base field must be finite."
        p = K.characteristic()
        d0 = K.degree()
        q = K.cardinality()
        assert q == p**d0

        # compute all nonconstant irreducible polynomials of degree <= g
        R = F0._ring
        x = R.gen()
        polys = set([x])
        for k in range(1, d+1):
            G = (x**(q**k-1)-1).factor()
            for g, e in G:
                polys.add(g)
        # count points
        N = [0]*(d+1)
        for g in polys:
            v0 = F0.valuation(g)
            for v in v0.extensions(F):
                L = v.residue_field()
                try:
                    from_L, to_L, L = L.absolute_extension()
                except AttributeError:
                    pass
                k = ZZ(L.degree()/d0)
                if k <= d:
                    N[k] += 1
        v0 = F0.valuation(~F0.gen())
        # points at infinity
        for v in v0.extensions(F):
            L = v.residue_field()
            try:
                from_L, to_L, L = L.absolute_extensions()
            except AttributeError:
                pass
            k = ZZ(L.degree()/d0)
            if k <= d:
                N[k] += 1
        return N

    def zeta_function(self, var_name='T'):
        r""" Return the Zeta function of the curve.

        For any scheme `X` of finite type over `\mathbb{Z}`, the **arithmetic
        zeta funtion** of `X` is defined as the product

        .. MATH::

             \zeta(X,s) := \prod_x \frac{1}{1-N(x)^{-s}},

        where `x` runs over over all closed points of `X` and `N(x)`
        denotes the cardinality of the residue field of `x`.

        If `X` is a smooth projective curve over a field with
        `q` elements, then `\zeta(X,s) = Z(X,q^{-s})`,
        where `Z(X,T)` is a rational function in `T` of the form

        .. MATH::

               Z(X,T) =  \frac{P(T)}{(1-T)(1-qT)},

        for a polynomial `P` of degree `2g`, with some extra properties
        reflecting the Weil conjectures. See:

        - Hartshorn, *Algebraic Geometry*, Appendix C, Section 1.

        Note that that this makes only sense if the constant base
        field of self is finite, and that `Z(X,T)` depends on the
        choice of the constant base field (unlike the function
        `\zeta(X,s)`!).

        """
        if hasattr(self, "_zeta_function"):
            return self._zeta_function

        K = self._constant_base_field
        q = K.order()
        g = self.genus()
        S = PowerSeriesRing(ZZ, var_name, g+1)
        N = self.count_points(g)
        Z_series = S(1)
        for k in range(1, g+1):
            Z_series *= (1-S.gen()**k)**(-N[k])
        P = (Z_series*(1-S.gen())*(1-q*S.gen())).polynomial()
        c = list(range(2*g+1))
        for k in range(g+1):
            c[k] = P[k]
        for k in range(g+1, 2*g+1):
            c[k] = c[2*g-k]*q**(k-g)
        R = P.parent()
        zeta = R(c)/(1-R.gen())/(1-q*R.gen())
        self._zeta_function = zeta
        return zeta

    def points_with_coordinates(self, a):
        r""" Return all points with given coordinates.

        INPUT:

        - ``a`` -- a tupel of coordinates, of lenght `n`, at most the
          number of coordinate functions of the curve

        OUTPUT:

        a list containing all points on the curve whose first
        `n` coordinate values agree with ``a``.

        """
        n = len(a)
        assert n >= 1, "You must give at least one coordinate!"
        assert n <= len(self._coordinate_functions), "Too many coordinates given."
        F = self._function_field
        F0 = F.base_field()
        if a[0] == Infinity:
            v0 = F0.valuation(~F0.gen())
        else:
            v0 = F0.valuation(F0.gen()-a[0])
        if F0 is F:
            return self.point(v0)
        V = v0.extensions(F)
        f = self.coordinate_functions()
        ret = []
        for v in V:
            if all([compute_value(v, f[i]) == a[i] for i in range(n)]):
                ret.append(self.point(v))
        return ret

    def fiber(self, v0):
        r"""
        Return the set of points lying above a point on the projective line.

        INPUT:

        - ``v0`` -- a function field valuation on the rational function field

        OUTPUT:

        a list containing the points on this curve `Y` corresponding to extensions
        of ``v0`` to the function field of `Y`.

        """
        V = v0.extensions(self.function_field())
        return [PointOnSmoothProjectiveCurve(self, v) for v in V]

    def base_change(self, L):
        r""" Return the base change of this curve wrt a field extension.

        If `X` is a (irreducible) smooth projective curve over a field `K`, and
        `L/K` is a separable field extension, then the base change `X_L:=X\otimes_K L`
        is a smooth projecitve (but not necessarily irreducible) curve over `L`.

        INPUT:

        - ``L`` -- a field extension of the constant base_field of this curve `X`

        OUTPUT:

        a list containing all the irreducible factors of the base change of `X`
        to `L`.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<t> = QQ[]
            sage: K = NumberField(t^2+1, "i")
            sage: S.<x,y> = QQ[]
            sage: Y = SmoothProjectiveCurve(x^2+y^2)
            sage: Y.base_change(K)
            [the smooth projective curve with Function field in y defined by y - i*x,
             the smooth projective curve with Function field in y defined by y + i*x]

        """
        from mclf.field_extensions.field_extensions import FieldExtension
        from sage.all import FunctionField
        F = self.function_field()
        F_L = F.base_change(L)

        K = self.constant_base_field()
        if isinstance(L, FieldExtension):
            assert L.base_field() is K
        else:
            assert L.has_coerce_map_from(K)
            L = FieldExtension((L, K))
        FX = self.rational_function_field()
        FX_L = FunctionField(L.codomain(), FX.variable_name())
        G_L = self.function_field().polynomial().change_ring(FX_L)
        ret = []
        for g, _ in G_L.factor():
            ret.append(SmoothProjectiveCurve(FX_L.extension(g)))
        return ret

# ----------------------------------------------------------------------------


class PointOnSmoothProjectiveCurve(SageObject):
    r""" A closed point on a smooth projective curve.

    A point on a curve `X` is identified with the corresponding
    normalized valuation `v_x` on the function field `F` of `X`.

    INPUT:

    - ``X`` -- a smooth projective curve
    - ``v`` -- a discrete valuation on the function field of `X` which is trivial
               on the constant base field

    OUTPUT:

    The point `x` on `X` such that `v_x` is equivalent to `v`.

    Alternatively, a point `x` on `X` can be represented by the vector

    .. MATH::

         [v_x(f_1),\ldots, v_x(f_n)]

    where `f_1,\ldots,f_n` is a list of *coordinate functions*, i.e. rational
    functions which define an injective map from `X` into
    `\mathbb{P}^1\times\ldots\times\mathbb{P}^1`.

    We use the latter representation to check for equality of points.
    """

    def __init__(self, X, v):
        self._curve = X
        self._valuation = v/v(v.uniformizer())

    def __repr__(self):
        return "Point on {} with coordinates {}.".format(self._curve, self.coordinates())

    def curve(self):
        """ Return the underlying curve of the point.
        """
        return self._curve

    def valuation(self):
        """ Return the valuation corresponding to the point.
        """
        return self._valuation

    def residue_field(self):
        """ Return the residue field of the point.

        .. NOTE::

            This should be a relative extension of the constant base field of the curve.
            Unfortunately, this is not true in general!

        """
        return self._valuation.residue_field()

    def absolute_degree(self):
        r""" Return the absolute degree of self.

        The *absolute degree* of a point `x` on a curve `X` over `k` is the
        degree of the extension `k(x)/k`.

        Here `k` is the constant base field of the curve, which may not be equal to
        the field of constants.
        """
        if not hasattr(self, "_absolute_degree"):
            self._absolute_degree = extension_degree(self._curve._constant_base_field, self._valuation.residue_field())
        return self._absolute_degree

    def degree(self):
        r""" Return the degree of self.

        The *degree* of a point `x` on a curve `X` over `k` is the degree of the
        residue field `k(x)` as an extension of the field of constants of `X`.
        The latter may be a proper extension of the base field `k`!

        """
        if not hasattr(self, "_degree"):
            self._degree = ZZ(extension_degree(self._curve._constant_base_field, self._valuation.residue_field())/self._curve._field_of_constants_degree)
        return self._degree

    def value(self, f):
        r""" Return the value of the function ``f`` in the point.

        If ``f`` has a pole then ``Infinity`` is returned.
        """

        if self._valuation(f) < 0:
            return Infinity
        else:
            return self._valuation.reduce(f)

    def order(self, f):
        r""" Return the order of the function in the point.

        This is the same as ``self.valuation()(f)``.
        """

        return self._valuation(f)

    def coordinates(self):
        r""" Return the coordinate tupel of the point.

        NOTE:

        for a curve over a number field and for a point whose residue field
        is of high degree, this can be *very* slow.
        It would be better to implement this function in a lazy way,
        for instance as an iterator.
        """

        if not hasattr(self, "_coordinates"):
            self._coordinates = tuple([self.value(x) for x in self._curve.coordinate_functions()])
        return self._coordinates

    def is_equal(self, P):
        r""" Check whether this point is equal to P.

        INPUT:

        - ``P`` -- a point on the curve underlying this point

        OUTPUT:

        ``True`` is `P` is equal to ``self``, ``False`` otherwise.

        Currently, the check for equality is done using the 'coordinates' of the
        points. This may be very slow. It would probably be better to test the
        equality of the underlying valuations. But here we can't rely on Sage,
        so this would require a hack.

        EXAMPLES::

            sage: import mclf.curves.smooth_projective_curves
            sage: from mclf.curves.smooth_projective_curves import SmoothProjectiveCurve
            sage: F0.<x> = FunctionField(GF(3))
            sage: R.<y> = F0[]
            sage: F.<y> = F0.extension(y^2 - (x+1)*x^2)
            sage: Y = SmoothProjectiveCurve(F)
            sage: v0 = F0.valuation(x)
            sage: fiber = Y.fiber(v0)
            sage: fiber[0].is_equal(fiber[1])
            False

        """
        return self.coordinates() == P.coordinates()

    def base_change(self, L):
        r""" Return the list of points on the base to L above this one.

        INPUT:

        - ``L`` -- a finite field extension of the constant base field of the curve

        OUTPUT:

        the list of points on the base change `X_L` above this point.

        These points are objects of the class :class:`ExtensionPointOnSmoothProjectiveCurve`.
        (really? Why?)

        EXAMPLES::

            sage: from mclf import *
            sage: R.<t> = QQ[]
            sage: K = NumberField(t^2+1, "i")
            sage: S.<x,y> = QQ[]
            sage: Y = SmoothProjectiveCurve(y^2 - x^3 + 1)
            sage: FX = Y.rational_function_field()
            sage: x = FX.gen()
            sage: v = FX.valuation(x-1)
            sage: P = Y.fiber(v)[0]
            sage: P
            Point on the smooth projective curve with Function field in y defined
            by y^2 - x^3 + 1 with coordinates (1, 0).
            sage: P.base_change(K)

        """
        Y = self.curve()
        x = self.base_point()  # this is the image of this point on the projective line
        Y_L = Y.base_change(L)
        ret = []
        for Z in Y_L:
            pass
        return ret


class ExtensionPointOnSmoothProjectiveCurve(PointOnSmoothProjectiveCurve):
    r""" An object representing an L-point on the curve.

    If `Y` is a smooth projective curve over a field `K`, and `L/K` is a field
    extension, then we call an *`L`-point* on `Y` a closed point `y\in Y`,
    together with a `K`-linear embedding of `L` into the residue field `k(y)`.

    Note that an `L`-point `x` on `X` is the same thing as a closed point on the
    curve `X_L`, the base change of `X` to `L`. Therefore, it corresponds to
    a discrete, normalized valuation `v_x` on the function field of `X_L`.

    One caveat: the curve `X_L` may not be irreducible anymore (something we
    usually assume for a smooth projective curve). If this is the case then
    the "function field" of `X_L` is a finite commutative algebra over the
    function field of `X`. The valuation `v_x` is then a normalized valuation
    on exactly one of the irreducible factors of this algebra, and trivial on
    all others.

    INPUT:

    - ``X`` -- a smooth projective curve, with constant base field `K`
    - ``L`` -- a finite field extension of the constant base field of `X`
    - ``v`` -- a discrete valuation on an irreducible factor of the function
               field of `X_L`

    OUTPUT:

    The `L`-point `x` on `X` given by `v`.

    """

    def __init__(self, X, v):
        pass

    def __repr__(self):
        return "point on {} over {}, given by  {}".format(self.curve(), self.base_field(), self.valuation())

    def curve(self):
        return self._curve

    def base_field(self):
        return self._base_field

    def valuation(self):
        return self._valuation

    def residue_field(self):
        return self._residue_field

    def base_point(self):
        return self._base_point

# ------------------------------------------------------------------------------

# auxiliary functions


def compute_value(v, f):
    r"""
    Return the value of ``f`` at ``v``.

    INPUT:

    - ``v`` -- a function field valuation on `F`
    - ``f`` -- an element of `F`

    OUTPUT: The value of ``f`` at the point corresponding to ``v``.

    This is either an element of the residue field of the valuation ``v``
    (which is a finite extension of the base field of `F`), or `\infty`.

    """
    from sage.rings.infinity import Infinity

    if v(f) < 0:
        return Infinity
    else:
        return v.reduce(f)


def separate_points(coordinate_functions, valuations):
    r"""
    Add new coordinate functions to separate a given number of points.

    INPUT:

    - ``coordinate_functions`` -- a list of elements of a function field `F`
    - ``valuations`` -- a list of function field valuations on `F`

    OUTPUT: enlarges the list ``coordinate_functions`` in such a way
    that the lists ``[value(v,x) for x in coordinate_functions]``,
    where ``v`` runs through ``valuations``, are pairwise distinct.

    """
    repeat = True
    while repeat:
        dict = {}
        for v in valuations:
            a = tuple([compute_value(v, x) for x in coordinate_functions])
            v1 = dict.get(a)
            if v1:
                coordinate_functions.append(separate_two_points(v, v1))
                repeat = True
                break
            else:
                dict[a] = v
                repeat = False
    return coordinate_functions


def separate_two_points(v1, v2):
    r""" Return a rational function which separates two points

    INPUT:

    - ``v1``, ``v2`` -- discrete, nonequivalent  valuations on a common function field `F`

    OUTPUT:

    An element `f` of `F` which takes distinct values at the two points corresponding
    to ``v1`` and ``v2``.

    """
    # first a simple ad hoc test
    # this should always work if F is a rational function field
    f1 = v1.uniformizer()
    f2 = v2.uniformizer()
    test_elements = [f1, f2, f1/f2, f2/f1]
    for f in test_elements:
        if compute_value(v1, f) != compute_value(v2, f):
            return f
    # we can now assume that F is a finite extension of a rational function field
    # Then v1 is either induced from a (pseudo)-valuation w1 on a polynomial
    # ring or from a function field valuation via an automorphism
    # In the first case we use the explicit realization of w1 to construct an element g,
    # or a sequence of elements g, such that v1(g) goes to infinity
    w1 = v1._base_valuation
    if hasattr(w1, "_approximation"):
        # w1 is a limit valuation
        # we try to approximate it
        loops = 0
        # 10 loops should be enough
        while loops < 10:
            w1._improve_approximation()
            u1 = w1._approximation
            g = v1._from_base_domain(u1.phi())
            f = g/v2.element_with_valuation(v2(g))
            if compute_value(v1, f) != compute_value(v2, f):
                return f
            loops += 1
        raise ValueError
    elif hasattr(w1, "_phi"):
        # w1 is an inductive valuation and hence w1.phi is a polynomial
        # of 'minimal degree with maximal valuation'
        g = v1._from_base_domain(w1.phi())
        f = g/v2.element_with_valuation(v2(g))
        if compute_value(v1, f) != compute_value(v2, f):
            return f
    else:
        # probably, v1 is induced from w1 by an isomorphism of function fields
        w2 = v2._base_valuation
        if w2.domain() == w1.domain():
            f = separate_two_points(w1, w2)
            return v1._from_base_domain(f)
        elif w1.domain() == v2.domain():
            return separate_two_points(w1, v2)
    raise NotImplementedError


def absolute_degree(K):
    r"""
    Return the absolute degree of a (finite) field.

    """
    assert K.is_finite(), "K must be finite!"
    p = K.characteristic()
    q = K.cardinality()
    return q.log(p)


def extension_degree(K, L, check=False):
    r""" Return the degree of the field extension.

        INPUT:

        - ``K``, ``L`` -- two fields, where ``K`` has a natural embedding into ``L``
        - ``check`` (default: ``False``) -- boolean

        OUTPUT:

        the degree `[L:K]`

        At the moment, this works correctly only if `K` and `L` are
        finite extensions of a common base field. It is not checked
        whether `K` really maps to `L`.

    """
    assert K.characteristic() == L.characteristic(), "K and L must have the same characteristic."
    if hasattr(K, "absolute_extension"):
        K = K.absolute_extension()[2]
    if hasattr(L, "absolute_extension"):
        L = L.absolute_extension()[2]
    try:
        n = K.absolute_degree()
    except (AttributeError, NotImplementedError):
        n = absolute_degree(K)
    try:
        m = L.absolute_degree()
    except (AttributeError, NotImplementedError):
        m = absolute_degree(L)
    assert n.divides(m), "K is not a subfield of L."
    return ZZ(m/n)


def sum_of_divisors(D1, D2):
    r""" Return the sum of the divisors ``D1`` and ``D2``.

    INPUT:

    - ``D1``, ``D2``: divisors on the same curve `X`

    OUTPUT:

    `D_1` is replaced by the sum `D_1+D_2` (note that this changes `D_1`!).

    Here a divisor `D` is given by a dictionary with entries ``(a:(P,m))``,
    where ``a`` is a coordinate tupel, ``P`` is a point on `X` with coordinates
    ``a`` and ``m`` is the multiplicity of ``P`` in `D`.
    """

    for a in D2.keys():
        P, m2 = D2[a]
        if a in D1.keys():
            Q, m1 = D1[a]
            D1[a] = (P, m1+m2)
        else:
            D1[a] = D2[a]
    return D1


def field_of_constant_degree_of_polynomial(G, return_field=False):
    r""" Return the degree of the field of constants of a polynomial.

    INPUT:

    - ``G`` -- an irreducible monic polynomial over a rational function field
    - ``return_field`` -- a boolean (default:`False`)

    OUTPUT: the degree of the field of constants of the function field defined
    by ``G``. If ``return_field`` is ``True`` then the actual field of constants
    is returned. This is currently implemented for finite fields only.

    This is a helper function for ``SmoothProjectiveCurve.field_of_constants_degree``.

    """
    from sage.rings.function_field.function_field import RationalFunctionField
    from sage.rings.function_field.constructor import FunctionField
    from sage.rings.number_field.number_field import NumberFields
    from sage.arith.misc import primes
    from mclf.semistable_reduction.reduction_trees import make_function_field
    F = G.base_ring()
    assert isinstance(F, RationalFunctionField)
    K = F.constant_base_field()
    R = F._ring   # the polynomial ring underlying F
    n = G.degree()
    if K.is_finite():
        d = 1    # will be the degree of the field of constants at the end
        for p in primes(2, n+1):
            while p.divides(n):
                try:
                    K1 = K.extension(p)
                except:
                    # if K is not a true finite field the above fails
                    # we use a helper function which construct an extension
                    # of the desired degree
                    K1 = extension_of_finite_field(K, p)
                F1 = FunctionField(K1, F.variable_name())
                G1 = G.change_ring(F1)
                G2 = G1.factor()[0][0]   # the first irreducible factor of G1
                if G2.degree() < n:      # G becomes reducible over K1
                    d = d*p              # we replace G by G2 and adapt
                    K = K1               # the values of n, d, K, G
                    G = G2
                    n = G.degree()
                else:                    # G is irreducible over K1
                    break                # we try the next prime
        if return_field:
            return K
        else:
            return d
    elif K in NumberFields():
        from sage.rings.integer_ring import ZZ
        from sage.rings.all import GaussValuation
        if return_field:
            raise NotImplementedError('Computation of field of constants for number fields is not yet implemented.')
        d = n
        count = 0
        for p in K.primes_of_bounded_norm_iter(ZZ(1000)):
            vp = K.valuation(p)
            v0 = F.valuation(GaussValuation(R, vp))
            v = GaussValuation(G.parent(), v0)
            if v(G) == 0:
                Gb = v.reduce(G)
                Fb, _, _ = make_function_field(Gb.base_ring())
                Gb = Gb.change_ring(Fb)
                if Gb.is_irreducible():
                    dp = field_of_constant_degree_of_polynomial(Gb)
                    d = d.gcd(dp)
                    count += 1
            if d == 1 or count > 10:
                break
        return d
    else:
        raise NotImplementedError('Constant base field has to be finite or a number field.')


def e_f_of_valuation(v):
    r""" Return the ramification index of this valuation.

    INPUT:

    - ``v`` -- a function field valuation on an extension of a rational function field

    OUTPUT: the ramification index of `v` over the base field

    """
    from sage.rings.polynomial.polynomial_ring import PolynomialRing_field
    while not isinstance(v.domain(), PolynomialRing_field):
        v = v._base_valuation
    if hasattr(v, "_approximation"):
        v = v._approximation
    return (v.E(), v.F())


def extension_of_finite_field(K, n):
    r""" Return a field extension of this finite field of degree n.

    INPUT:

    - ``K`` -- a finite field
    - ``n`` -- a positive integer

    OUTPUT: a field extension of `K` of degree `n`.

    This function is useful if `K` is constructed as an explicit extension
    `K = K_0[x]/(f)`; then ``K.extension(n)`` is not implemented.

    .. NOTE::

        This function should be removed once ``trac.sagemath.org/ticket/26103``
        has been merged.

    """
    assert K.is_field()
    assert K.is_finite()
    q = K.order()
    R = PolynomialRing(K, 'z'+str(n))
    z = R.gen()
    # we look for a small number e dividing q^n-1 but not q-1
    e = min([d for d in (q**n-1).divisors() if not d.divides(q-1)])
    F = (z**e-1).factor()
    f = [g for g, m in F if g.degree() == n][0]
    # this is very inefficient!
    return K.extension(f, 'z'+str(e))


def make_finite_field(k):
    r""" Return the finite field isomorphic to this field.

    INPUT:

    - ``k`` -- a finite field

    OUTPUT: a triple `(k_1,\phi,\psi)` where `k_1` is a 'true' finite field,
    `\phi` is an isomorphism from `k` to `k_1` and `\psi` is the inverse of `\phi`.

    This function is useful when `k` is constructed as a tower of extensions
    with a finite field as a base field.

    .. NOTE::

        This function should be removed once ``trac.sagemath.org/ticket/26103``
        has been merged.


    """
    assert k.is_field()
    assert k.is_finite()
    if not hasattr(k, "base_field"):
        return k, k.hom(k), k.hom(k)
    else:
        k0 = k.base_field()
        G = k.modulus()
        assert G.parent().base_ring() is k0
        k0_new, phi0, _ = make_finite_field(k0)
        G_new = G.map_coefficients(phi0, k0_new)
        k_new = k0_new.extension(G_new.degree())
        alpha = G_new.roots(k_new)[0][0]
        try:
            phi = k.hom(alpha, k_new)
        except Exception:
            Pk0 = k.cover_ring()
            Pk0_new = k0_new[Pk0.variable_name()]
            psi1 = Pk0.hom(phi0, Pk0_new)
            psi2 = Pk0_new.hom(alpha, k_new)
            psi = psi1.post_compose(psi2)
            # psi: Pk0 --> k_new
            phi = k.hom(Pk0.gen(), Pk0, check=False)
            phi = phi.post_compose(psi)
        alpha_new = k_new.gen()
        for alpha, e in alpha_new.minpoly().roots(k):
            if phi(alpha) == alpha_new:
                break
        phi_inverse = k_new.hom(alpha, k)
        return k_new, phi, phi_inverse
