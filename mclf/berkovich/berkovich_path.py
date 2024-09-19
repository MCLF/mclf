# -*- coding: utf-8 -*-
r"""
Paths on the Berkovich line

Let `K` be a field with a discrete valuation `v_K`. Let `X` be the projective
line over `K` and `X^{an}` the Berkovich analytic space associated to `X` and
`v_K` (the *Berkovich line*).

According to [Ber1990], `X^{an}` is a simply connected quasi-polyhedron.
Basically, this means that any two points `\xi_1,\xi_2` are the endpoints
of a unique closed subset `[\xi_1,\xi_2]\subset X^{an}` homeomorphic to the
closed unit interval. We call `[\xi_1,\xi_2]` the *interval* with endpoints
`\xi_1,\xi_2`. Only the two endpoints can be points of type I.

Let `H\subset X^{an}` be the complement of the set of points of type I (the
*hyperbolic Berkovich space*). On `H` there is a canonical metric

..MATH::  \rho:H\times H \to \RR

called the *path metric*. Restricting `\rho` to an interval `[\xi1,\xi2]`
(with `\xi_1,\xi_2\in H`) gives the latter a canonical metric and affine
structure. In particular, we obtain a natural parametrization

..MATH::  \gamma:[0,r]\to [\xi_1,\xi_2]

which is an isomometry. We call `\gamma` the *path* from `\xi_1` to `\xi_2` and
the real number `r` the *length* of the path.

We can extend this construction to the case where `\xi_2` is a point of type I.
In this case `r=\infty`.

Let `h` be a valuative function on 'X^{an}' (see ??). Then the composition
of `h` with the natural parametrization `gamma` of the path is a continuous and
locally affine function

..MATH::  h\circ\gamma:[0,r]\to\RR\cup\{\pm\infty\}.

Moreover, kinks of this function can only occur in points of type II.

"""

# ****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import SageObject, Infinity
from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine


class AscendingBerkovichPath(SageObject):

    def __init__(self, xi0, xi1):
        r"""
        Create an path `\gamma` with initial point ``xi0`` and endpoint
        ``xi1``. The point ``xi0`` has to be of type II, and
        ``xi0``<=``xi1``.

        We realize `\gamma` as an *induction chain*, which is a list
        `[(v_i, \phi_i, t_i)]`, where `i=0,..,r-1`:

        - `v_i` are inductive valuations on `K[x]`
        - `\phi_i` is a key polynomial for `v_i`
        - `t_i` are positive rational numbers or `\infty`

        such that:

        - `v_{i+1}=[v_i, v_{i+1}(\phi_i)=t_]` for `i=0,..,r-1`
           (for `i=r-1` this defines `v_r`)
        - `v_0` corresponds to the initial point
        - `v_r` corresponds to the terminal point

        """
        assert xi0.type() == "II"
        assert xi0.is_leq(xi1)
        self._X = xi0._X
        self._xi0 = xi0
        self._xi1 = xi1
        self._is_in_unit_disk = xi1.is_in_unit_disk()
        self._is_inductive = xi1.is_inductive()
        v0 = xi0.pseudovaluation_on_polynomial_ring()
        if not self._is_inductive:
            xi1 = xi1.approximation(xi0)
        print("xi1 = %s"%(xi1,))
        vr = xi1.pseudovaluation_on_polynomial_ring()
        print("vr = %s"%(vr,))
        w = vr.augmentation_chain()[::-1]
        print("w = %s"%(w,))
        # this is 'reverse' augmentation chain of vr; the Gauss val. is the first entry
        r = len(w)
        print("r = %s"%(r,))
        # we want to find the index i such that w[i]<=v0<w[i+1]
        i = 0
        while w[i+1] <= v0:
            i += 1
        print("i = %s"%(i,))
        aug_list = [(v0, w[i+1].phi(), w[i+1](w[i+1].phi()))]
        for j in range(i+1, r-1):
            print("j = %s"%(j,))
            aug_list.append((w[j], w[j+1].phi(), w[j+1](w[j+1].phi())))
        self._aug_list = aug_list
        self._phi = aug_list[-1][1]
        self._v0 = aug_list[0][0]
        self._vr = vr
        self._s0 = self._v0(self._phi)
        self._sr = vr(self._phi)
        # the internal attributes are:
        # _X
        # _xi0   : the initial point
        # _xi1   : the endpoint
        # _is_in_unit_disk
        # _is_inductive
        # _aug_list
        # _v0
        # _vr
        # _s0
        # _sr


    def X(self):
        r""" Return the underlying Berkovich line.
        """

        return self._X

    def initial_point(self):
        return self._xi0

    def terminal_point(self):
        return self._xi1

    def length(self):
        r""" Return the length of ``self``, with respect to the
        discoid metric.
        """

        if self._is_inductive:
            return self._sr - self._s0
        else:
            return Infinity


    def _improve_approximation(self, s):
        r""" Improve the approximation of the endpoint.

        If the endpoint of ``self`` is a limit valuation, then we improve
        the internal approximation of it such that self._sr >= s afterwards.
        """

        if self._is_inductive:
            return              # nothing to do
        r = len(self._aug_list)
        v1 = self._xi1.mac_lane_valuation()
        # v1 is a limit valuation
        vr = v1._approximation
        sr = vr(vr.phi())
        while sr < s:
            v1._improve_approximation()
            vr = v1._approximation
            sr = vr(vr.phi())
        self._aug_list[r-1] = (self._aug_list[r-1][0], vr.phi(), sr)
        self._vr = vr
        self._sr = sr
        return

    def point(self, s):
        r""" Return the point on ``self`` at position ``s``.
        """

        if self._is_inductive:
            if s < self._s0 or s > self._sr:
                return None
            else:
                return self._X.point_from_discoid(self._phi, s, self._is_in_unit_disk)
        else:
            if s < self._s0:
                return None
            else:
                self._improve_approximation(s)
                return self._X.point_from_discoid(self._phi, s, self._is_in_unit_disk)

    def direction(self, s):
        r""" Return the directional vector of ``self`` at position ``s``.

        If `\gamma=[\xi_0,\xi_1]` is a (simple) path, parametrized by `[s_0,s_1]`,
        and `s_0 <= s < s_1`, then the directional vector of `gamma` at 's' is
        a point of type V, with underlying point of type II `\gamma(s)`.
        It corresponds to the residue class of `\xi_1` in the discoid
        corresponding to `\gamma(s)`.
        """

        if self._is_inductive:
            assert self._s0 <= s and s < self._sr
        else:
            assert self._s0 <= s
            self._improve_approximation(s)
        return TypeVPointOnBerkovichLine(self.X(), self._phi, s, self._is_in_unit_disk)


    def position(self, xi):
        r""" Return the position of ``xi`` on ``self``.
        """

        v = xi.mac_lane_valuation()
        if self._is_inductive:
            if not self._xi0.is_leq(xi) or not xi.is_leq(self._xi1):
                return None
            else:
                s = v(self._phi)
                assert self._s0 <= s and s <= self._s1
                return s
        else:
            if not self._xi0.is_leq(xi) or not xi.is_leq(self._xi1):
                return None
            else:
                # we need an approximation of xi1 which is greater or equal to xi
                # to correctly compute s
                s = v(self._phi)
                while s > self._sr:
                    self.improve_approximation(s)
                    s = v(self._phi)
                return s

    def derivative(self, f, s):
        r""" Return the derivative of the valuative function corresponding to
        ``f`` at ``s``.
        """

        eta = self.direction(s)
        return eta.derivative(f)/eta.derivative(self._phi)



    def first_kink(self, f):
        r""" Return the first kink on ``self`` of the valuative function
        corresponding to ``f``.

        INPUT:

        - ``f`` -- a polynomial in x or in 1/x

        OUTPUT:

        We consider ``f`` as a polynomial in `K[x]` if ``self`` lies on the
        standard unit disk, or as a polynomial in `K[1/x]` if it doesn't.
        Then the valuative function `\xi\mapsto v_\xi(f)` is continuous and
        piecewise affine on the path ``self``. The output is the parameter
        `t` corresponding to the point on ``self`` where this function has its
        first 'kink'. So if `[s_0,s_1]` is the interval parametrising ``self``,
        then `s_0 < t <= s_1`. If `t = s_1` this means that the function is
        affine on the whole path.
        """
        pass

#--------------------------------------------------------------------------


def augmentation_list(xi0, xi1):

    assert xi0.is_leq(xi1)
    phi1, s1, in_unit_disk = xi1.discoid_representation(xi0)




def next_kink(v, phi, f, start_at=None):
    r""" Return the first kink.

    INPUT:

    - ``v`` -- an inductive valuation on `K[x]`
    - ``phi`` -- a key polynomial for ``v``
    - ``f`` -- an element of `K[x]`
    - ``start_at`` -- a nonnegative rational, or None

    OUTPUT:

    The smallest value where the function `t\mapsto v_t(f)`, with
    `v_t = [v, v_t(\phi)=t]`, has a kink, or Infinity if there is no kink.
    If ``start_at`` is None, then we start with the value `t=v(\phi)`,
    otherwise at ``start_at``.
    """
    assert v.is_key(phi)
    t0 = v(phi)
    if start_at is not None:
        assert t0 <= start_at
        t0 = start_at
    w = v.augmentation(phi, t0, check=False)
    NP = w.newton_polygon(f).principal_part()
    slopes = NP.slopes(repetition=True)
    if len(slopes) < 1:
        return Infinity    # there is no kink
    else:
        return t0 - slopes[-1]
