# -*- coding: utf-8 -*-
r"""
`p`-adic embeddings
===================

Let `K` and `L` be `p`-adic number fields. In this module we define a class
``pAdicEmbedding`` whose objects represent embeddings `\phi:K\to L` over
`\mathbb{Q}_p`.

Here the `p`-adic number fields `K` and `L` are objects of the
class :class:`pAdicNumberField`. This means that `K` and `L` represented as pairs
`(K_0,v_K)` and `(L_0,v_L)`, where e.g. `K_0` is a number field and `v_K` a
`p`-adic valuation on `K_0` such that `K` is the completion of `K_0` at `v_K`.
In fact, we do not work with actual `p`-adic numbers.

Given an embedding `\phi:K\to L`, there need not exist any embedding `K_0\to L_0`
of the underlying number fields. Therefore, the embedding `\phi` has to be
constructed in a rather indirect way. Recall that `K_0` and `L_0` are absolute
number fields generated by prime elements `\pi_K` and `\pi_L` over `\mathbb{Q}`
(with respect to `v_K` and `v_L`). So an embedding `\phi:K\to L` is uniquely
determined by a root of the absolute minimal polynomial `P_K` of `\pi_K` over
`\mathbb{Q}` in `L`. Such a root may be represented e.g. by a (limit) pseudo
valuation `v` on the polynomial ring `L_0[x]` with `v(P_K)=\infty`.




AUTHORS:

- Stefan Wewers (2021-05-5): initial version (adapted from the previous module
  ``fake_padic_embeddings``)


EXAMPLES:



TO DO:


"""


# *****************************************************************************
#       Copyright (C) 2021 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************

from sage.all import SageObject, Infinity, QQ


class pAdicEmbedding(SageObject):
    r"""
    Return an embedding of two `p`-adic number fields.

    INPUT:

    - ``K``, ``L`` -- two `p`-adic number fields, given as objects of
      :class:`pAdicNumberField
    - ``alpha_0`` - an approximation of the desired embedding

    OUTPUT: the embedding of `K` into `L` which is determined by `\alpha_0`.

    The element `\alpha_0\in L_0` of the number field underlying `L` is assumed
    to be an *approximate root* of the minimal poylnomial `f\in \mathbb{Q}[x]` of
    the standard generator of `K/\mathbb{Q}_p`. Here 'approximate root' means
    that the pair `(f, \lapha_0)` satisfies the condition of Hensel's Lemma,
    which guarantees that there exists a unique root `\alpha\in L` of `f`
    strictly closer to `\alpha_0` than any other root. The associated embedding
    is then the map

    .. MATH::

        \phi:K\cong \mathbb{Q}[x]/(f) \to L, \quad x \mapsto \alpha.

    Not that the embedding `\phi` does in general not restrict to a map between
    the underlying number fields, `K_0\to L_0`. Therefore, we cannot compute
    `\phi` exactly, but only approximately. Hensel's Lemma guarantees that
    the root `\alpha` approximated by `\alpha_0` is unique, and that the
    approximation `\alpha_0` can be improved to arbitrary precision via the
    `p`-adic Newton method. This allows us to approximate the map `\phi` up to
    arbitrary precison.

    """

    def __init__(self, K, L, alpha_0):
        L_0 = L.number_field()
        v_L = L.valuation()
        alpha_0 = L_0(alpha_0)
        assert v_L(alpha_0) >= 0
        f = K.polynomial().change_ring(L_0)
        fx = f.derivative()
        s = v_L(f(alpha_0))
        t = v_L(fx(alpha_0))
        assert s >= 2*t + 1, "the approximation alpha_0 does satisfy the condition of Hensel's Lemma"
        self._domain = K
        self._codomain = L
        self._approximate_generator = alpha_0
        self._equation = f
        self._derivative = fx
        self._precision = (s - t)

    def __repr__(self):
        return "an embedding of {} into {}".format(self.domain(), self.codomain())

    def domain(self):
        return self._domain

    def codomain(self):
        return self._codomain

    def precompose(self, psi):
        r""" Return the precompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` -- an embedding of `p`a-dic number fields `\psi:M\to K`,
                     where `K` is the domain of this embedding `\phi`.

        OUTPUT: the composition `\phi\circ\psi`.

        """
        phi = self
        # I have to think harder how to set the precision; this is just
        # a first try:
        s = min(phi.precision(), psi.precision())
        if s == Infinity:
            s = QQ(10)
        alpha = phi.approximate_evaluation(psi.approximate_generator(s), s)
        return pAdicEmbedding(psi.domain(), phi.codomain(), alpha)

    def postcompose(self, psi):
        r""" Return the postcompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` -- an embedding of `p`a-dic number fields `\psi:L\to M`,
                     where `L` is the codomain of this embedding `\phi`.

        OUTPUT: the composition `\psi\circ\phi`.

        """
        return psi.precompose(self)

    def precision(self):
        return self._precision

    def approximate_generator(self, t=None):
        r""" Return an approximation of the image of the generator of the domain.

        INPUT:

        - ``t`` -- a positive rational number, or ``None`` (default: ``None``)

        OUTPUT: an approximation `\pi_0` of `\phi(\pi_K)`, up to precision `t`.

        Here `\phi:K\to L` is this embedding, `\alpha\in K_0` is the generator of
        the number field underlying the domain `K` and `\alpha_0\in L_0` is an
        element of the number field `L_0` underlying the codomain `L`, such that

        .. MATH::

            v_L(\alpha_0-\phi(\alpha)) > t.

        If `t` is not given, then the approximation of used for the
        previous call of this method is returned. It is guaranteed to determine
        the embedding uniquely.

        """
        if t is None or t <= self.precision():
            return self._approximate_generator
        L = self.codomain()
        v_L = L.valuation()
        alpha = self._approximate_generator
        f = self._equation
        fx = self._derivative
        f_alpha = f(alpha)
        f_x_alpha = fx(alpha)
        s = v_L(f_alpha) - v_L(f_x_alpha)
        while s <= t:
            alpha = L.approximation(alpha - f_alpha/f_x_alpha, (t+1).ceil())
            f_alpha = f(alpha)
            f_x_alpha = fx(alpha)
            s = v_L(f_alpha) - v_L(f_x_alpha)
        self._approximate_generator = alpha
        self._precision = s
        return alpha

    def approximate_integral_basis(self, s):
        r""" Return an approximation of the standard integral basis of the domain.

        """
        if hasattr(self, "_approximate_integral_basis") and self.precision() >= s:
            return self._approximate_integral_basis
        K = self.domain()
        int_basis_K = K.integral_basis()
        approx_int_basis = [self.approximate_evaluation(a, s, polynomial=True)
                            for a in int_basis_K]
        self._approximate_integral_basis = approx_int_basis
        return approx_int_basis

    def approximate_evaluation(self, alpha, s, polynomial=False):
        r""" Return an approximation of this embedding on an element.

        INPUT:

        - ``alpha`` -- an element of the number field `K_0`approximating the domain `K`
        - ``s`` -- a positive rational number

        OUTPUT:

        an approximation `\alpha_0` of the image of `\alpha under this embedding
        `\phi:K\to L`, with the guaranteed precision `s`. This means that

        .. MATH::

            v_L(\alpha_0 - \phi(\alpha)) > s.

        """
        K = self.domain()
        L = self.codomain()
        N = s.ceil()
        assert alpha in K.number_field(), "alpha must be an element of the underlying number field of the domain"
        if alpha.is_rational():
            return L.number_field()(alpha)
        alpha = K.number_field()(alpha)
        assert K.valuation()(alpha) >= 0, "alpha must be integral"
        if polynomial:
            f = alpha.polynomial()
            pi0 = self.approximate_generator(s)
            return L.approximation(f(pi0), N)
        else:
            # we evaluate via the integral basis
            # first we write alpha as a LK of the integral basis
            u = K.vector(alpha)
            # u should be a vector with integral coefficients
            approx_int_basis = self.approximate_integral_basis(s)
            return sum(u[i]*approx_int_basis[i] for i in range(len(approx_int_basis)))

    def approximate_polynomial(self, f, s):
        r""" Return an approximation of the image of a polynomial under this embedding.

        INPUT:

        - ``f`` -- a polynomial in `K_0[x]`
        - ``s`` -- a positive rational number

        Here `K_0` is the number field underlying the domain of this embedding.

        OUTPUT: a polynomial `f_0 \in L_0[x]`, where `L_0` is the number field
        underlying the codomain of this embedding `\phi:K\to L`, such that

        .. MATH::

            v_L(f_0-\phi(f)) > s.

        """
        R_K = f.parent()
        assert R_K.base_ring() == self.domain().number_field()
        L0 = self.codomain().number_field()
        return f.map_coefficients(lambda c: self.approximate_evaluation(c, s), L0)
