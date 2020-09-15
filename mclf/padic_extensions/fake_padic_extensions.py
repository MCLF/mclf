# -*- coding: utf-8 -*-
r"""
Fake `p`-adic extensions
========================

Let `K` be a `p`-adic number field. For our project we need to be able to
compute with Galois extensions `L/K` of large degree.

At the moment, computations with general extensions of `p`-adic fields of large
degree are still problematic. In particular, it seems difficult to obtain results
which are provably correct. For this reason we do not work which `p`-adic numbers at all.
Instead, we use our own class ``FakepAdicCompletion``, in which a `p`-adic number
field is approximated by a pair `(K_0, v_K)`, where `K_0` is a suitable number field
and `v_K` is a `p`-adic valuation on `K_0` such that `K` is the completion
of `K_0` at `v_K`.

In this module we define a class ``FakepAdicExtension``, which realizes a finite
extension `L/K` of `p`-adic number fields. Both fields `K` and `L` are realized
as objects in the class ``FakepAdicCompletion``, the embedding `K\to L` as
an object of ``FakepAdicEmbedding``.


AUTHORS:

- Stefan Wewers (2017-08-30): initial version


EXAMPLES:



TO DO:

- the method ``polynomial`` should give an *exact* result, namely a object of
  some class ``FakepAdicPolynomial``


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

from sage.all import SageObject, ZZ


class FakepAdicExtension(SageObject):
    r"""
    Return the extension of `p`-adic number fields corresponding to an embedding.

    INPUT:

    - ``phi`` -- an embedding of `p`-adic number fields

    OUTPUT:  the extension `L/K` where `K` is the domain and `L` the target of `phi`

    """
    def __init__(self, phi):

        K = phi.domain()
        L = phi.target()
        self._base_field = K
        self._extension_field = L
        self._ramification_degree = ZZ(L.absolute_ramification_degree()/K.absolute_ramification_degree())
        self._degree = ZZ(L.absolute_degree()/K.absolute_degree())
        self._inertia_degree = ZZ(L.absolute_inertia_degree()/K.absolute_inertia_degree())
        assert self._degree == self._ramification_degree * self._inertia_degree


    def __repr__(self):
        return "%s as extension over %s"%(self._extension_field, self._base_field)


    def p(self):
        """
        Return the prime `p`.
        """
        return self.base_field().p()


    def base_field(self):
        """
        Return the base field.
        """
        return self._base_field


    def extension_field(self):
        """
        Return the extension field.
        """
        return self._extension_field


    def valuation(self):
        """ Return the valuation of the extension."""
        return self._extension_field.valuation()


    def normalized_valuation(self):
        """ Return the normalized valuation."""
        return self._extension_field.normalized_valuation()


    def degree(self):
        """ Return the degree of the extension."""
        return self._degree


    def ramification_degree(self):
        """ Return the ramification degree of the extension."""
        return self._ramification_degree


    def inertia_degree(self):
        """ Return the inertia degree of the extension."""
        return self._inertia_degree


    def polynomial(self):
        r"""
        Return the minimal polynomial of a generator of this extension.

        OUTPUT:

        A monic, integral and irreducible polynomial `P` over the number field
        underlying the base field of this extension.

        Let `L/K` be our extension of `p`-adic number fields. Then `P` is a
        monic polynomial over the number field `K_0` underlying `K`, of degree
        `[L:K]`, with the following properties:

        - `P` is integral and irreducible over `K`
        - `P` is the minimal polynomial of a prime element `\pi` of `L` such
          that `L = K[\pi]`.

        Note, however, that `\pi` is in general not equal to the canonical absolute
        generator `\pi_L` of `L/\mathbb{Q}_p`. Moreover, in general no root of `P`
        is contained in the number field `L_0` underlying `L`.

        TODO:

        `P` should be naturally equipped with

        """
        if not hasattr(self, "_polynomial"):
            K = self.base_field()
            L = self.extension_field()
            n = self.degree()
            if K.is_Qp():
                self._polynomial = L.polynomial()
                return self._polynomial()
            if n == 1:
                x = L.polynomial().parent().gen()
                self._polynomial = x - self.p()
                return self._polynomial()

            # the following computation may be quite expensive
            # it would be better to have an approximation of P already
            # when this extension is created.
            factor_list = K.approximate_factorization(L.polynomial(), only_ramified_factors=True)
            P_list = [g for g, e in factor_list if g.degree() == n]
            assert len(P_list) > 0, "strange: no factor of the degree of L/K found"
            self._polynomial = P_list[0]
        return self._polynomial


    def subextension(self, alpha, d):
        r"""
        Return a subextension of given degree, containing (approximately) a given element.

        INPUT:

        - ``alpha`` -- an (approximate) element of this extension field
        - ``d`` -- a positive integer

        OUTPUT:

        a subextension of degree `d` which (approximately) contains ``alpha``,
        or ``None`` if no such subextension exists.

        Let `L/K` be the given extension of `p`-adic number fields. Then we are
        looking for a subextension `K \subset M \subset L` such that
        `[M:K] = d`. If `\alpha` is given exactly, then we demand that `\alpha\in M`.
        If `\alpha` is given by an approximation `(\alpha_0,N)` then we demand
        that there exists an element `\alpha_1\in M` such that

        .. MATH::

                v_M(\alpha_1-\alpha_0) \geq N`.

        Here the valuation `v_M` is normalized such that `v_M(p)=1`.

        """
        pass
