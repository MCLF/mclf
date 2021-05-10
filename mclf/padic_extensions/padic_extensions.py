# -*- coding: utf-8 -*-
r"""
Extension of `p`-adic number fields
===================================


In this module we define a class ``pAdicExtension``, which realizes a finite
extension `L/K` of `p`-adic number fields. Both fields `K` and `L` are realized
as objects in the class :class:`pAdicNumberField`, the embedding `K\to L` as
an object of ``pAdicEmbedding``.

The class :class:`pAdicExtension` is actually a subclass of
:class:`pAdicNumberField`, emphazising the point of view that we may regard
an extension `L/K` as an *absolute* `p`-adic number field, or as a *relative*
`p`-adic number field with base field `K`.

AUTHORS:

- Stefan Wewers (2021-05-9): initial version


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

from sage.all import ZZ
from mclf.padic_extensions.padic_number_fields import pAdicNumberField
from mclf.padic_extensions.p_adic_embeddings import ExactpAdicEmbedding, ApproximatepAdicEmbedding


class pAdicExtension(pAdicNumberField):
    r"""
    Return the extension of `p`-adic number fields corresponding to an embedding.

    INPUT:

    - ``phi`` -- an embedding of `p`-adic number fields

    OUTPUT:  the extension `L/K` where `K` is the domain and `L` the codomain of `phi`

    """

    def __init__(self, phi):

        K = phi.domain()
        L = phi.codomain()

        # first we initialize L as an absolute p-adic number field
        super().__init__(L.number_field(), L.valuation())

        # now we initialize L/K as relative p-adic number field
        self._embedding = phi
        self._base_field = K
        self._extension_field = L
        self._relative_ramification_degree = ZZ(L.absolute_ramification_degree()/K.absolute_ramification_degree())
        self._relative_degree = ZZ(L.absolute_degree()/K.absolute_degree())
        self._relative_inertia_degree = ZZ(L.absolute_inertia_degree()/K.absolute_inertia_degree())
        assert self._relative_degree == self._relative_ramification_degree * self._relative_inertia_degree

    def __repr__(self):
        return "{}, as extension of {}".format(self._extension_field, self._base_field)

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

    def embedding(self):
        return self._embedding

    def relative_degree(self):
        """ Return the degree of the extension."""
        return self._relative_degree

    def relative_ramification_degree(self):
        """ Return the ramification degree of the extension."""
        return self._relative_ramification_degree

    def relative_inertia_degree(self):
        """ Return the inertia degree of the extension."""
        return self._relative_inertia_degree

    def relative_polynomial(self):
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
        raise NotImplementedError()

        # I am not sure this is what we need
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
                # this seems to be wrong!!
                return self._polynomial()

            # the following computation may be quite expensive
            # it would be better to have an approximation of P already
            # when this extension is created.
            factor_list = K.approximate_factorization(L.polynomial(), only_ramified_factors=True)
            P_list = [g for g, e in factor_list if g.degree() == n]
            assert len(P_list) > 0, "strange: no factor of the degree of L/K found"
            self._polynomial = P_list[0]
        return self._polynomial

    def superextension(self, M):
        r""" Return the composition of this extension with a superextension.

        INPUT:

        - ``M`` -- a finite extension of the extension field `L` of this
                   extension `L/K`

        OUTPUT: the composite extension `M/K`.

        """
        raise NotImplementedError()

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

        .. NOTE::

            I should completely review this concept, and develop better methods
            to determined suextensions.

        """
        raise NotImplementedError()


class ExactpAdicExtension(pAdicExtension):
    r""" An object representing a finite extension `L/K` of `p`-adic number
    fields, determined by an *exact* embedding of the number field `K_0`
    underlying `K` into the number field `L_0` underlying `L`.

    INPUT:

    - ``phi`` -- an exact embedding of `p`-adic number fields

    OUTPUT:  the extension `L/K` where `K` is the domain and `L` the codomain
    of `phi`.

    `\phi` has to be an object of :class:`ExactpAdicEmbedding`.


    """

    def __init__(self, phi):
        assert isinstance(phi, ExactpAdicEmbedding), "phi has to be an exact embedding"
        super().__init__(phi)

    def relative_minpoly(self, a):
        raise NotImplementedError()

    def relative_polynomial(self):
        raise NotImplementedError()


class ApproximatepAdicExtension(pAdicExtension):
    r""" An object representing a finite extension `L/K` of `p`-adic number
    fields, determined by an *approximate* embedding of `K` into `L`.

    INPUT:

    - ``phi`` -- an approximate embedding of `p`-adic number fields

    OUTPUT:  the extension `L/K` where `K` is the domain and `L` the codomain
    of `phi`.

    `\phi` has to be an object of :class:`ApproximatepAdicEmbedding`.


    """

    def __init__(self, phi):
        assert isinstance(phi, ApproximatepAdicEmbedding), "phi has to be an approximate embedding"
        super().__init__(phi)

    def relative_minpoly(self, a):
        raise NotImplementedError()

    def relative_polynomial(self):
        raise NotImplementedError()

    def exact_extension(self, isomorphism=False):
        r""" Return an isomorphic, and exact extension.

        INPUT:

        - ``isomorphism`` -- a boolean (default=``False``)

        As this is an approximate extension `L/K`, we return an exact extension
        `L'/K`, where `L'` and `L` are `K`-isomorphic.

        If ``isomorphism`` is true, we return the pair `(L'/K, \phi)`, where
        `\phi:L\to L'` is an (approximate) `K`-isomorphism.

        """
        from mclf.padic_extensions.approximate_factorization import approximate_factorization
        if isomorphism:
            raise NotImplementedError("Computation of isomorphism not yet implemented")
        K = self.base_field()
        L = self.extension_field()
        d = self.relative_degree()
        f = L.absolute_polynomial()
        factors = approximate_factorization(K, f)
        factors = [g for g in factors if g.degree() == d]
        assert len(factors) > 0, "something is wrong!"
        g = factors[0]
        return K.simple_extension(g, exact_extension=True)
