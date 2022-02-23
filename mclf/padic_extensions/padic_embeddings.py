# -*- coding: utf-8 -*-
r"""
Embeddings of `p`-adic number fields
====================================

Let `K` and `L` be `p`-adic number fields. In this module we define a class
``pAdicEmbedding`` whose objects represent embeddings `\varphi:K\to L` over
`\mathbb{Q}_p`.

Recall that a p-adic number field `K` is represented by a pair `(K_0,v_K)`,
where `K_0` is a number field and `v_K` is a p-adic valuation on `K_0`, such
that `K` is the completion of `K_0` w.r.t. `v_K`. If `L` is another p-adic
number field, represented by `(L_0,v_L)` and `\varphi:K\to L` is an embedding,
then there is no reason a priori to expect that `\varphi(K_0)=L_0`. If this is
the case then we say that `\varphi` is an *exact embedding*.

Exact embeddings are preferable, but it is not always possible (and mostly too
expensive) to choose the underlying number fields in such a way that the
embedding we are interested in is exact. So our default is that an embedding
`\varphi:K\to L` is not exact (we then say it is an *approximate embedding*).

Recall that the number field `K_0` underlying `K` has an absolute generator
`\alpha` and is therefore completely determined by the absolute minimal
polynomial `f\in \mathbb{Q}` of `\alpha`.  In order to define an embedding
`\varphi:K\to L`, it suffices to give the image `\beta:=\varphi(\alpha)`,
where `\beta\in L` is a root of `f`. Note that `\beta` will typically not lie
in the number field `L_0` underlying `L` (otherwise, `\varphi` would be an
exact emebdding). It is therefore necessary to represent `\beta` as an
*algebraic element* of `L`, determined by its minimal polynomial
`f\in\mathbb{Q}[x]` and a sufficiently good approximation `\beta_0\in L_0`.
See :module:`Elements of p-adic number fields<mclf.padic_extensions.\
elements_of_padic_number_fields>`.



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

from sage.all import SageObject, Infinity, ZZ
from mclf.padic_extensions.padic_number_fields import pAdicNumberField
from mclf.padic_extensions.elements_of_padic_number_fields import (
    ElementOfpAdicNumberField)


class pAdicEmbedding(SageObject):
    r""" Return an embedding of two `p`-adic number fields.

    INPUT:

    - ``K``, ``L`` -- two `p`-adic number fields
    - ``alpha`` - an algebraic element of `L` which is a root of the
                  polynomial defining `K`, or a sufficiently good approximation
                  of such a root

    OUTPUT:

    the (unique) embedding of `K` into `L` which sends the canonical generator
    of `K` to  `\alpha`.

    """

    def __init__(self, K, L, alpha):
        from mclf.padic_extensions.elements_of_padic_number_fields import (
            ElementOfpAdicNumberField_algebraic)
        assert isinstance(K, pAdicNumberField), "K has to be a p-adic number field"
        assert isinstance(L, pAdicNumberField), "L has to be a p-adic number field"
        f = K.polynomial()
        if isinstance(alpha, ElementOfpAdicNumberField_algebraic):
            assert alpha.minimal_polynomial() == f, "alpha is not a root of f"
        else:
            # we assume that alpha is a sufficient approximation of a root of f
            alpha = L.algebraic_element(alpha, f)
        self._domain = K
        self._codomain = L
        self._image_of_generator = alpha

    def __repr__(self):
        return "an embedding of {} into {}".format(self.domain(), self.codomain())

    def domain(self):
        return self._domain

    def codomain(self):
        return self._codomain

    def __call__(self, a):
        return self.evaluation(a)

    def image_of_generator(self):
        return self._image_of_generator

    def degree(self):
        return ZZ(self.codomain().absolute_degree()/self.domain().absolute_degree())

    def is_isomorphism(self):
        return self.degree() == 1

    def inverse(self):
        raise NotImplementedError()

    def is_equal(self, psi):
        r""" Return whether this embedding is equal to another one.

        INPUT:

        - ``psi`` - - an embedding of `K\to L`

        Here `\phi: K\to L` is this embedding.

        OUTPUT: whether `\phi` and `\psi` are equal.

        """
        phi = self
        assert phi.domain() == psi.domain(), "phi and psi do not have the same domain"
        assert phi.codomain() == psi.codomain(), "phi and psi do not have the same codomain"
        return phi.image_of_generator().is_equal(psi.image_of_generator())

    def precision(self):
        r""" Return the precision with which this embedding has been computed
        so far.

        """
        return self.image_of_generator().precision()

    def evaluation(self, a, precision=None):
        r""" Return the value of this embedding on an element of the domain.

        INPUT:

        - ``a`` -- an element of the codomain `K` of this embedding
        - ``precision`` -- a positive rational, or ``None`` (default: ``None``)

        Here `a` may be given as an element of the number field underlying `K`,
        or as an instance of :class:`ElementOfpAdicNumberField\
        <mclf.padic_extensions.elements_of_padic_number_fields.ElementOfpAdicNumberField>`.


        OUTPUT:

        the value `\varphi(a)` of this embedding `\varphi:K\to L` on `a`.

        If a value for ``precision`` is given, we try to compute `\varphi(a)` up
        to this precision, but not further. If this is not possible (because
        the precision with which `a` is known is too small), an error is raised.

        If ``precision`` is not given, then we compute `\varphi(a)` to the
        maximal possible precision. In particular, if `a` is known exactly,
        so will be `\varphi(a)` (but note that this is because `\varphi(a)` is
        algebraic in this case, and the infinite precision may only be potential).

        To compute `\varphi(a)`, we write `a=g(\alpha)` as a polynomial in the
        canonical generator `\alpha` of `K`. Then

        .. MATH::

            \varphi(a) = g(\alpha'),

        where `\alpha'=\varphi(\alpha)\in L` is the (known) image of `\alpha`.

        """
        from mclf.padic_extensions.elements_of_padic_number_fields import (
            element_of_padic_number_field)
        K = self.domain()
        if isinstance(a, ElementOfpAdicNumberField):
            assert K.is_equal(a.parent()), "a must lie in K"
            return a.evaluate_embedding(self)
        else:
            a = element_of_padic_number_field(K, a)
            g = a.polynomial(precision)
            return self.image_of_generator().evaluate_polynomial(g, precision)

    def precompose(self, psi):
        r""" Return the precompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` - - an embedding of `p`a-dic number fields `\psi: M\to K`,
                     where `K` is the domain of this embedding `\phi`.

        OUTPUT: the composition `\phi\circ\psi`.

        """
        M = psi.domain()
        K = psi.codomain()
        phi = self
        assert phi.domain() == K
        L = phi.codomain()
        return pAdicEmbedding(M, L, phi(psi.image_of_generator()))

    def postcompose(self, psi):
        r""" Return the postcompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` - - an embedding of `p`a-dic number fields `\psi: L\to M`,
                     where `L` is the codomain of this embedding `\phi`.

        OUTPUT: the composition `\psi\circ\phi`.

        """
        return psi.precompose(self)


# --------------------------------------------------------------------------


class ExactpAdicEmbedding(pAdicEmbedding):
    r"""
    Return an embedding of two `p`- adic number fields.

    INPUT:

    - ``K``, ``L`` - - two `p`- adic number fields,
    - ``phi0`` - a morphism between the number fields underlying `K` and `L`,
                 or ``None`` (default: ``None``)

    OUTPUT: the embedding of `K` into `L` which is determined by `\phi_0`. if
    `\phi_0` does not induce and embedding of `K` into `L`, an error is raised.

    If `\phi_0` is not given, then all possible embedding between the number fields
    are tried, and the first which induces an embedding of `K` into `L` is chosen.
    If none is found, an error is raised.

    """

    def __init__(self, K, L, phi0=None):
        self._domain = K.extension_field()
        self._codomain = L.extension_field()
        K0 = K.number_field()
        L0 = L.number_field()
        if phi0 is None:
            from sage.all import Hom
            embeddings = Hom(K0, L0)
            if hasattr(embeddings, "list"):
                embeddings = embeddings.list()
            else:
                embeddings = [embeddings.an_element()]
            if len(embeddings) == 0:
                raise AssertionError("There is no embedding of {} into {}".format(K0, L0))
        else:
            assert phi0.domain() == K0
            assert phi0.codomain() == L0
            embeddings = [phi0]
        # we have to see if one of the embedding is compatible with the valuation
        for phi in embeddings:
            if L.valuation()(phi(K.uniformizer())) > 0:
                self._exact_embedding = phi
                return
        raise AssertionError("phi0 is not a continous embedding of {} into {}".format(K0, L0))

    def exact_embedding(self):
        r""" Return the embedding of number fields underlying this embedding of
        `p`- adic number fields.

        """
        return self._exact_embedding

    def __call__(self, a):
        r""" Return the image of `a` under this embedding.

        INPUT:

        - ``a`` - - an element of the number field underlying the domain of this embedding.

        OUTPUT: the image of `a` under this embedding - which lies in the number
        field underlying the codoamin.

        Note that we can evaluate this embedding * only * on elements of the
        underlying number field.
        """
        return self.exact_embedding()(a)

    def image_of_generator(self):
        return self(self.domain().generator())

    def precision(self):
        return Infinity

    def is_equal(self, psi):
        r""" Return wether this embedding is equal to another one.

        INPUT:

        - ``psi`` - - an embedding of `K\to L`

        Here `\phi: K\to L` is this emebdding.

        OUTPUT: whether `\phi` and `\psi` are equal.

        """
        from sage.geometry.newton_polygon import NewtonPolygon
        if not (self.domain() == psi.domain() and self.codomain() == psi.codomain()):
            return False
        if isinstance(psi, ExactpAdicEmbedding):
            return self.exact_embedding() == psi.exact_embedding()
        else:
            v_L = self.codomain().valuation()
            v_K = self.domain().valuation()
            f = self.domain().polynomial()
            alpha = self.domain().generator()
            # we have f(alpha)=0
            # test whether the approximate generator of psi is closer to alpha
            # than any other root of the minimal polynomial
            alpha_0 = psi.approximate_generator()
            F = f(f.parent().gen() + alpha)
            np = NewtonPolygon([(i, v_K(F[i])) for i in range(f.degree()+1)])
            return v_L(f(alpha_0)) > np(1) + np.slopes()[0]

    def precompose(self, psi):
        r""" Return the precompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` - - an embedding of `p`a-dic number fields `\psi: M\to K`,
                     where `K` is the domain of this embedding `\phi`.

        OUTPUT: the composition `\phi\circ\psi`.

        """
        phi = self
        if isinstance(psi, ExactpAdicEmbedding):
            composition = self.exact_embedding().precompose(psi.exact_embedding())
            return ExactpAdicEmbedding(psi.domain(), phi.codomain(), composition)
        elif isinstance(psi, pAdicEmbedding):
            alpha = phi(psi.approximate_generator())
            return pAdicEmbedding(psi.domain(), phi.codomain(), alpha)
        else:
            raise ValueError("psi has to be an exact or an approximate embedding")

    def postcompose(self, psi):
        r""" Return the postcompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` - - an embedding of `p`a-dic number fields `\psi: L\to M`,
                     where `L` is the codomain of this embedding `\phi`.

        OUTPUT: the composition `\psi\circ\phi`.

        """
        return psi.precompose(self)

    def approximate_evaluation(self, alpha, s=None, polynomial=False):
        r""" Return an approximation of this embedding on an element.

        INPUT:

        - ``alpha`` - - an element of the number field `K_0`approximating the domain `K`
        - ``s`` - - a positive rational number

        OUTPUT:

        an approximation `\alpha_0` of the image of `\alpha under this embedding
        `\phi: K\to L`, with the guaranteed precision `s`. This means that

        .. MATH::

            v_L(\alpha_0 - \phi(\alpha)) > s.

        """
        return self.codomain().approximation(self(alpha), s.ceil())
