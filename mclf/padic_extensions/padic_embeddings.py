# -*- coding: utf-8 -*-
r"""
Embeddings of `p`-adic number fields
====================================

Let `K` and `L` be `p`-adic number fields. In this module we define a class
``pAdicEmbedding`` whose objects represent embeddings `\varphi:K\to L` over
`\mathbb{Q}_p`.

There are two kinds of embeddings. The first ist called *exact*, meaning that
`\varphi` is induced from an embedding of the underlying number fields. If this
is not the case then the embedding is called *approximate*.

Recall that a p-adic number field `K` is represented by a pair `(K_0,v_K)`,
where `K_0` is a number field and `v_K` is a p-adic valuation on `K_0`, such
that `K` is the completion of `K_0` w.r.t. `v_K`. If `L` is another p-adic
number field, represented by `(L_0,v_L)` and `\varphi:K\to L` is an embedding,
then there is no reason a priori to expect that `\varphi(K_0)=L_0` (which means
that `\varph` is exact).



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

from sage.all import SageObject, Infinity, QQ, ZZ
from mclf.padic_extensions.padic_number_fields import pAdicNumberField
from mclf.padic_extensions.elements_of_padic_number_fields import (
    ElementOfpAdicNumberField)


class pAdicEmbedding(SageObject):
    r""" Return an embedding of two `p`-adic number fields.

    INPUT:

    - ``K``, ``L`` -- two `p`-adic number fields
    - ``alpha`` - an algebraic element of `L` which is a root of the
                  polynomial defining `K`

    OUTPUT:

    the (unique) embedding of `K` into `L` which sends the canonical generator
    of `K` to  `\alpha`.

    Here `\alpha` may be given as an element of the number field underlying `L`.
    In this case, the resulting embedding `\varphi:K\to L` is called *exact*,
    as it is induced from an embedding of the underlying number fields of `K`
    and `L`.

    Otherwise, `\alpha` must be an instance of the class
    :class:`ElementOfpAdicNumberField_algebraic<mclf.padic_extensions.\
    elements_of_padic_number_fields.ElementOfpAdicNumberField_algebraic>`.

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
            # it is still problematic to use == to test equality of p-adic
            # number fields, because they may or may not be "extensions"
            # assert a.parent() == K, "a must lie in K"
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

#   we should not need this anymore:

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
        if isinstance(psi, ApproximatepAdicEmbedding):
            alpha = phi(psi.approximate_generator())
            return ApproximatepAdicEmbedding(psi.domain(), phi.codomain(), alpha)
        elif isinstance(psi, ExactpAdicEmbedding):
            composition = self.exact_embedding().precompose(psi.exact_embedding())
            return ExactpAdicEmbedding(psi.domain(), phi.codomain(), composition)
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


class ApproximatepAdicEmbedding(pAdicEmbedding):
    r"""
    Return an(approximate) embedding of two `p`- adic number fields.

    INPUT:

    - ``K``, ``L`` - - two `p`- adic number fields
    - ``alpha_0`` - an approximation of the image of the generator of the domain.

    OUTPUT: the embedding of `K` into `L` which is determined by `\alpha_0`.

    The element `\alpha_0\in L_0` of the number field underlying `L` is assumed
    to be an * approximate root * of the minimal polynomial `f\in \mathbb{Q}[x]` of
    the standard generator of `K /\mathbb{Q}_p`. Here 'approximate root' means
    that the pair `(f, \alpha_0)` satisfies the condition of Hensel's Lemma,
    which guarantees that there exists a unique root `\alpha\in L` of `f`
    strictly closer to `\alpha_0` than any other root. The associated embedding
    is then the map

    .. MATH::

        \phi: K\cong \mathbb{Q}[x]/(f) \to L, \quad x \mapsto \alpha.

    Note that the embedding `\phi` does in general not restrict to a map between
    the underlying number fields, `K_0\to L_0`. Therefore, we cannot compute
    `\phi` exactly, but only approximately. Hensel's Lemma guarantees that
    the root `\alpha` approximated by `\alpha_0` is unique, and that the
    approximation `\alpha_0` can be improved to arbitrary precision via the
    `p`- adic Newton method. This allows us to approximate the map `\phi` up to
    arbitrary precison.

    """

    def __init__(self, K, L, alpha_0):
        L_0 = L.number_field()
        v_L = L.valuation()
        alpha_0 = L_0(alpha_0)
        assert v_L(alpha_0) >= 0
        f = K.polynomial()
        alpha_0 = L.approximate_root(f, alpha_0, K.required_precision())
        self._domain = K.extension_field()
        self._codomain = L.extension_field()
        self._approximate_generator = alpha_0
        self._equation = f
        # I don't understand this choice anymore; it seems to work though
        self._precision = K.required_precision()

    def precompose(self, psi):
        r""" Return the precompositon of this embedding with the embedding `\psi`.

        INPUT:

        - ``psi`` - - an embedding of `p`a-dic number fields `\psi: M\to K`,
                     where `K` is the domain of this embedding `\phi`.

        OUTPUT: the composition `\phi\circ\psi`.

        """
        phi = self
        if isinstance(psi, ApproximatepAdicEmbedding):
            # I have to think harder how to set the precision; this is just
            # a first try:
            s = min(phi.precision(), psi.precision())
            if s == Infinity:
                s = QQ(10)
            while True:
                try:
                    alpha = phi.approximate_evaluation(psi.approximate_generator(s), s)
                    return ApproximatepAdicEmbedding(psi.domain(), phi.codomain(), alpha)
                except AssertionError:
                    s += 2
        elif isinstance(psi, ExactpAdicEmbedding):
            alpha = psi(psi.domain().generator())
            alpha = phi.approximate_evaluation(alpha)
            return ApproximatepAdicEmbedding(psi.domain(), phi.codomain(), alpha)
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

    def precision(self):
        return self._precision

    def is_equal(self, psi):
        r""" Return wether this embedding is equal to another one.

        INPUT:

        - ``psi`` - - an embedding of `K\to L`

        Here `\phi: K\to L` is this emebdding.

        OUTPUT: whether `\phi` and `\psi` are equal.

        """
        from sage.geometry.newton_polygon import NewtonPolygon
        if isinstance(psi, ExactpAdicEmbedding):
            return psi.is_equal(self)
        phi = self
        # now phi and psi are both approximate
        if not (phi.domain() == psi.domain() and phi.codomain() == psi.codomain()):
            return False
        if phi.domain().is_Qp():
            # there is only one embedding of QQ_p into a p-adic number field
            return True
        v_L = phi.codomain().valuation()
        alpha_1 = phi.approximate_generator()
        alpha_2 = psi.approximate_generator()
        f = phi.domain().polynomial()
        # we know that both alpha_1 and alpha_2 are closer to some root of f
        # then any other root. We have to check whether alpha_1 and alpha_2
        # belong to the same root
        F = f(f.parent().gen() + alpha_1)
        np = NewtonPolygon((i, v_L(F[i])) for i in range(1, f.degree()+1))
        # the slopes of np are - the valuation of alpha_1-other roots of f
        return v_L(alpha_1-alpha_2) > -np.slopes()[0]

    def approximate_generator(self, t=None):
        r""" Return an approximation of the image of the generator of the domain.

        INPUT:

        - ``t`` - - a positive rational number, or ``None`` (default: ``None``)

        OUTPUT: an approximation `\pi_0` of `\phi(\pi_K)`, up to precision `t`.

        Here `\phi: K\to L` is this embedding, `\alpha\in K_0` is the generator of
        the number field underlying the domain `K` and `\alpha_0\in L_0` is an
        element of the number field `L_0` underlying the codomain `L`, such that

        .. MATH::

            v_L(\alpha_0 -\phi(\alpha)) > t.

        If `t` is not given, then the approximation of used for the
        previous call of this method is returned. It is guaranteed to determine
        the embedding uniquely.

        """
        if t is None or t <= self.precision():
            return self._approximate_generator
        L = self.codomain()
        alpha = self._approximate_generator
        f = self._equation
        alpha = L.approximate_root(f, alpha, t)
        self._approximate_generator = alpha
        self._precision = t
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

    def approximate_evaluation(self, alpha, s=None):
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
        K = self.domain()
        L = self.codomain()
        if s is None:
            s = self.precision()
        # Attention! this is preliminary:
        if s == Infinity:
            s = QQ(10)
        N = QQ(s).ceil()
        assert alpha in K.number_field(), "alpha must be an element of the underlying number field of the domain"
        if alpha.is_rational():
            return L.number_field()(alpha)
        alpha = K.number_field()(alpha)
        assert K.valuation()(alpha) >= 0, "alpha must be integral"
        f = alpha.polynomial()
        pi0 = self.approximate_generator(s)
        return L.approximation(f(pi0), N)


# ---------------------------------------------------------------------------

#                     helper functions
