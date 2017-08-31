r"""
Fake `p`-adic embeddings
========================

Let `K` and `L` be `p`-adic number fields. In this module we define a class
``FakepAdicEmbedding`` whose objects represent embeddings `\phi:K\to L` over
`\mathbb{Q}_p`.

Here the `p`-adic number fields `K` and `L` are objects of the
class ``FakepAdicCompletion``. This means that `K` and `L` represented as pairs
`(K_0,v_K)` and `(L_0,v_L)`, where e.g. `K_0` is a number field and `v_K` a
`p`-adic valuation on `K_0` such that `K` is the completion of `K_0` at `v_K`.
In fact, we do not work with actual `p`-adic numbers.

Given an embedding `\phi:K\to L`, there need not exist any embedding `K_0\to L_0`
of the underlying number fields. Therefore, the embedding `\phi` has to be
construced in a rather indirect way. Recall that `K_0` and `L_0` are absolute
number fields generated by prime elements `\pi_K` and `\pi_L` over `\mathbb{Q}`
(with respect to `v_K` and `v_L`). So an embedding `\phi:K\to L` is uniquely
determined by a root of the absolute minimal polynomial `P_K` of `\pi_K` over
`\mathbb{Q}` in `L`. Such a root may be represented by a limit pseudo valuation
`v` on the polynomial ring `L_0[x]` with `v(P_K)=\infty`.




AUTHORS:

- Stefan Wewers (2017-08-30): initial version


EXAMPLES:



TO DO:


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
from sage.rings.integer_ring import IntegerRing
from sage.rings.rational_field import RationalField
from sage.rings.number_field.number_field import NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.infinity import Infinity
from mac_lane import *
from mclf.padic_extensions.fake_padic_completions import FakepAdicCompletion


ZZ = IntegerRing()
QQ = RationalField()



class FakepAdicEmbedding(SageObject):
    r"""
    Return an embedding of two `p`-adic number fields.

    INPUT:

    - ``K``, ``L`` -- two `p`-adic number fields, given as objects of
      ``FakepAdicCompletion``
    - ``approximation`` - an approximation of the desired emdding, or ``None``
      (default: ``None``)

    OUTPUT: an embedding of `K` into `L` which is approximated by ``approximation``,
    or ``None`` if no such embedding exists.

    WARNING: to return ``None`` doesn't make sense, because __init__ returns
    an instance of ``FakepAdicEmbedding``.

    Internally, the embedding `\phi` is represented by a limit pseudo valuation
    `v` on `L_0[x]` such that `v(P_K)=\infty`. Here `K_0` and `L_0` are the
    algebraic number fields underlying `K` and `L` and `P_K` is the minimal
    valuation of the canonical generator of `K_0` over `\mathbb{Q}`.

    An *approximation* of `\phi` is any discrete valuation `v_0` on `L_0[x]`
    which approximates `v`. This may actually be `v` itself.

    Note that the resulting embedding may not be unique, in which case an
    arbitrary embedding is chosen.

    """
    def __init__(self, K, L, approximation=None):
        if isinstance(approximation, MacLaneLimitValuation):
            # v = apprximation determines phi uniquely
            v = approximation
            assert v(K.polynomial()) == Infinity
        else:
            if approximation == None:
                R = PolynomialRing(L.number_field(), 'x')
                v0 = GaussValuation(R, L.valuation())
            else:
                v0 = approximation
            # now we have to find a limit valuation v such that v(P_K)=infinity
            # which is approximated by v0
            P = K.polynomial()
            V = [v0]
            done = False
            while len(V) > 0 and not done > 0:
                V_new = []
                for v in V:
                    if v.phi().degree() == 1:
                        if v.effective_degree(P) == 1:
                            V_new = [v]
                            done = True
                            break
                        else:
                            V_new += v.mac_lane_step(P)
                V = V_new
            if len(V) == 0:
                raise AssertionError("no embedding exists")
            else:
                v = V[0]
        # now v is an approximation of an irreducible factor of P of degree 1
        v = LimitValuation(v, P)
        self._domain = K
        self._target = L
        self._limit_valuation = v


    def __repr__(self):
        return "an embedding of %s into %s"%(self._domain, self._target)


    def domain(self):
        return self._domain


    def target(self):
        return self._target


    def limit_valuation(self):
        return self._limit_valuation


    def precompose_with(self, psi):
        pass


    def postcompose_with(self, psi):
        pass


    def eval(self, alpha, precision=2):
        r"""
        Evaluate this embedding on an element of this domain, or on a polynomial.

        INPUT:

        - ``alpha`` -- an element of the domain of this embedding, or a polynomial
          over the underlying number field of the domain
        - ``precision`` -- a positive integer, or None (default: ``None``)

        OUTPUT:

        the image of ``alpha`` under this embedding `\phi:K\to L`, with the
        guaranteed precision ``precision``.

        The element `\alpha` of `K` may be given as an element of the number
        field `K_0` underlying `K`. In this case the image `\phi(\alpha)`
        will be given as an element of the number field `L_0` underlying `L`,
        which is an approximation of the true value of `\phi(\alpha)` modulo `p^N`,
        where `N` is the guaranteed precision. If ``precision`` is given then
        `N` is larger or equal to ``precision``. Otherwise the internal precision
        of `\phi` is used (which only guarantees that `\phi` is uniquely determined).

        The element `alpha` in `K` may also be given by a ...

        """

        pass


    def improve_approximation(self, N=None):
        r"""
        Improve the underlying approximation of this embedding.

        INPUT:

        - ``N`` -- a positive integer, or ``None`` (default: ``None``)

        The effect of this method is that the underlying approximation of the
        limit valuation representing this embedding is improved. If ``N``
        is given then this improvement will guarantee that for any integral
        element `\alpha` of the number field `K_0` underlying the domain `K`
        of this embedding, the value of ``self.eval(alpha)`` will agree with
        the true value `\phi(\alpha)` modulo `p^N`.

        """
        pass
