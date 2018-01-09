r"""
Weak p-adic Galois extensions
=============================

Let `K` be a `p`-adic number field. For our project we need to be able to
compute with Galois extensions `L/K` of large ramification degree.
For instance, we need to be able to compute the breaks of the ramification
filtration of the Galois group of `L/K`, as well as the corresponding
subfields.

At the moment, computations with large Galois extensions of `p`-adic fields are
still problematic. In particular, it seems difficult to obtain results which are
provably correct. For this reason we do not work which `p`-adic numbers at all.
Instead, we use our own class ``FakepAdicCompletion``, in which a `p`-adic number
field is approximated by a pair `(K_0, v_K)`, where `K_0` is a suitable number field
and `v_K` is a `p`-adic valuation on `K_0` such that `K` is the completion
of `K_0` at `v_K`.

Let `L/K` be a finite field extension. We say that `L/K` is a **weak Galois
extension** if the induced extension  `L^{nr}/K^{nr}` is Galois. Given a
polynomial `f` in `K[x]`, we say that `L/K` is a **weak splitting field** for `f`
if `f` splits over `L^{nr}`.

Given a weak Galois extension `L/K`, we have canonical isomorphisms between the
following groups:

- the Galois group of `L^{nr}/K^{nr}`,
- the inertia subgroup of the Galois closure of `L/K`,

Moreover, this isomorphism respects the filtrations by higher ramification
groups.

If `L/K` is totally ramified then the degree of `L/K` is equal to the degree
of `L^{nr}/K^{nr}`, which is equal to the order of the inertia subgroup of the
Galois closure of `L/K`. Therefore, our approach allows us to fully
understand the inertia group of a Galois extension of `p`-adic fields, while
keeping the degree of the field extensions with which one works as small as
possible.

Our method can also be used to work with approximations of the subfields
of a `p`-adic Galois extension corresponding to the higher ramification
subgroups.

For `u\geq 0` we let `L^{sh,u}` denote the subfield of `L^{sh}/K^{sh}`
corresponding to the `u`th filtration step of the Galois group of
`L^{sh}/K^{sh}`. Then the completion of `L^{sh,u}` agrees with the maximal
unramified extension of the subextension `\hat{L}^u` of the Galois closure
`\hat{L}/\hat{K}` corresponding to the `u`th ramification step. Moreover,
there exists a finite extensions `L^u/K`, together with an extension `v_{L^u}`
of `v_K` to `L^u` such that

- the strict henselization of `(L^u, v_{L^u})` is isomorphic to `L^{sh,u}`,
- the completion of `(L^u, v_{L^u})` agrees with `\hat{L}^u`, up to a finite
  unramified extension.

Note that `L^u` will in general not be a subfield of `L` (and not even of the
Galois closure of `L/K`).


In this module we define a class ``WeakPadicGaloisExtension``, which realizes an
approximation of a `p`-adic Galois extension, up to unramified extensions.


AUTHORS:

- Stefan Wewers (2017-08-06): initial version


EXAMPLES:

This example is from the "Database of Local Fields":  ::

    sage: K = QQ
    sage: v_3 = pAdicValuation(K, 3)
    sage: R.<x> = K[]
    sage: f = x^6+6*x^4+6*x^3+18
    sage: L = WeakPadicGaloisExtension(v_3, f)
    sage: L.upper_jumps()
    [0, 1/2]


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
from sage.rings.number_field.number_field import NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.integer_ring import IntegerRing
from sage.rings.rational_field import RationalField
from sage.rings.finite_rings.integer_mod import mod
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import Infinity
from sage.functions.generalized import sgn
from sage.functions.other import ceil
from sage.misc.prandom import randint
from sage.geometry.newton_polygon import NewtonPolygon
from sage.misc.misc_c import prod
from sage.arith.misc import lcm
from mac_lane import *
from mclf.padic_extensions.fake_padic_completions import FakepAdicCompletion
from mclf.padic_extensions.fake_padic_extensions import FakepAdicExtension

ZZ = IntegerRing()
QQ = RationalField()


class WeakPadicGaloisExtension(FakepAdicExtension):
    r"""
    Return the weak p-adic splitting field of a polynomial.

    INPUT:

    - ``K`` -- a `p`-adic number field
    - ``F`` -- a polynomial over the number field underlying `K`, or a list of
      such polynomials
    - ``minimal_ramification`` -- a positive integer (default: ``1``)

    OUTPUT: the extension `L/K`, where `L` is a weak splitting field of ``F``
    whose ramification index over `K` is a multiple of ``minimal_ramification``.

    NOTE:

    For the time being, ``F`` has to be defined oover `\mathbb{Q}`,
    and ``minimal ramification`` has to be prime to `p`.

    """
    def __init__(self, K, F, minimal_ramification=ZZ(1)):

        # print "entering WeakPadicGaloisExtension with"
        # print "F = %s"%F
        # if F is a polynomial, replace it by the list of its irreducible factors
        # if isinstance(F, Polynomial):
        #     F = [f for f, m in F.factor()]
        assert K.is_Qp(), "for the moment, K has to be Q_p"
        # assert not K.p().divides(minimal_ramification), "minimal_ramification has to be prime to p"
        if not isinstance(F, Polynomial):
            if F == []:
                F = PolynomialRing(K.number_field(),'x')(1)
            else:
                F = prod(F)
        self._base_field = K
        L = K.weak_splitting_field(F)
        e = ZZ(L.absolute_ramification_degree()/K.absolute_ramification_degree())
        if not minimal_ramification.divides(e):
                        # enlarge the absolute ramification index of vL
                        # such that minimal_ramification divides e(vL/vK):
            m = ZZ(minimal_ramification/e.gcd(minimal_ramification))
            # assert not self.p().divides(m), "p = %s, m = %s, e = %s,\nminimal_ramification = %s"%(self.p(), m, e, minimal_ramification)
            L = L.ramified_extension(m)
            # if m was not prime to p, L/K may not be weak Galois anymore
        else:
            m = ZZ(1)
        self._extension_field = L
        self._ramification_degree = e*m
        self._degree = ZZ(L.absolute_degree()/K.absolute_degree())
        self._inertia_degree = ZZ(L.absolute_inertia_degree()/K.absolute_inertia_degree())
        assert self._degree == self._ramification_degree * self._inertia_degree


    def __repr__(self):
        return "%s as weak Galois extension of %s"%(self._extension_field, self._base_field)


    def ramification_filtration(self, upper_numbering=False):
        r"""
        Return the list of ramification jumps.

        INPUT:

        - ``upper_numbering`` -- a boolean (default: ``False``)

        OUTPUT: an ordered list of pairs `(u, m_u)`, where `u` is a jump in the
        filtration of higher ramification groups and `m_u` is the order of the
        corresponding subgroup. The ordering is by increasing jumps.

        If ``upper_numbering`` is ``False``, then the filtration is defined as
        follows. Let `L/K` be a Galois extension of `p`-adic number fields, with
        Galois group `G`. Let `\pi` be a prime element of `L`, and let `v_L`
        denote the normalized valuation on `L` (such that `v_L(\pi)=1`). For
        `u\geq 0`, the ramification subgroup `G_u` consists of all element
        `\sigma` of the inertia subgroup `I` of `G` such that

        .. MATH::

             v_L(\sigma(\pi) - \pi) \geq i + 1.

        In particular, `I=G_0`. An integer `u\geq 0` is called a "jump" if
        `G_{u+1}` is strictly contained in `G_u`. Note that this is equivalent
        to the condition that there exists an element `\sigma\in G` such that

        .. MATH::

            v_L(\sigma(\pi) - \pi) = u + 1.

        It follows that the ramification filtration can easily be read off from
        the Newton polygon (with respect to `v_L`) of the polynomial

        .. MATH::

            G := P(x + \pi)/x,

        where `P` is a minimal polynomial of `\pi` over `K`.  The polynomial
        `G` is called the *ramification polynomial* of the Galois extension `L/K`.

        """

        if upper_numbering:
            if hasattr(self, "_upper_jumps"):
                return self._upper_jumps
            else:
                self._compute_upper_jumps()
                return self._upper_jumps
        else:
            if hasattr(self, "_lower_jumps"):
                return self._lower_jumps
            else:
                self._compute_lower_jumps()
                return self._lower_jumps


    def lower_jumps(self):
        r"""
        Return the upper jumps of the ramification filtration of this extension.

        """
        return [u for u, m in self.ramification_filtration()]


    def upper_jumps(self):
        r"""
        Return the lower jumps of the ramification filtration of this extension.

        """
        return [u for u, m in self.ramification_filtration(upper_numbering=True)]


    def _compute_lower_jumps(self):
        """
        This method computes the lower jumps and stores them
        as ``_lower_jumps``.

        """
        if self.ramification_degree() == 1:
            self._lower_jumps = []
        else:
            NP = self.ramification_polygon()
            f = self.inertia_degree()
            # this is the Newton polygon of the ramification
            # polygon G
            jumps = []
            for v1, v2 in NP.sides():
                u = (v1[1]-v2[1])/(v2[0]-v1[0]) - 1  # jump = -slope - 1
                if u == 0:                # G does not distinguish Gamma and Gamma_0
                    m = self.ramification_degree()
                else:
                    m = v2[0] + 1
                jumps.append((u, m))
            jumps.reverse()               # increasing order for jumps
            if len(jumps) >= 2 and jumps[0][1] == jumps[1][1]:
                jumps = jumps[1:]     # u=0 is not a jump
            self._lower_jumps = jumps


    def _compute_upper_jumps(self):
        """
        This method computes the upper jumps and stores them
        as ``_upper_jumps``.

        """
        if self.lower_jumps() == []:
            self._upper_jumps = []
        else:
            jumps = self.ramification_filtration()
            m = [m_i for m_i, g_i in jumps]
            g = [g_i for m_i, g_i in jumps]
            e = self.ramification_degree()
            u = [m[0]*g[0]/e]
            for i in range(1, len(jumps)):
                u.append(u[i-1]+(m[i]-m[i-1])*g[i]/e)
            self._upper_jumps = [(u[i], g[i]) for i in range(len(jumps))]


    def ramification_polynomial(self, precision=20):
        r"""
        Return the ramification polynomial of this weak Galois extension.

        The *ramification polynomial* is the polynomial

        .. MATH::

            G := P(x+\pi)/x

        where `\pi` is a prime element of `L` which generates the extension
        `L/K` and `P` is the minimal polynomial of `\pi` over `K^{nr}`, the
        maximal unramified subextension of .

        NOTE:

        - For the time being, we have to assume that `K=\mathbb{Q}_p`. In this
          case we can choose for `\pi` the canonical generator of the absolute
          number field `L_0` underlying `L`.

        """
        if not hasattr(self, "_ramification_polynomial"):
            assert self.base_field().is_Qp(), "K has to be equal to Q_p"
            L = self.extension_field()
            pi = L.uniformizer()
            P = L.minpoly_over_unramified_subextension(precision)
            x = P.parent().gen()
            self._ramification_polynomial = P(pi+x).shift(-1)
        return self._ramification_polynomial


    def ramification_polygon(self):
        r"""
        Return the ramification polygon of this extension.

        The *ramification polygon* of a weak Galois extension `L/K`
        of `p`-adic number fields is the Newton polygon of the
        ramification polynomial, i.e. the polynomial

        .. MATH::

            G := P(x+\pi)/x

        where `\pi` is a prime element of `L` which generates the extension
        `L/K` and `P` is the minimal polynomial of `\pi` over `K^{nr}`, the
        maximal unramified subextension of .

        The (strictly negative) slopes of the ramification polygon (with respect
        to the valuation `v_L` on `L`, normalized such that `v_L(\pi_L)=1`)
        correspond to the jumps in the filtration of higher ramification groups,
        and the abscissae of the vertices of the corresponding vertices are equal
        to the order of the ramification subgroups that occur in the filtration.

        NOTE:

        - For the time being, we have to assume that `K=\mathbb{Q}_p`. In this
          case we can choose for `\pi` the canonical generator of the absolute
          number field `L_0` underlying `L`.

        """
        if not hasattr(self, "_ramification_polygon"):
            assert self.base_field().is_Qp(), "K has to be equal to Q_p"
            L = self.extension_field()
            vL = L.normalized_valuation()
            G = self.ramification_polynomial()
            self._ramification_polygon = NewtonPolygon([(i, vL(G[i])) for i in range(G.degree()+1)])
        return self._ramification_polygon


    def factors_of_ramification_polynomial(self, precision=10):
        r"""
        Return the factorization of the ramification polynomial into factors
        with fixed slope.

        OUTPUT: a dictionary ``factors`` such that `g=` ``factors[s]``
        is the maximal factor of the ramification polynomial `G` whose Newton
        polygon has a single slope `s`. We omit the factor with slope `s=-1`.

        """
        from mclf.padic_extensions.slope_factors import slope_factors

        NP = self.ramification_polygon()
        slopes = NP.slopes(False)
        G = self.ramification_polynomial()
        R = G.parent()
        L = self.extension_field()
        vL = self.valuation()
        reduce_function = lambda g: L.reduce_polynomial(g, precision + 2)
        F = slope_factors(G, vL, precision*self.ramification_degree(),
            reduce_function, slope_bound=-1)
        N = (vL(G[0]) + precision).ceil()
        F_reduced = {}
        for s in F.keys():
            g = F[s]
            g = R([L.reduce(g[i], N) for i in range(g.degree()+1)])
            F_reduced[s] = g
        return F_reduced


    def ramification_subfields(self, precision=1):
        r"""
        Return the ramification subfields of this weak Galois extension.

        The set of all subfields is returned as dictionary, in which the
        keys are the lower jumps and the values are the corresponding subfields,
        given as extension of the base field.

        """
        if hasattr(self, "_ramification_subfields"):
            return self._ramification_subfields
        L = self.extension_field()
        e = self.ramification_degree()
        v_p = L.base_valuation()
        pi = L.uniformizer()
        NP = self.ramification_polygon()
        slopes = NP.slopes(False)
        vertices = NP.vertices()
        subfields = {}
        while len(subfields.keys()) < len(slopes):
            factors = self.factors_of_ramification_polynomial(precision)
            # we compute approximate factors of G corresponding to the slopes that occur
            beta = pi
            for i in range(len(slopes)):
                s = -slopes[i]
                m = vertices[i+1][0] + 1
                k = vertices[i+1][0] - vertices[i][0]
                if s == 1:        # this slope corresponds to the inertia subgroup G_0
                                # the corresponding subfield is the max. unramified ext.
                                #  we return Q_p because unramified extensions are ignored
                    subfields[0] = FakepAdicCompletion(QQ, v_p)
                else:
                    g = factors[-s]
                    beta = beta*(-1)**k*g(-pi)
                    K_i = L.subfield(beta, ZZ(e/m))
                    if K_i != None:
                        subfields[s-1] = K_i
            precision = precision + 1
        self._ramification_subfields = subfields
        return subfields


    def ramification_subfield(self, u):
        r"""
        Return the ramification subfield corresponding to a given lower jump.

        Here a nonnegative integer `u \geq 0` is called a *lower jump* for the
        weak `p`-adic Galois extension `L/K`  if `u`is a jump in the filtration
        `(G_u)_{u\geq 0}` of the Galois group `G = Gal(L^{nr}/K^{nr})` of the
        induced extension `L^{nr}/K^{nr}`. This is equivalent to the following
        condition: there exists an element `g\in G`, such that

        .. MATH::

                v_L(g(\pi_L)-\pi_L) = u + 1.

        Here `v_L` is the valuation of the extension field `L` and `\pi_L`
        is a prime element of `L`. We normalize `v_L` such that `v_L(\pi_L)=1`.

        """
        ramification_subfields = self.ramification_subfields()
        assert u in ramification_subfields.keys(), "u is not a lower jump"
        return ramification_subfields[u]


#-----------------------------------------------------------------------------
