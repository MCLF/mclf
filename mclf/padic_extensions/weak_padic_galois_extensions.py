r"""  Weak p-adic Galois extensions

Let `\hat{K}` be a `p`-adic number field. For our project we need to be able to
compute with Galois extensions `\hat{L]/}`\hat{K}` of large ramification degree.
For instance, we need to be able to compute the breaks of the ramification
filtration of the Galois group of `\hat{L}/\hat{K}`, as well as the corresponding
subfields.

At the moment, computations with large Galois extensions of `p`-adic fields are
still problematic. In particular, it seems difficult to obtain results which are
provably correct. For this reason we do not work which `p`-adic numbers at all.
Instead, we approximate `p`-adic fields by pairs `(K, v_K)`, where `K` is  a
number field and `v_K` a `p`-adic valuation on `K`. Given any finite extension
`\hat{L}/\hat{K}`, there always exists a finite extension `L/K` and an extension
`v_L` of `v_K` such that `\hat{L}` is the completion of `L` and `v_L` (this is
an easy consequence of Krasner's lemma).

From a more abstract point of view our approach means that
we work with the **henselization** `K^h` of `K` at `v_K`. Since we are mostly
interested in ramification, we may also consider the **strict** henselization
`K^{sh}` of `K` with respect to `v_K`, i.e. the maximal unramified extension
of `K^h`.

Let `L/K` be a finite field extension and `v_L` an extension of `v_K` to `L`.
We say that `L/K` is a **weak Galois extension** (with respect to `v_L`)
if `L^{sh}/K^{sh}` is Galois. Given a polynomial `f` in `K[x]`, we say that
`L/K` is a **weak splitting field** for `f` if `f` splits over `L^{sh}`.

Given a weak Galois extension `L/K`, we have canonical isomorphisms between the
following groups:

- the Galois group of `L^{sh}/K^{sh]}`,
- the inertia subgroup of the Galois closure of `\hat{L}/\hat{K}`,
- the inertia subgroup of the Galois closure of `L/K`, with respect to some
    extension of `v_K`.

Moreover, these isomorphisms respect the filtrations by higher ramification
groups.

If `L/K` is totally ramified then the degree of `L/K` is equal to the degree
of `L^{sh}/K^{sh}`, which is equal to the order of the inertia subgroup of the
Galois closure of `\hat{L}/\hat{K}`. Therefore, our approach allows us to fully
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
from sage.rings.integer import Integer
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
from mclf.padic_extensions.approximate_characteristic_polynomial import approximate_characteristic_polynomial

ZZ = Integer


class WeakPadicGaloisExtension(SageObject):
    r"""
    Return the weak splitting field of a list of polynomials.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``F`` -- a polynomial over `K`, or a list of irreducibel polynomials
    - ``minimal_ramification`` -- a positive integer (default: ``1``)
    - ``version`` -- a string (default: "experimental1")

    OUTPUT: a weak splitting field of ``F`` whose ramification index (as an
    extension of ``vK``) is a multiple of ``minimal_ramification``

    """

    def __init__(self, vK, F, minimal_ramification=ZZ(1), version="experimental2"):

        # print "calling WeakPadicGaloisExtension with vK = ", vK
        # print "F = ", F
        # print "and minimal_ramification = ", minimal_ramification
        p = vK.p()
        self._vK = vK
        self._K = vK.domain()
        # # if F is a polynomial, replace it by the list of its irreducible factors
        # if isinstance(F, Polynomial):
        #     F = [f for f, m in F.factor()]
        if not isinstance(F, Polynomial):
            if F == []:
                F = PolynomialRing(self._K,'x')(1)
            else:
                F = prod(F)
        if F.is_constant():
            self._vL = vK
            self._L = vK.domain()
            self._vLn = vK.scale(1/vK(vK.uniformizer()))
            self._ram_degree = ZZ(1)
            self._inertia_degree = ZZ(1)
            self._degree = ZZ(1)

        if version == "experimental2":
            assert vK.domain() == QQ, "the base field must be QQ"
            if F.is_constant():
                vL = vK
            else:
                vL = weak_splitting_field_2(vK, F)
            piL = vL.uniformizer()
            piK = vK.uniformizer()
            eL = vL(p)/vL(piL)  # absolute ramification index of vL
            eK = vK(p)/vK(piK)  # absolute ramification index of vK
            e = ZZ(eL/eK)       # the ramification index of L/K
                                # formulas should hold no matter how vK, vL
                                # are normalized
            if not minimal_ramification.divides(e):
                        # enlarge the absolute ramification index of vL
                        # such that minimal_ramification divides e(vL/vK):
                m = ZZ(eL*minimal_ramification/e.gcd(minimal_ramification))
                vL = padic_sufficiently_ramified_extension(vL, m)
                piL = vL.uniformizer()
            vLn = vL.scale(1/vL(piL))
            self._ram_degree = vLn(p)
            if self._ram_degree > 1:
                self._inertia_degree = vL.residue_field().degree()
                self._degree = self._ram_degree * self._inertia_degree
            else:                # if vL is unramified, we can replace it by
                vL = vK          # the trivial extension
                vLn = vK
                self._inertia_degree = 1
                self._degree = 1
            self._vL = vL
            self._L = vL.domain()
            self._vLn = vLn

        else:
            raise NotImplementedError

        # compute ramification jumps, lower numbering:

        if self._ram_degree == ZZ(1):
            jumps = []
        else:
            vK1 = padic_unramified_extension(vK, self._inertia_degree)
            K1 = vK1.domain()
            P = piL.minpoly().change_ring(K1)
            P1 = padic_irreducible_factor(vK1, P)
            assert P1.degree() == self._ram_degree
            R = P1.parent()
            v1 = vK1.mac_lane_approximants(P1)[0]
            v1 = LimitValuation(v1, P1)
            v1 = v1.scale(1/v1(v1.uniformizer()))
            assert v1(P1) == Infinity
            S = PolynomialRing(R, 'T')
            G = P1(S(R.gen()) + S.gen()).shift(-1)
            NP = NewtonPolygon([(i, v1(G[i])) for i in range(G.degree()+1)])
            jumps = []
            for v1, v2 in NP.sides():
                u = (v1[1]-v2[1])/(v2[0]-v1[0]) - 1  # jump = -slope - 1
                m = v2[0] + 1
                if u == 0:                # G does not distinguish Gamma and Gamma_0
                    m = self._ram_degree
                jumps.append((u, m))
            jumps.reverse()               # increasing order for jumps
            if len(jumps) >= 2 and jumps[0][1] == jumps[1][1]:
                jumps = jumps[1:]     # u=0 is not a jump
        self._lower_jumps = jumps

        # compute ramificaton jumps, upper numbering:

        if jumps == []:
            self._upper_jumps = []
        else:
            m = [m_i for m_i, g_i in jumps]
            g = [g_i for m_i, g_i in jumps]
            e = self._ram_degree
            u = [m[0]*g[0]/e]
            for i in range(1, len(jumps)):
                u.append(u[i-1]+(m[i]-m[i-1])*g[i]/e)
            self._upper_jumps = [(u[i], g[i]) for i in range(len(jumps))]

    def base_field(self):

        return self._L

    def base_valuation(self):

        return self._vK

    def field(self):

        return self._L

    def valuation(self):

        return self._vL

    def normalized_valuation(self):

        return self._vLn

    def degree(self):

        return self._degree

    def p(self):

        return self._p

    def ramification_degree(self):

        return self._ram_degree

    def inertia_degree(self):

        return self._inertia_degree

    def ramification_filtration(self, upper_numering=False):
        r"""
        Return the list of ramification jumps.

        INPUT:

        - ``upper_numbering`` -- a boolean (default: ``False``)

        OUTPUT: an ordered list of pairs `(u, m_u)`, where `u` is a jump in the
        filtration of higher ramification groups and `m_u` is the order of the
        corresponding subgroup. The ordering is by increasing jumps.

        If ``upper_numbering`` is ``False``, then the filtration is defined as
        follows. Let `L/K` be a Galois extension of henselian fields, with
        Galois group `G`. Let `\pi` be a prime element of `L`, and let `v_L`
        denote the normalized valuation on `L` (such that `v_L(\pi)=1`). For
        `u\geq 0`, the ramification subgroup `G_u` consists of all element
        `\sigma` of the inertia subgroup `I` of `G` such that

        .. MATH::

             v_L(\sigma(\pi)-\pi) \geq i + 1.

        In particular, `I=G_0`. An integer `u\geq 0` is called a "jump" if
        `G_{u+1}` is strictly contained in `G_u`.
        """

        if upper_numering:
            return self._upper_jumps
        else:
            return self._lower_jumps

    def lower_jumps(self):

        return [u for u, m in self._lower_jumps]

    def upper_jumps(self):

        return [u for u, m in self._upper_jumps]


    def ramification_subfields(self):

        pass

    def ramification_subfield(self):

        pass


#------------------------------------------------------------------------------

#                         auxiliary functions



def is_padic_irreducible_factor(vK, g, f):
    r"""
    Check whether ``g`` is an irreducible factor of ``f``.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``f``, ``g``: univariate polynomials in over `K`; it is assumed that
        ``g` is monic
        do we need this assumption ??
        and irreducible over the completion of `K`, and of degree
        strictly less than the degree of ``f``

    Output: True if ``g`` is an approximate factor of f, i.e.
    if g is irreducible and Krasner's condition is satified (see below),
    and False otherwise.


    Krasner's condition implies that the stem field of ``g`` over the completion
    of `K` is a subfield of the splitting field of ``f`` over the completion
    of `K`.

    # Method: we check if for some root alpha
    # of g there exists a root beta of f such that alpha is p-adically
    # closer to beta than to any other root of g.
    # It follows from Krasner's Lemma that in this case K[alpha] is a subfield
    # of K[beta].
    # Note that if deg(g)=1 then the condition is nontrivial, even though
    # the conclusion from Krasner's Lemma is trivial.

    """

    # print '.....'
    # print 'calling is_padic_irreducible_factor with g=',g,'and f=',f,' over K=',vK.domain()
    R = f.parent()
    K = R.base_ring()
    assert K is vK.domain(), 'the base ring of f is not the domain of vK'
    assert R is g.parent(), 'f and g do not lie in the same ring'
    assert g.is_monic(), 'g has to be monic'
    # assert g.degree() < f.degree(), "the degree of g must be less than the degree of f"
    x = R.gen()

    if g == f:
        return True
    if g.degree() == 1:             # the case deg(g)=1 is different
        alpha = -g[0]               # the unique root of g
        F = f(x+alpha)
        if F[0] == 0:               # alpha is an exact root of f
            return True
        np_f = NewtonPolygon([(i, vK(F[i])) for i in range(F.degree()+1)])
                # the slopes correspond to vK(alpha-beta), beta the roots of f
        return ( len(np_f.vertices())>1 and np_f.vertices()[1][0]==1 and
                np_f.slopes()[0]<0 )

    # now deg(g)>1
    # we check that g is really irreducible over the completion
    V = vK.mac_lane_approximants(g)
    if len(V) != 1:
        return False   # g is not irreducible
    v = V[0]
    while v(g) < Infinity:
        v = v.mac_lane_step(g)[0]

    # the valuation v has the property
    #        v(h)=vK(h(alpha))
    # for all h in K[x], where alpha is a root of g

    S = PolynomialRing(R, 'T')
    G = g(x + S.gen()).shift(-1)
    # print "G = ", G
    np_g = NewtonPolygon([(i, v(G[i])) for i in range(G.degree()+1)])
    # print "np_g = ", np_g
    # the slopes of np_g correspond to the valuations of
    # alpha-alpha_i, where alpha_i runs over all roots of
    # g distinct from alpha
    # print 'np_g=',np_g,'and slopes',np_g.slopes()

    F = f(x + S.gen())
    # print " F = ", F
    np_f = NewtonPolygon([(i, v(F[i])) for i in range(F.degree()+1)])
    # print "np_f = ", np_f

    # the slopes of np_f correspond to the valuations of
    # alpha-beta, where beta runs over all roots of
    # f

    result = min(np_g.slopes()) > min(np_f.slopes())
    return result

    # returns true if there is a root beta of f
    # such that vK(alpha-beta)>vK(alpha-alpha_i) for all i


def padic_irreducible_factor(vK, f):
    r"""
    Return an approximate irreducible factor of ``f``.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``f`` -- a squarefree univariate polynomial over `K`

    OUTPUT: a polynomial `g` which is irreducible over the completion `\hat{K}`
    of `K` at ``vK``, such that the stem field of `g` over `\hat{K}` is

    - a subfield of the splittig field of ``f`` over `\hat{K}`, and
    - a nontrivial and ramified extension of `\hat{K}`.

    If no such polynomial exist, then ``None`` is returned. This is the case
    if and only if ``f`` splits over an unramified extension of `\hat{K}`.`

    """

    # print '....'
    # print 'calling padic_irreducible_factor with K=',vK.domain(),' and f=',f

    K = vK.domain()
    p = vK.residue_field().characteristic()
    e = vK(p)/vK(vK.uniformizer())  # the total ramification degree of (K,vK)
    assert not f.is_constant(), 'f must not be constant'
    V = vK.mac_lane_approximants(f, require_incomparability=True)
    # V = [improve_maclane_valuation(v) for v in V]
    V = [LimitValuation(v, f) for v in V]
    # print "V = ", V
    n = f.degree()
    while V != []:
        V_new = []
        for v in V:
            v1 = v._approximation
            g = v1.phi()
            # print "g = ", g
            if g.degree() == f.degree() or is_padic_irreducible_factor(vK, g, f):
                # this is dangerous; shouldn't the first condition go?
                if v(p)/v(v.uniformizer()) > e:
                    return g
            else:
                v._improve_approximation()
                V_new.append(v)
        V = V_new
        # print "new V = ", V

    return None


def padic_irreducible_factors(vK, f):
    r"""
    Return a list of approximate irreducible factors of ``f``.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``f`` -- a squarefree univariate polynomial over `K`

    OUTPUT: a list of pairs `(g,e)`, where `g` is a polynomial over `K` which is
    irreducible over the completion `\hat{K}` of `K` at `v_K` and `e>=1`.
    The pairs `(g,e)` are in bijection with the irreducible factors of `f` over
    `\hat{K}`. If `(g,e)` corresponds to the irreducible factor `f_i' then `g`
    and `f_i` generate the same extension of `\hat{K}`. In particular, `f_i` and
    `g` have the same degree. Moreover `e` is the ramification degree of the
    of `\hat{K}` generated by `g` (or `f_i`).

    At the moment we have to assume that `f` is monic and integral
    with respect to `v_K`.

    """
    K = vK.domain()
    p = vK.residue_field().characteristic()
    # eK = vK(p)/vK(vK.uniformizer())  # the total ramification degree of (K,vK)
    assert not f.is_constant(), 'f must not be constant'
    n = f.degree()
    V = vK.mac_lane_approximants(f, require_incomparability=True)
    # print "V = ", V
    V = [LimitValuation(v, f) for v in V]
    ret = []
    while sum([g.degree() for g, e in ret]) < n:
        ret = []
        for v in V:
            while True:
                g = v._approximation.phi()
                if is_padic_irreducible_factor(vK, g, f):
                    break
                else:
                    v._improve_approximation()
            g = simplify_irreducible_polynomial(vK, g)
            e = vK(vK.uniformizer())/v(v.uniformizer())
            ret.append((g,e))
    return ret


#------------------------------------------------------------------------------

#                          experimental version 1


def weak_splitting_field_1(vK, f):
    r""" Return the weak splitting field of ``f`` with respect to ``vp``

    INPUT:

    - ``vp`` -- the `p`-adic valuation on the rational field, for some prime `p`
    - ``f`` -- a nonconstant univariat polynomial over the rational field

    OUTPUT: a `p`-adic valuation `v_L` on a number field `L`
    such that `(L,v_L)` is a weak splitting field of ``f``. This means that
    ``f`` splits over the strict henselization of `L` with respect to `v_L`,
    and that the strict henselization is a Galois extension of the strict
    henselization of ``Q`` at `p`.

    """

    # print '........'
    # print 'calling padic_splitting_field with vK=',vK
    # print ' and f=',f
    # print

    K = QQ
    assert f.base_ring() is K
    p = vK.residue_field().characteristic()

    L = K
    vL = vK
    while True:
        g = padic_irreducible_factor(vL, f)
        if g == None:
            return vL
        # print "g = ", g
        n = g.degree()
        if p.gcd(n) == 1:
            vL = padic_sufficiently_ramified_extension(vL, n)
        else:
            vL = padic_simple_extension(vL, g)
        L = vL.domain()
        # print "L = ", L
        R = PolynomialRing(L,'x%s'%randint(10,20))
        f = R(f)
        assert f.base_ring() is L


#--------------------------------------------------------------------------

#                    experimental version 2

def weak_splitting_field_2(vK, f):
    r""" Return the weak splitting field of ``f`` with respect to ``vp``

    INPUT:

    - ``vp`` -- the `p`-adic valuation on the rational field, for some prime `p`
    - ``f`` -- a nonconstant univariat polynomial over the rational field

    OUTPUT: a `p`-adic valuation `v_L` on a number field `L`
    such that `(L,v_L)` is a weak splitting field of ``f``. This means that
    ``f`` splits over the strict henselization of `L` with respect to `v_L`,
    and that the strict henselization is a Galois extension of the strict
    henselization of ``Q`` at `p`.

    """
    K = QQ
    assert f.base_ring() is K
    p = vK.residue_field().characteristic()

    factor_list = padic_irreducible_factors(vK, f)
    # this is a list of pairs (g,e)
    F = [g for g,e in factor_list if e > 1]
    # print "F = ", F
    # F contains all the factors of f over QQ which lead to ramification
    # we keep this list, and try to find an extension L/QQ which splits
    # splits all elements of F
    done = (F == [])

    L = K
    vL = vK
    while not done:
        # check if there are factors which lead to wild ramification
        G = [g for g, e in factor_list if p.divides(e)]
        # print "G = ", G
        if G != []:
            g = G[0]
            vL = padic_simple_extension(vL, g)
            L = vL.domain()
            # we have to created the new factor list
            factor_list = []
            F_new = []
            done = True  # unless we find a factor in F which still needs attention
            for f in F:
                fL = f.change_ring(L)
                partial_factor_list = padic_irreducible_factors(vL, fL)
                for g, e in partial_factor_list:
                    if e > 1:
                        factor_list.append((g,e))
                        # we keep f in our list of factors we want to split
                        F_new.append(f)
                        done = False
            F = F_new
            # print "new factor list : ", factor_list
        else:
            # there are no factors with wild ramification
            # it remains to find  the lcm of the ramification indeces
            # and produce an extension of this degree
            n = lcm([e for g, e in factor_list])
            vL = padic_sufficiently_ramified_extension(vL, n)
            done = True
    return vL


#----------------------------------------------------------------------------

#          experimental version 3: extra handling of p=2


def weak_splitting_field_3(f):
    r""" Return the weak splitting field of ``f`` with respect to `2`-adic valuation.

    INPUT:

    - ``f`` -- a nonconstant univariat polynomial over the rational field

    OUTPUT: a `2`-adic valuation `v_L` on a number field `L`
    such that `(L,v_L)` is a weak splitting field of ``f``. This means that
    ``f`` splits over the strict henselization of `L` with respect to `v_L`,
    and that the strict henselization is a Galois extension of the strict
    henselization of ``Q`` at `p=2`.

    """
    K = QQ
    assert f.base_ring() is K
    vK = pAdicValuation(K, 2)

    factor_list = padic_irreducible_factors(vK, f)
    # this is a list of pairs (g,e)
    F = [g for g,e in factor_list if e > 1]
    # print "F = ", F
    # F contains all the factors of f over QQ which lead to ramification
    # we keep this list, and try to find an extension L/QQ which splits
    # splits all elements of F
    done = (F == [])

    L = K
    vL = vK
    while not done:
        # check if there are factors which lead to wild ramification
        G = [g for g, e in factor_list if ZZ(2).divides(e)]
        # print "G = ", G
        if G != []:
            g = G[0]
            delta = g.discriminant()
            vL1 = twoadic_quadratic_extension(vL, delta)
            if not vL1 == vL:
                 vL = vL1
                 print "took the square root of the discriminant of g = ", g
            else:
                print "need to take the simple extension given by g = ", g
                vL = padic_simple_extension(vL, g)
            L = vL.domain()
            # we have to created the new factor list
            factor_list = []
            F_new = []
            done = True  # unless we find a factor in F which still needs attention
            for f in F:
                fL = f.change_ring(L)
                partial_factor_list = padic_irreducible_factors(vL, fL)
                for g, e in partial_factor_list:
                    if e > 1:
                        factor_list.append((g,e))
                        # we keep f in our list of factors we want to split
                        F_new.append(f)
                        done = False
            F = F_new
            # print "new factor list : ", factor_list
        else:
            # there are no factors with wild ramification
            # it remains to find  the lcm of the ramification indeces
            # and produce an extension of this degree
            n = lcm([e for g, e in factor_list])
            vL = padic_sufficiently_ramified_extension(vL, n)
            done = True
            print "took a tame extension of degree n = ", n
    return vL


def twoadic_quadratic_extension(vK, delta):
    r"""
    Return the `2`-adic quadratic extension obtain by taking a square root.

    INPUT:

    - ``vK`` -- a `2`-adic valuation on a number field `K`
    - ``delta`` -- an element of `K` which is not a square

    OUTPUT:

    A `2`-adic valuation `v_L` on a number field `L` such that

    - `L=K`, or the strict henselization of `L` at `v_L` is a quadratic extension
      of the strict henselization of `K` at `v_K`
    - ``delta`` is a square in the strict henselizaton of `L` at `v_L`.

    """
    K = vK.domain()
    # assert delta.parent() is K, "delta must be an element of the domain of vK"
    delta = K(delta)
    assert vK.residue_field().characteristic() == 2, "vK must be a 2-adic extension"
    assert not delta.is_zero(), "delta must be nonzero"
    R = PolynomialRing(K, 'z')
    z = R.gen()

    pi = vK.uniformizer()
    e = 1/vK(pi)
    n = ZZ(e*vK(delta))
    if not ZZ(2).divides(n):
        k = ZZ((n-1)/2)
        g = z**2 - simplify_coeff(delta/pi**(2*k), ZZ(2), ZZ(3))
    else:
        k = ZZ(n/2)
        delta = delta/pi**(2*k)
        # now delta is a unit; it can be further simplified:
        delta = simplify_coeff(delta, ZZ(2), ZZ(3))
        a, b = two_approximation(vK, delta)
        # now delta = a^2 + b, such that the valuation of b is either maximal,
        # or vK(b) >= vK(4)
        if vK(b) >= vK(4):
            # the extension K(delta^(1/2))/K is unramified
            return vK
        else:
            n = ZZ(e*vK(b))
            print "n = ", n
            assert not ZZ(2).divides(n), "something is wrong with the two-approximation"
            k = ZZ((n-1)/2)
            print "k = ", k
            g1 = simplify_coeff(2*pi**(-k)*a, ZZ(2), ZZ(3))
            g0 = simplify_coeff(- b*pi**(-2*k), ZZ(2), ZZ(3))
            g = z**2 + g1*z + g0
            print "g = ", g
            assert e*vK(g[0]) == 1 and e*vK(g[1]) >= 1, "g is not Eisenstein!"
    L = K.extension(g, 'pi')
    piL = L.gen()
    P = piL.absolute_charpoly()
    P = simplify_irreducible_polynomial(pAdicValuation(QQ, 2), P)
    L = NumberField(P, 'pi%s'%P.degree(), maximize_at_primes=[])
    print "L = ", L
    vL = pAdicValuation(QQ, 2).extension(L)
    return vL


def two_approximation(vK, a):
    r"""
    Return the `2`-approximation of ``a`` with respect to ``vK``.

    INPUT:

    - ``vK`` -- a `2`-adic valuation on a number field `K`
    - ``a`` -- an element of `K` which is a unit for `v_K`

    OUTPUT: a pair `(b, c)` of elements of `K` such that

    - `a=b^2+c`
    - the valuation `v_K(c)` is either maximal, or `v_K(c)\geq v_K(4)`

    If `v_K(c)\geq v_K(4)` then the extension `K(\sqrt{a})/K` is known
    to be unramified at `v_K`. Otherwise, `v_K(c)` attains a maximum
    which is stricly smaller than `v_K(4)` and such that `v_K(c)/2` is not
    in the value group of `v_K`. This is the case if and only if the
    extension `K(\sqrt{a})/K` is ramified.

    """
    assert vK(a) == 0, "a must be a unit for vK"
    pi = vK.uniformizer()
    e = 1/vK(pi)
    n = e*vK(4)
    b = vK.lift(vK.reduce(a).square_root())
    c = a - b**2
    k = e*vK(c)
    while k < n and ZZ(2).divides(k):
        print "a = %s, b = %s, c = %s"%(a,b,c)
        print "k= %s, n = %s"%(k, n)
        c1 = c*pi**(-k)
        d1 = vK.lift(vK.reduce(c1).square_root())
        b = b + pi**(k/2)*d1
        c = a -  b**2
        k = e*vK(c)
    print "k = ", k
    return b, c


#--------------------------------------------------------------------------

#                    experimental version 4

def weak_splitting_field_4(vK, f):
    r""" Return the weak splitting field of ``f`` with respect to ``vp``

    INPUT:

    - ``vp`` -- the `p`-adic valuation on the rational field, for some prime `p`
    - ``f`` -- a nonconstant univariat polynomial over the rational field;
      it is assumed that `f` is irreducible over `\mathbb{Q}_p`.

    OUTPUT: a `p`-adic valuation `v_L` on a number field `L`
    such that `(L,v_L)` is a weak splitting field of ``f``. This means that
    ``f`` splits over the strict henselization of `L` with respect to `v_L`,
    and that the strict henselization is a Galois extension of the strict
    henselization of ``Q`` at `p`.

    """
    K = QQ
    assert f.base_ring() is K
    p = vK.residue_field().characteristic()

    factor_list = padic_irreducible_factors(vK, f)
    # this is a list of pairs (g,e)
    F = [g for g,e in factor_list if e > 1]
    # print "F = ", F
    # F contains all the factors of f over QQ which lead to ramification
    # we keep this list, and try to find an extension L/QQ which splits
    # splits all elements of F
    done = (F == [])
    assert len(F) == 1, "f has to be irreducible over QQ_p"
    f = F[0]
    n = f.degree()

    L = K.extension(f, 'gamma')
    vL = vK.extension
    while not done:
        # check if there are factors which lead to wild ramification
        G = [g for g, e in factor_list if p.divides(e)]
        # print "G = ", G
        if G != []:
            g = G[0]
            vL = padic_simple_extension(vL, g)
            L = vL.domain()
            # we have to created the new factor list
            factor_list = []
            F_new = []
            done = True  # unless we find a factor in F which still needs attention
            for f in F:
                fL = f.change_ring(L)
                partial_factor_list = padic_irreducible_factors(vL, fL)
                for g, e in partial_factor_list:
                    if e > 1:
                        factor_list.append((g,e))
                        # we keep f in our list of factors we want to split
                        F_new.append(f)
                        done = False
            F = F_new
            # print "new factor list : ", factor_list
        else:
            # there are no factors with wild ramification
            # it remains to find  the lcm of the ramification indeces
            # and produce an extension of this degree
            n = lcm([e for g, e in factor_list])
            vL = padic_sufficiently_ramified_extension(vL, n)
            done = True
    return vL




#----------------------------------------------------------------------------


def padic_simple_extension(vK,f):
    r"""
    Return a p-adic extension containing a root of ``f``.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``f`` -- a polynomial over `K`, irreducible over the completion of `K`

    Output: a `p`-adic valuation `v_L` on a number field `L`, such that the
    completion of `L` at `v_L` is isomorphic to the stem field of ``f`` over
    the completion of `K` at ``vK``.

    Note that `L` will in general not be an extension of `K`.

    """

    # print '.....'
    # print 'calling padic_simple_extension with K = ', vK.domain()
    # print 'and f = ', f

    K = vK.domain()
    R = f.parent()
    p = vK.residue_field().characteristic()
    assert R.base_ring() is K, 'f is not defined over the domain of vK'

    V = vK.mac_lane_approximants(f)
    assert len(V) == 1, "f is not irreducible over the completion"
    v = LimitValuation(V[0], f)
    pix = v.uniformizer()
    r = v(pix)
    for m in range(2,10):                                           # this loop has been added on 25.10.2016
        pix1 = pix.map_coefficients(lambda c:simplify_coeff(c, p, m))
        if v(pix1) == r:
            break
    P = approximate_characteristic_polynomial(K, f, pix1, p, m + 70)    # der Exponent m+5 ist rein heuristisch gewaehlt
                                                                       # eigentlich muesste man eine Abschaetzung berechnen
    # L = K.extension(f, 'gamma')
    # vL = vK.extension(L)
    # pi = vL.uniformizer()
    # P = pi.absolute_minpoly()

    print "P = ", P
    P = simplify_irreducible_polynomial(pAdicValuation(QQ, p), P)
    print "P simplified = ", P
    L = NumberField(P, 'pi%s'%P.degree(), maximize_at_primes=[])
    print "L = ", L
    v_L = pAdicValuation(QQ,p).extension(L)
    return v_L


def padic_sufficiently_ramified_extension(vK, e):
    """
    Return an extensions whose absolute ramification index is divided by e.
    """

    p = vK.residue_field().characteristic()
    e1 = vK(p)/vK(vK.uniformizer())
    n = e/e.gcd(e1)
    # print "n = ",n
    if n > 1:
        K = vK.domain()
        A = PolynomialRing(K, 'w')
        return padic_simple_extension(vK, A.gen()**n-vK.uniformizer())
    else:
        return vK


def padic_unramified_extension(vK, n):
    r"""
    Return an unramified extension of degree ``n``.

    """
    if n == 1:
        return vK
    k0 = vK.residue_field()
    assert k0.is_finite()
    k1 = k0.extension(n)
    gb = k1.polynomial()
    fb = gb.change_ring(k0).factor()[0][0]
    R = PolynomialRing(vK.domain(), 'x')
    f = R([vK.lift(fb[i]) for i in range(fb.degree()+1)])
    L = vK.domain().extension(f, 'theta'+str(n))
    vL = vK.extension(L)
    return vL


#----------------------------------------------------------------------------

def compute_approximate_minpoly(K, f, g, p, N):

    # K: a (relative) number field
    # f,g: polynomials in K[x], f is irreducible

    # returns the absolute minimal polynomial of beta=g(alpha) with respect
    # to the extension L:=K[alpha|f(alpha)=0]/QQ, modulo p**N

    print '...'
    print 'calling compute_absolute_minpoly with K=',K,',\nl f=',f,', \n g=',g

    L = K.extension(f, 'alpha')
    print "L = ", L
    d = L.absolute_degree()
    La = L.absolute_field('gamma'+str(d))
    print "La = ", La
    phi, psi = La.structure()
    ga = g.map_coefficients(psi, La)
    beta = ga(psi(L.gen()))
    print "beta = ", beta
    print "computing the minimal polynomial of beta: "
    F = beta.minpoly()
    print "F = ", F
    print
    print [c.valuation(p) for c in F.padded_list()]
    return F.map_coefficients(lambda c:Integer(mod(c,p**N))) # F mod p**N , i.e. over the ring Z/p**N


def improve_maclane_valuation(v):
    """ Return an improvement of v.

    INPUT:

    - v -- an inductive valuation on a polynomial ring K[x]

    OUTPUT:

    an inductive valuation v1 on K[x] which is equal to v (as a valuation)
    but whose representation is (hopefully) simpler.

    At the moment, we simply try to replace the last key polynomial
    phi of the given representation by a polynomial phi1 whose
    coefficients are as small as possible.
    """

    print '....'
    print 'calling improve_maclane_valuation with v=',v
    v0 = v._base_valuation
    # vK = v.constant_valuation()

    p = v.residue_field().characteristic()
    phi = v.phi()
    s = v(phi)
    r = s/v(p)
    if r == Infinity:
        return v
    N = floor(r)+1
    while true:
        phi1 = phi.parent()([simplify_coeff(c,p,N) for c in phi.padded_list()])
        if v0.is_key(phi1) and v(phi1) == s:
            v1=v0.augmentation(phi1, s)
            if v1(phi) == s:
                print "v1 = ", v1
                return v1
            else:
                print "v1(phi)!= s"
        print "improvement for N=%s not sufficient."%N
        N += 1


def simplify_irreducible_polynomial(vK, f):
    r"""
    Return a simpler polynomial generating the same extension.

    INPUT:

    - ``vK`` -- a p-adic valuation on a number field `K`
    - ``f`` -- an univariate polynomial over K which is irreducible over the completion of `K`

    OUTPUT:

    A polynomial `g` over `K` which is irreducible over the completion `\hat{K}`
    of `K`, and which generates the same extension of `\hat{K}` as `f`.

    """
    R = f.parent()
    p = vK.p()
    assert R.base_ring() == vK.domain(), "f must be defined over the domain of vK"
    # first we see if we can normalize f such that the unique slope of the
    # Newton polygon is >-1 and <=0.
    NP = NewtonPolygon([(i, vK(f[i])) for i in range(f.degree()+1)])
    slopes = NP.slopes(repetition=False)
    assert len(slopes) == 1, "f is not irreducible over the completion!"
    s = slopes[0]
    assert s <= 0, "f is not integral"
    if s <= -1:
        m = floor(-s)
        pi = vK.uniformizer()
        f = f(pi**m*R.gen()).monic()
    # Now we simplify the coefficients of f
    N = (vK(f[0])/vK(p)).ceil() + 1
    n = f.degree()
    while True:
        # print "N = ", N
        g = R([simplify_coeff(f[i], p, N) for i in range(n+1)])
        # print "g = ", g
        try:
            is_irreducible_factor = is_padic_irreducible_factor(vK, g, f)
        except (AssertionError, ValueError):
            is_irreducible_factor = False
        if is_irreducible_factor:
            return g
        else:
            N = N + 1


def simplify_coeff(c,p,N):

    K = c.parent()
    if K == QQ:
        k = c.valuation(p)
        if k >= 0:
            return Integer(mod(c,p**N))
        else:
            return Integer(mod(c*p**(-k),p**N))*p**k
    else:
        l = c.list()
        l = [simplify_coeff(l[i],p,N) for i in range(0,len(l))]
        return sum([l[i]*K.gen()**i for i in range(0,len(l))])

        # Ka.<alpha>=K.absolute_field()
        # to_K,from_K=Ka.structure()
        # f=from_K(c).polynomial()
        # f=f.map_coefficients(lambda x:Integer(mod(x,p**N)))
        # return to_K(Ka(f))
