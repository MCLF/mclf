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
from sage.rings import *
# from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
# from sage.rings.polynomial.polynomial_element import Polynomial
# from sage.rings.integer import Integer
# from sage.rings.finite_rings.integer_mod import mod
from sage.misc.cachefunc import cached_method
# from sage.rings.infinity import Infinity
from sage.functions.generalized import sgn
from sage.geometry.newton_polygon import NewtonPolygon
from mac_lane import *



class WeakPadicGaloisExtension(SageObject):
    r"""
    Return the weak splitting field of a list of polynomials.

    INPUT:

    - ``vK`` -- a `p`-adic valuation on a number field `K`
    - ``F`` -- a polynomial over `K`, or a list of irreducibel polynomials
    - ``version`` -- a string (default: "experimental1")

    OUTPUT: a weak splitting field of ``F``.

    """

    def __init__(self, vK, F, version="experimental1"):

        p = vK.p()
        self._vK = vK
        self._K = vK.domain()
        # # if F is a polynomial, replace it by the list of its irreducible factors
        # if isinstance(F, Polynomial):
        #     F = [f for f, m in F.factor()]
        if not isinstance(F, Polynomial):
            F = prod(F)

        if version == "experimental1":
            assert vK.domain() == QQ, "the base field must be QQ"
            vL = weak_splitting_field_1(vK, F)
            pi = vL.uniformizer()
            vLn = vL.scale(1/vL(vL.uniformizer()))
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

        if self._ram_degree == 0:
            jumps = []
        else:
            vK1 = padic_unramified_extension(vK, self._inertia_degree)
            K1 = vK1.domain()
            P = pi.minpoly().change_ring(K1)
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
        ``g` is monic and irreducible over the completion of `K`, and of degree
        strictly less than the degree of ``f``

    Output: True if ``g`` is an approximate factor of f, i.e.
    if Krasner's condition is satified (see below), and False otherwise.


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
    assert g.degree() < f.degree(), "the degree of g must be less than the degree of f"
    x = R.gen()

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
    assert len(V) == 1, \
        "g is not irreducible over the completion of its base field."
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
    V = [LimitValuation(v, f) for v in V]
    # print "V = ", V
    n = f.degree()
    while V != []:
        V_new = []
        for v in V:
            g = v._approximation.phi()
            # print "g = ", g
            if g.degree() == f.degree() or is_padic_irreducible_factor(vK, g, f):
                if v(p)/v(v.uniformizer()) > e:
                    return g
            else:
                v._improve_approximation()
                V_new.append(v)
        V = V_new
        # print "new V = ", V

    return None


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
        # n = g.degree()
        # if p.gcd(n) == 1:
        #     vL = padic_sufficiently_ramified_extension(vL, n)
        # else:
        vL = padic_simple_extension(vL, g)
        L = vL.domain()
        R = PolynomialRing(L,'x%s'%randint(10,20))
        f = R(f)
        assert f.base_ring() is L


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

    n = K.absolute_degree()*f.degree()
    V = vK.mac_lane_approximants(f)
    assert len(V) == 1, "f is not irreducible over the completion"
    v = LimitValuation(V[0], f)
    pix = v.uniformizer()
    r = v(pix)
    for m in range(2,10):                                           # this loop has been added on 25.10.2016
        pix1 = pix.map_coefficients(lambda c:simplify_coeff(c, p, m))
        if v(pix1) == r: break
    # e = v(p)/r
    # fL = n/e
    P = compute_approximate_minpoly(K, f, pix1, p, m + 5)    # der Exponent m+5 ist rein heuristisch gewaehlt
                                                               # eigentlich muesste man eine Abschaetzung berechnen

    # print "P = ", P
    L = NumberField(P, 'pi%s'%P.degree(), maximize_at_primes=[])
    # print "L = ", L

    v_L = pAdicValuation(QQ,p).extension(L)
    return v_L

def padic_sufficiently_ramified_extension(vK, e):
    """
    Return an extensions whose absolute ramification index is divided by e.
    """

    p = vK.residue_field().characteristic()
    e1 = vK(p)/vK(vK.uniformizer())
    n = e/gcd(e,e1)
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

    # print '...'
    # print 'calling compute_absolute_minpoly with K=',K,',\nl f=',f,', \n g=',g

    L = K.extension(f, 'alpha')
    # print "L = ", L
    d = L.absolute_degree()
    La = L.absolute_field('gamma'+str(d))
    # print "La = ", La
    phi, psi = La.structure()
    ga = g.map_coefficients(psi, La)
    beta = ga(psi(L.gen()))
    # print "beta = ", beta
    # print "computing the minimal polynomial of beta: "
    F = beta.minpoly()                          # it should be much faster to compute
    # print "F = ", F
    # print
    #print [c.valuation(p) for c in F.padded_list()]
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

    # print '....'
    # print 'calling improve_maclane_valuation with v=',v
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
                return v1
            else:
                print "v1(phi)!= s"
        print "improvement for N=%s not sufficient."%N
        N += 1


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
