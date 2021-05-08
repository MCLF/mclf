# -*- coding: utf-8 -*-
r"""
Approximate factorization of polynomials over `p`-adic number fields
====================================================================

Let `K` be a `p`-adic number field and `f\in K[x]` an univariate polynomial over
`K`. A key task for us is to compute the splitting field `L/K` of `f` and
various intermediate fields (e.g. the stem fields of the prime factors of `f`).

Recall that we realize `K` internally by choosing a dense subfield `K_0\subset K`
and then try to do all computations with `K_0` and the valuation `v_K` on `K_0`
induced by the `p`adic valuation of `K`. Even if the given polynomial `f` has
coefficients in `K_0`, its irreducible factors may not be defined over `K_0`.
Fortunately, by Krasner's Lemma, it suffices to work with sufficiently good
approximations of the irreducible factors of `f`, and these can be chosen to
be defined over `K_0`.

In this module we implement the concept of an *approximate irreducible* factor
of a polynomial over a `p`-adic number field.

**Definition**

    Let `f,g \in K[x]` be polynomials over `K`. Assume that `g` is monic,
    integral, irreducible and of degree `\geq 2`. We say that `g` is an
    *approximate prime factor* of `f` if for every root  `\alpha` of `g` there
    exists a root `\beta` of `f` which is strictly closer to `\alpha` than to
    any other root of `g`. If, moreover, `\deg(g)=\deg(f)` then `f` and `g` are
    called *Krasner equivalent`.

    An *approximate prime factor* over `K` is a Krasner equivalence class of
    polynomials `g\in K[x]` which are monic, integral, irreducible and of degree
    `\geq 2`.

"""

from sage.all import SageObject, PolynomialRing, GaussValuation, Infinity
from mclf.padic_extensions.padic_number_fields import pAdicNumberField
from mclf.padic_extensions.fake_padic_extensions import FakepAdicExtension


def approximate_factorization(K, f, v0=None):
    r""" Return an approximate factorization of a squarefree polynomial over a
    p-adic number field.

    INPUT:

    - ``K`` - a p-adic number field
    - ``f`` -- a univariate, squarefree polynomial over `K`
    - ``v0` -- an inductive valuation on `K[x]`

    OUTPUT: the list of approximate prime factors of `f`.

    If an inductive valuation `v_0` is given, then only the factors with
    approximation `\geq v_0` are returned.

    An *approximate irreducible factor* is a Krasner equivalence class of monic,
    integral and irreducible polynomials `g` which are *approximate prime factors*
    of `f` in the following sense: for every root `\alpha` of `g` there exists
    a root `\beta` of `f` which is strictly closer to `\alpha` than all other
    roots of `g`.

    .. NOTE::

        It may be usefull to allow `v_0` to be an *enhanced valuation*.

    """
    if isinstance(K, FakepAdicExtension):
        K = K.extension_field()
    else:
        assert isinstance(K, pAdicNumberField)
    f = f.change_ring(K.number_field())
    if v0 is None:
        R = f.parent()
        v_K = K.valuation()
        v0 = GaussValuation(R, v_K)
        # as v_0 is the minimal inductive valuation, we put no restriction
        # on the prime factors of f

    from sage.geometry.newton_polygon import NewtonPolygon
    F = v0.equivalence_decomposition(f)
    ret = []
    # each irreducible factor of the equivalence decompositon of f corresponds
    # to a residue class of v0 containing at least one prime factor of f.
    # We visit these residue classes one after the other.
    for phi, _ in F:
        t0 = v0(phi)
        v00 = v0.augmentation(phi, t0, check=False)
        # we use v00 only for convenience; it is important not to augment it
        valuations = list(v00.valuations(f))
        a = min(valuations)
        n = min(i for i in range(len(valuations)) if valuations[i] == a)
        # n is the degree of f with respect to v00; n*deg(phi) is the number
        # of roots of f inside the residue class corresponding to phi
        np = NewtonPolygon(enumerate(valuations))
        slopes = [mu for mu in np.slopes(repetition=False) if mu < 0]
        if len(slopes) == 0:
            t1 = Infinity
        else:
            t1 = t0 - max(slopes)
        # now t1 is the maximal value such that the discoid corresponding to
        # v1=[v0, v(phi)=t1] still contains all the prime factors of f in
        # the residue class corresponding to phi
        # we have to see if there is a value t with t0 < t <= t1 such that
        # v=[v0, v1(phi)=t1] is separating.
        # This can only happen if deg(phi) > 1:
        if phi.degree() > 1:
            t = separating_value(v0, phi)
            if t >= t0 and t < t1:
                v = enhanced_augmentation(v0, phi, t)
                # v is an enhanced valuation!
                g = ApproximatePrimeFactor(K, v)
                ret.append(g)
        # We have to further look for irreducible factors of f beyond v1,
        # unless:
        if (n > 1 and t1 < Infinity) or (phi.degree() > 1 and t1 < Infinity and t >= t1):
            ret += approximate_factorization(K, f, v0.augmentation(phi, t1))
    return ret


def weak_splitting_field(K, f):
    r""" Return the weak splitting field of a polynomial
    over a `p`-adic number field.

    INPUT:

    - ``K`` -- a `p`-adic number field
    - ``f`` -- a polynomial `f\in K[x]`

    OUTPUT: a weak splitting field `L/K` of `f`.

    This means that `L/K` is a finite extension of `p`-adic number fields such
    that `f` splits into linear factors over an unramified extension of `L`.


    .. NOTE::

        At the moment, the extension that is returned is in general *not* an
        extension of `K`! But it should, and for this we need to implement
        composition of embeddings first.

    """
    f = f.change_ring(K.number_field())
    f = f.radical()
    if f.is_constant():
        return K
    v0 = GaussValuation(f.parent(), K.valuation())
    f = v0.monic_integral_model(f)[2]
    F = approximate_factorization(K, f)
    # F is the list of approximate irreducible factors of f
    # we first get rid of all unramified factors
    F = [g for g in F if not g.is_unramified()]
    L = K
    while len(F) > 0:
        L = F[0].stem_field()
        new_factors = []
        for g in F:
            new_factors += g.base_change(L)
        F = [g for g in new_factors if not g.is_unramified()]
    return L


class ApproximatePrimeFactor(SageObject):
    r""" An  approximation of a monic, integral and irreducible polynomial
    over a p-adic number field.

    More precisely, this object represents a *Krasner equivalence class* of
    polynomials (see below).

    INPUT:

    - ``K`` -- a p-adic number field
    - ``f`` -- data defining a Krasner equivalence class of irreducible
               polynomials over `K`.

    The data defining `f` can be of the following form:

    1. a polynomial over the number field `K_0` underlying `K` which is
      - monic and integral
      - irreducible over `K`
    2. an infinite pseudovaluation `v` on `K_0[x]`
    3. a separating *enhanced* inductive valuation on `K[x]`

    It is clear that a polynomial `f\in K_0[x]` satisfying the conditions in (1)
    determines a unique pseudovaluation `v_f` on `K_0[x]` such that `v_f(f)=\infty`.
    Conversely, an infinite pseudovaluation `v` determines a unique irreducible
    polynomial `f\in K[x]`, but the coefficients of `f` may not lie in `K_0`
    (in this case, `v` is defined as a limit valuation).

    Let `f_1,f_2\in K[x]` be two polynomials satisfying (1). We say
    that `f_1` and `f_2` are *Krasner equivalent* if they have the same degree,
    and for any root `\alpha` of `f_1` there exists a unique root `\beta` of
    `f_2` which is strictly closer to `alpha` than any other root of `f_1`.
    Then by Krasner's Lemma, the stem field `L=K(\alpha)` of `f_1` does only
    depend on the equivalence class of `f_1`.

    So if the input is as in (1) or (2), the object that is returned represents
    the Krasner equivalence class defined by the input.

    Let `v = [v_0,v(\phi)=t]` be an enhanced inductive valuation, which is an
    augmentation of `v_0` with key polynomial `\phi` (by enhanced we mean that
    the `v`-equivalence class of key polynomials containing `\phi` is part of
    data). We call `v` *separating* if the set of distinguished key polynomials
    is contained in a Krasner equivalence class. It is called *strictly separating*
    if it is equal to a Krasner equivalence class.

    Given a separating enhanced valuation `v`, there exists a unique strictly
    separating enhanced valuation `v_0` whose equivalence class contains the
    equivalence class of `v`. We call `v_0` the **root** of `v`.

    So if the input is as in (3) it defines a Krasner equivalence class as
    well. Conversely, a Krasner equivalence class gives rise to a unique
    strictly separating enhanced valuation. It is called the **root** of
    the Krasner class.

    """

    def __init__(self, K, f):
        from sage.rings.polynomial.polynomial_element import Polynomial
        assert isinstance(K, pAdicNumberField)
        self._base_field = K
        if isinstance(f, Polynomial):
            f = f.change_ring(K.number_field())
            assert f.is_monic(), "f must be monic"
            v0 = GaussValuation(f.parent(), K.valuation())
            assert f.is_monic(), "f must be monic"
            assert v0(f) >= 0, "f must be integral"
            v = v0
            while v(f) < Infinity:
                V = v.mac_lane_step(f)
                assert len(V) == 1, "f must be irreducible"
                v = V[0]
            self._pseudo_valuation = v
            self._approximate_polynomial = f
            self._polynomial_ring = f.parent()
        elif isinstance(f, EnhancedInductiveValuation):
            v = f
            assert v.is_separating(), "v must be separating"
            self._approximate_polynomial = v.key()
            self._polynomial_ring = v.key().parent()
            # we want to find the predecessor which is strictly separating
            self._root = v.root()
        elif f.is_discrete_pseudo_valuation() and not f.is_discrete_valuation():
            v = f
            self._polynomial_ring = v.domain()
            self._pseudo_valuation = v
        else:
            raise ValueError("f is not of the right type")

    def __repr__(self):
        return "an approximate irreducible polynomial over {} of degree {}".format(self.base_field(), self.degree())

    def base_field(self):
        return self._base_field

    def base_valuation(self):
        return self._base_field.valuation()

    def polynomial_ring(self):
        return self._polynomial_ring

    def root(self):
        if not hasattr(self, "_root"):
            raise NotImplementedError()
        return self._root

    def approximate_polynomial(self):
        if not hasattr(self, "_approximate_polynomial"):
            self._approximate_polynomial = self.root().key()
        return self._approximate_polynomial

    def degree(self):
        return self.approximate_polynomial().degree()

    def ramification_degree(self):
        return self.root().ramification_degree()

    def is_unramified(self):
        return self.ramification_degree().is_one()

    def is_tamely_ramified(self):
        p = self.base_field().p()
        return not p.divides(self.ramification_degree())

    def inertia_degree(self):
        return self.root().inertia_degree()

    def is_purely_wild(self):
        p = self.base_field().p()
        e = self.ramification_degree()
        return p.divides(e) and e.is_prime_power()

    def stem_field(self):
        r""" Return the stem field of this approximate irreducible polynomial.

        OUTPUT: the extension `L/K` of `p`-adic number fields defined by an
        irreducible polynomial representing this Krasner equivalence class.

        Let `f\in K[x]` be an monic, integral and irreducible polynomial lying
        in this Krasner equivalence class. Then the stem field `L:=K[\alpha]`,
        where `\alpha` is a root of `f`, is independent, up to unique isomorphism,
        from the choice of the representative `f`.


        .. NOTE::

            At the moment the extension `L/K` consists simply of an embedding of
            (fake) `p`-adic number fields. However, the fact that `L/K` was
            constructed as a stem field carries extra information. So in the future
            an object of an appropriate subclass should be produced, carrying this
            extra information.

        """
        K = self.base_field()
        return K.simple_extension(self.approximate_polynomial())

    def base_change(self, L):
        r""" Return the factorization of the base change of this irreducible factor
        with respect to a finite extension of the base field.

        INPUT:

        - ``L`` - a finite extension of the base field `K` of this irreducible factor

        OUTPUT: an approximate factorization of this irreducible factor `f`,
        considered as an (approximate) polynomial in `L[x]`.

        Note that the linear factors of `f` over `L` are ignored.

        """
        V = self.root().base_change(L.embedding())
        return [ApproximatePrimeFactor(L.extension_field(), v) for v in V if v.degree() > 1]


# ----------------------------------------------------------------------------


def enhanced_augmentation(v0, phi, t):
    r""" Return an enhanced valuation by augmenting an inductive valuation.

    INPUT:

    - ``v0`` -- an inductive valuation
    - ``phi`` -- a key polynomial for `v_0`
    - ``t`` -- a rational number `\geq v_0(\phi)`

    OUTPUT: the augmented valuation `v = [v_0, v(\phi)=t]`, enhanced by the
    `v`-equivalence class of the key polynomial `\phi`.

    Note that if `v_(\phi)=t` then `v=v_0`.

    """
    assert v0.is_key(phi), "phi must be a key polynomial for v0"
    t0 = v0(phi)
    assert t0 <= t, "t must be >= v0(phi)"
    if t == t0:
        return EnhancedInductiveValuation(v0, phi)
    else:
        return EnhancedInductiveValuation(v0.augmentation(phi, t), phi)


class EnhancedInductiveValuation(SageObject):
    r""" A class whose objects represent inductive valutions together with
    the choice of an equivalence class of key polynomials.

    INPUT:

    - ``v`` -- an inductive valuation
    - ``phi`` -- a key polynomial for `v`

    OUTPUT: the valuation `v`, enhanced by the equivalence class of `\phi`.

    """

    def __init__(self, v, phi):
        phi = v.domain()(phi)
        assert v.is_key(phi), "phi must be a key polynomial for v"
        self._valuation = v
        self._key = phi

    def __repr__(self):
        return "{}, with equivalence class of {}".format(self.valuation(), self._key())

    def __call__(self, f):
        return self.valuation()(f)

    def valuation(self):
        return self._valuation

    def key(self):
        r""" Return a key polynomial which represents the equivalence class
        corresponding to this enhanced valuation.

        """
        return self._key

    def degree(self):
        return self.key().degree()

    def is_key(self, phi):
        return phi.degree() == self.key().degree() and self.valuation().is_equivalent(phi, self.key())

    def is_separating(self, test_for_strictly_separating=False):
        r""" Return whether this enhanced valuation is separating.

        We write `v=[v_0,v(phi)=t]` as a proper augmentation, where `\phi` is a
        distinguished key polynomial for `v`. Then `v` is called
        *separating* if the set of key polynomials for `v` which are `v`-equivalent
        to `\phi` is contained in the Krasner equivalence class of `\phi`.

        We call `v` *strictly separating* if this set is equal to the Krasner
        equivalence class of `\phi`.

        If ``test_for_strictly_separating`` is ``True`` then we return whether `v`
        is strictly separating.

        ALGORITHM: write

        .. MATH::

            \phi(x+T) = a_0(x) + a_1(x)T + \ldots + a_n(x)T^n.

        Note that `a_0=\phi`, `\deg(a_i) < \deg(\phi)` for `i>0` and `a_n=1`. So
        `v(a_0)=t`, `v(a_i)=v_0(a_i)` for `i>0` and `v(a_n)=0`. Consider the Newton
        polygon which is the lower convex hull of the points

        .. MATH::

            (1,v_0(a_1)), \ldots, (n,v_0(a_n)).

        Let `\mu` denote the first slope (note that `\mu \leq 0`). Then `\phi` is
        separating if and only if

        .. MATH:

            t = v(\phi) \geq v_0(a_1) - \mu,

        and it is strictly separating iff equality holds.


        """
        if self.degree() == 1:
            return False
        from sage.geometry.newton_polygon import NewtonPolygon
        v = self
        phi = v.key()
        n = phi.degree()
        R = phi.parent()
        x = R.gen()
        S = PolynomialRing(phi.parent(), "T")
        T = S.gen()
        F = phi(x+T)
        np = NewtonPolygon([(i, v(F[i])) for i in range(1, n+1)])
        a0 = v(phi)
        if test_for_strictly_separating:
            return a0 + np.slopes()[0] == v(F[1])
        else:
            return a0 + np.slopes()[0] >= v(F[1])

    def is_strictly_separating(self):
        r""" Return if this enhanced valuation is strictly separating.

        By definition, the enhanced valuation `v` is *strictly separating*
        if its equivalence class of key polynomials is equal to a Krasner
        equivalence class.


        """
        return self.is_separating(test_for_strictly_separating=True)

    def precursor(self):
        r""" Return the precursor of this enhanced valuation.

        The *precursor* of an enhanced valuation `v` is the maximal enhanced
        valuation `v_0` such that `v_0 < v` and `\deg(v_0) < \deg(v)`,
        or `v_0=v` if `\deg(v) = 1`.

        So if `\deg(v) > 1` then the internal representation of `v`
        *should* be of the form

        .. MATH::

            v = [v_0, v(\phi)=t],

        where `\deg(\phi) > \deg(v_0)` and `t > v_0(\phi)`. Then `v_0`, enhanced
        by the `v_0`-equivalence class of `\phi`, is the precursor of `v`.

        """
        if self.degree() == 1:
            return self
        v0 = self.valuation().augmentation_chain()[1]
        phi = self.key()
        psi = v0.equivalence_decomposition(phi)[0][0]
        assert phi.degree() > v0.phi().degree()
        return EnhancedInductiveValuation(v0, psi)

    def root(self):
        r""" Return the root of this separating enhanced valuation.

        The *root* of this enhanced valuation `v` is the (unique) strictly
        separating enhanced valuation whose equivalence class of keys contains
        the equivalence class of keys of `v`.

        If `v` is strictly separating, then we return `v` itself. If `v` is not
        separating then the root is not well defined, and an error ist returned.

        Now assume that `v` is separating, but not strictly separating. Then `v`
        is a *proper* augmentation of its base `v_0`,

        .. MATH::

            v = [v_0, v(\phi)=t_1],

        where `\phi` is a distinguished key for `v`. The root of `v` is then

        .. MATH::

            v' = [v_0, v_1(\phi)=t],

        where `t` is the smallest value in the interval `[t_0, t_1]` for which
        `v` is separating.

        """
        if self.is_strictly_separating():
            return self
        elif not self.is_separating():
            raise AssertionError("if v is not separating then the root is not well defined")
        else:
            v0 = self.precursor()
            phi = self.key()
            assert phi.degree() > 1, "the degree of phi must be > 1"
            assert v0.is_key(phi), "phi must be a key polynomial for v0"
            t = separating_value(v0, phi)
            assert t >= v0(phi), "something is wrong!"
            return enhanced_augmentation(v0.valuation(), phi, t)

    def ramification_degree(self):
        return self.root().valuation().E()

    def inertia_degree(self):
        return self.root().valuation().F()

    def base_change(self, phi):
        r""" Return the list of extension of this enhanced valuation to a finite
             extension of the base field.

        INPUT:

        - ``phi`` -- an embedding `\phi:K\to L` of the base field `K` into a
                     p-adic number field `L`

        OUTPUT: the list of all extensions of this enhanced valuation `v` to
        `L[x]`.

        """
        K = phi.domain()
        L = phi.codomain()
        v = self.valuation()
        f = self.key()
        t = v(f)
        f_L = phi.approximate_polynomial(f, t)
        assert v.domain().base_ring() == K.number_field()
        if self.degree() == 1:
            w0 = GaussValuation(f_L.parent(), L.valuation())
            return [enhanced_augmentation(w0, f_L, t)]
        else:
            v0 = self.precursor()
            W0 = v0.base_change(phi)
            W = []
            for w0 in W0:
                W += w0.all_augmentations(f_L, t)
            return W

    def all_augmentations(self, f, s):
        r""" Return the list of all augmentations of this enhanced valuation
             given by an inequality.

        INPUT:

        - ``f`` -- a polynomial, element of the domain `K[x]` of this enhanced valuation `v_0`
        - ``s`` -- a rational number, `\geq v(f)`

        OUTPUT: the list of all enhanced valuations `v` such that `v_0 \leq v`,
        `v(f)=s`, and `f` is `v`-divisible by the distinguished key of `v`.

        """
        from sage.geometry.newton_polygon import NewtonPolygon
        v0 = self.valuation()
        assert v0(f) <= s
        phi = self.key()
        t0 = v0(phi)
        v00 = v0.augmentation(phi, t0, check=False)
        valuations = list(v00.valuations(f))
        if valuations[0] <= min(valuations):
            # f is not v0-divisible by phi
            return []
        elif v0(f) == s:
            return [self]
        else:
            np = NewtonPolygon(enumerate(v00.valuations(f)))
            slopes = [mu for mu in np.slopes(repetition=False) if mu < 0]
            # this list should be nonempty if we include the possible slope -infinity
            # since `NewtonPolygon` ignores the slope -infinity, we have to add it
            if len(slopes) == 0:
                slopes = [-Infinity]
            t1 = max((s-v0(g))/i for i, g in enumerate(v00.coefficients(f)) if i > 0)
            # this is the maximal value for t_1 such that (1) holds
            t1 = min([t1, t0 - max(slopes)])
            # now t_1 is maximal with (1) and (2)
            v1 = v0.augmentation(phi, t1)
            F = v1.equivalence_decomposition(f)
            ret = []
            for psi, _ in F:
                ret += enhanced_augmentation(v1, psi, v1(psi)).all_augmentations(f, s)
            return ret


def separating_value(v0, phi):
    r""" Return the values of t such that `v=[v_0, v(\phi)=t]` is
    strictly separating.

    INPUT:

    - ``v0`` -- an inductive valuation on a polynomial ring `K[x]`
    - ``phi`` -- a key polynomial for `v_0`, of degree `\geq 2`

    OUTPUT: a rational number `t\geq v_0(\phi)` such that the augmentation

    .. MATH::

        v = [v_0, v(\phi)=t]

    is *strictly separating*. This means that the set key polynomials for `v`
    which are `v`-equivalent to `\phi` is exactly the Krasner equivalence class
    of `\phi`.

    It is possible that `t \leq v_0(\phi)`, and then the augmentation
    `v=[v_0, v(\phi)=t]` is not well defined. If this is the case, then `v_0`
    itself is already separating, and can be written as

    .. MATH::

        v_0 = [v_{-1}, v_0(\phi)=t_0],

    where `t_0\geq t`. Then `v:=[v_{-1}, v(\phi)=t]` is `\leq v_0` and
    strictly separating.

    """
    from sage.geometry.newton_polygon import NewtonPolygon
    assert phi.degree() > 1, "the degree of phi must be > 1"
    assert v0.is_key(phi), "phi must be a key polynomial for v0"
    R = phi.parent()
    x = R.gen()
    S = PolynomialRing(R, "T")
    T = S.gen()
    F = phi(x+T)
    np = NewtonPolygon([(i, v0(F[i])) for i in range(1, F.degree()+1)])
    t = v0(F[1]) - np.slopes()[0]
    # assert t >= v0(phi), "something is wrong!"
    return t
