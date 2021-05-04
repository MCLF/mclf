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
coefficients in `K_0`, its irreducible factors havn't, in general. Fortunately,
by Krasner's Lemma, it suffices to work with sufficiently good approximations
of the irreducible factors of `f`, and these can be chosen in `K_0[x]`.

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
from sage.rings.valuation.limit_valuation import LimitValuation
from mclf.padic_extensions.padic_number_fields import pAdicNumberField
from mclf.padic_extensions.fake_padic_embeddings import FakepAdicEmbedding
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
    approximation `\geq v_0` are retuned.

    An *approximate irreducible factor* is a Krasner equivalence class of monic,
    integral and irreducible polynomials `g` which are *approximate prime factors*
    of `f` in the following sense: for every root `\alpha` of `g` there exists
    a root `\beta` of `f` which is strictly closer to `\alpha` than all other
    roots of `g`.

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

    from sage.geometry.newton_polygon import NewtonPolygon
    F = v0.equivalence_decomposition(f)
    ret = []
    for phi, _ in F:
        t0 = v0(phi)
        v00 = v0.augmentation(phi, t0, check=False)
        valuations = list(v00.valuations(f))
        a = min(valuations)
        n = min(i for i in range(len(valuations)) if valuations[i] == a)
        # n is the degree of f with respect to v00
        np = NewtonPolygon(enumerate(valuations))
        slopes = [mu for mu in np.slopes(repetition=False) if mu < 0]
        if len(slopes) == 0:
            t1 = Infinity
        else:
            t1 = t0 - max(slopes)
        # we have to see if there are separating valuation v = [v0, v(phi)=t]
        # with t0 < t <= t1
        if phi.degree() > 1:
            t = separating_value(v0, phi)
            if t >= t0 and t < t1:
                g = ApproximatePrimeFactor(K, v0.augmentation(phi, t, check=False))
                ret.append(g)
        if n > 1 and t1 < Infinity or phi.degree() > 1 and t1 < Infinity and t >= t1:
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
    3. a separating inductive valuation on `K[x]`

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

    Let `v = [v_0,v(\phi)=t]` be an inductive valuation, which is an
    augmentation of `v_0` with key polynomial `\phi`. We call `v` *separating*
    if the set of key polynomials for `v` which are `v`-equivalent to `\phi`
    is exactly the Krasner equivalence class of `\phi`. We note that `v` is
    uniquely determined by the equivalence class of `\phi`. Conversely, `v`
    uniquely determines the class of `\phi` if `v` is a proper augmentation of
    `v_0`, i.e. if `t > v_0(\phi)`. Since `v` is internally represented as an
    augmentation and thus equipped with a representative `\phi` (via the
    method :meth:`phi`), the input (3) defines a Krasner equivalence class as
    well.

    """

    def __init__(self, K, f):
        from sage.rings.polynomial.polynomial_element import Polynomial
        assert isinstance(K, pAdicNumberField)
        self._base_field = K
        if isinstance(f, Polynomial):
            f = f.change_ring(K.number_field())
            assert f.is_monic(), "f must be monic"
            v0 = GaussValuation(f.parent(), K.valuation())
            assert v0(f) >= 0, "f must be integral"
            V = v0.mac_lane_step(f)
            assert len(V) == 1, "f must be irreducible"
            self._pseudo_valuation = LimitValuation(V[0], f)
            self._approximate_polynomial = f
            self._polynomial_ring = f.parent()
        elif f.is_discrete_valuation():
            v = f
            assert is_separating(v), "v must be separating"
            self._approximate_polynomial = v.phi()
            self._polynomial_ring = v.domain()
            # we want to find the predecessor which is strictly separating
            v0 = v.augmentation_chain()[1]
            phi = v.phi()
            t = separating_value(v0, phi)
            self._separating_valuation = v0.augmentation(phi, t, check=False)
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

    def separating_valuation(self):
        if not hasattr(self, "_separating_valuation"):
            raise NotImplementedError()
        return self._separating_valuation

    def approximate_polynomial(self):
        if not hasattr(self, "_approximate_polynomial"):
            self._approximate_polynomial = self.separating_valuation().phi()
        return self._approximate_polynomial

    def degree(self):
        return self.approximate_polynomial().degree()

    def ramification_degree(self):
        return self.separating_valuation().E()

    def is_unramified(self):
        return self.ramification_degree().is_one()

    def is_tamely_ramified(self):
        p = self.base_field().p()
        return not p.divides(self.ramification_degree())

    def inertia_degree(self):
        return self.separating_valuation().F()

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

        """
        V = extensions_of_inductive_valuation(self.separating_valuation(), L.embedding())
        return [ApproximatePrimeFactor(L.extension_field(), v) for v in V if v.phi().degree() > 1]


# -----------------------------------------------------------------------------

def is_separating(v, test_for_strictly_separating=False):
    r""" Return whether the inductive valuation is separating.

    INPUT:

    - ``v`` -- an inductive valuation on a polynomial ring `K[x]`

    We assume that the restriction of `v` to the base field `K` is nontrivial.

    OUTPUT: whether `v` is *separating*, in the following sense:

    We write `v=[v_0,v(phi)=t]` as a proper augmentation. Then `v` is called
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
    from sage.geometry.newton_polygon import NewtonPolygon
    phi = v.phi()
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

# -----------------------------------------------------------------------------


def extensions_of_inductive_valuation(v, phi):
    r""" Return all extensions of an inductive valuation to the base change.

    INPUT:

    - ``v`` -- an inductive valuation on a polynomial ring `K[x]`
    - ``phi`` -- an embedding `\phi:K\to L` of fake p-adic number fields

    Here `v` must be defined over `K_0`, the number field underlying `K`.

    OUTPUT: the list of all extensions of `v` to `L[x]`.

    ALGORITHM:

    If `v` is the Gauss valuation on `K[x]`, then it has a unique extension
    to `L[x]`, namely the Gauss valuation.

    Otherwise, `v` is an augmentation of the form

    .. MATH::

        v = [v_0, v(f)=\mu].

    Then any extension of `v` to `L[x]` is of the form

    .. MATH::

        w = [w_0, w_1(g_1)=\mu_1,\ldots,w_n(g_n)=\mu_n],

    with `n>0`, `w_0` an extension of `v_0` to `L[x]`. By induction, we may
    assume that we know all possibilities for `w_0`.

    The valuations `w` we are looking for are then exactly the inductive
    valuations on `L[x]` with the following properties:

    1. `w_0\leq w`
    2. `w(f) = \mu`
    3. `f` is not an equivalence unit with respect to `w`

    We can compute these inductive valuations with a variant of MacLane's
    algorithm. This is done by the helper function :func:`_all_augmentations`.

    """
    K = phi.domain()
    L = phi.codomain()
    assert v.domain().base_ring() == K.number_field()
    if v.is_gauss_valuation():
        return [GaussValuation(v.domain().change_ring(L.number_field()), L.valuation())]
    else:
        v0 = v.augmentation_chain()[1]
        W0 = extensions_of_inductive_valuation(v0, phi)
        W = []
        for w0 in W0:
            W += extensions_of_augmented_valuation(v, w0, phi)
        return W


def extensions_of_augmented_valuation(v, w0, phi):
    r""" Return all extensions of an inductive valuation to the base change.

    INPUT:

    - ``v`` -- an augmented valuation on a polynomial ring `K[x]`
    - ``w0`` -- an inductive valuation on `L[x]`
    - ``phi`` -- an embedding `\phi:K\to L` of p-adic number fields

    Here `v` must be an augmentation of the restriction `v_0` of `w_0` to `K[x]`.

    OUTPUT: the list of all extensions `w` of `v` to `L[x]` such that `w_0\leq w`.

    """
    K = phi.domain()
    L = phi.codomain()
    assert v.domain().base_ring() == K.number_field()
    assert w0.domain().base_ring() == L.number_field()
    f = v.phi()
    s = v(f)
    # so v = [v_0, v(f)=s]
    # note that s=infty is possible!
    # then the following command runs into an infinite loop!
    f0 = phi.approximate_polynomial(f, s)
    assert w0(f0) <= s
    return _all_augmentations(w0, f0, s)


# ----------------------------------------------------------------------------


def _all_augmentations(v0, f, s):
    r""" Return all augmentations of `v_0` corresponding to an inequality.

    INPUT:

    - ``v0`` -- an inductive valuation on `K[x]`
    - ``f`` -- a monic integral polynomial in `K[x]`
    - ``s`` -- a positive rational number

    OUTPUT:

    the list of all inductive valuations `v \geq v0` corresponding to the
    irreducible components of the affinoid given by `v(f) \geq s`.

    These are precisely the augmentations `v` of `v_0` such that

    - `v(f) = s`, and

    - `f` is not an equivalence unit of `v`

    ALGORITHM:

    This is a variant of MacLane's algorithm for developping inductive
    valuations, see ??.

    If `v_0(f) > s` or if `v_0(f) = s` and `f` is an equivalence unit for `v`
    then no `v` with the required property exists. If `v_0(f) = s` and if `f`
    is not an equivalence unit, then `v=v_0` is the only solution.

    Therefore, we may assume that `v_0(f) < s` and that `f` is not an equivalence
    unit. Then any solution `v` is of the form

    .. MATH::

        v = [v_0, v_1(\phi_1)=t_1,\ldots, v_n(\phi_n)=t_n],

    with `n>0`. Moreover, for every `i>0`, we may assume that

    - `\phi_i` is a irreducible factor of a `v_{i-1}`-equivalence decomposition
      of `f`,
    - t_i > v_{i-1}(\phi_i)` is maximal with the property that `v_i(f)\leq s`
      and that `f` is not an equivalence unit for `v_i`.

    By induction, it suffices to find, for every factor `\phi` in a `v_0`-equivalence
    decomposition of `f`, the maximal value of `t_1 > t_0:=v_0(\phi)` such that
    the augmentation

    .. MATH::

         v_1:=[v_0, v_1(\phi)=t_1]

    has the property that

    1. `v_1(\phi) \leq s`, and

    2. `f` is not a `v_0`-equivalence unit.

    To determine the value of `t_1`, we consider the `\phi`-development of `f`,

    .. MATH::

        f = f_0 + f_1\phi + \ldots + f_r\phi^r.

    Then (1) holds if and only if there exists an index `i` such that

    .. MATH::

        v_0(f_i) + i t_1 \leq s.

    Furthermore, (2) holds if and only if

    .. MATH::

        t_1 \leq t_0 - \mu,

    where `\mu` is the largest negative slope of the Newton polygon of the
    `\phi`-development of `f` with respect to `v_0`.

    This makes it easy to compute `t_1`.

    """
    from sage.geometry.newton_polygon import NewtonPolygon
    assert v0(f) <= s
    if v0(f) == s:
        if v0.is_equivalence_unit(f):
            return []
        else:
            ret = []
            for phi, _ in v0.equivalence_decomposition(f):
                ret.append(v0.augmentation(phi, v0(phi), check=False))
            return ret
    # we should return a nonempty list of true augmentations of v0
    F = v0.equivalence_decomposition(f)
    ret = []
    for phi, _ in F:
        t0 = v0(phi)
        v00 = v0.augmentation(phi, t0, check=False)
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
        v1 = v0.augmentation(phi, t1, check=False)
        ret += _all_augmentations(v1, f, s)
    return ret
