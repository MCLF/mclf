# -*- coding: utf-8 -*-
r"""
Valuations on standard fields
=============================


"""

from sage.all import QQ
from sage.rings.valuation.valuation import DiscreteValuation
from sage.rings.valuation.mapped_valuation import MappedValuation_base
from sage.rings.valuation.valuation_space import DiscretePseudoValuationSpace


class DiscreteValuationViaIsomorphism(MappedValuation_base, DiscreteValuation):
    r""" Return a discrete valuation on a field which is given via an
    isomorphism to another discretely valued field.

    INPUT:

    - ``base_valuation`` -- a discrete valuation on a base field
    - ``to_base_domain`` -- isomorphism from the domain to the base valuation
    - ``from_base_domain`` -- the inverse isomorphism from the base valuation

    """

    def __init__(self, base_valuation, to_base_domain, from_base_domain):

        parent = DiscretePseudoValuationSpace(to_base_domain.domain())
        DiscreteValuation.__init__(self, parent)
        self._base_valuation = base_valuation
        self._map_from_base_domain = from_base_domain
        self._map_to_base_domain = to_base_domain

    def _repr_(self):
        return "discrete valuation on {} via isomorphism with {}".format(
            self.domain(), self._base_valuation.domain())

    def _to_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of ``_base_valuation``.

        """
        return self._map_to_base_domain(f)

    def _from_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of this valuation.

        """
        return self._map_from_base_domain(f)


# -----------------------------------------------------------------------------

def equivalence_of_valuations(v, w):
    r"""" Return whether two valuations on the same standard field are equivalent.

    INPUT:

    - ``v``, ``w`` -- discrete valuations on the same standard field `K`

    Here `w` should be an object of :class:`DiscreteValuation`, but `v` may be
    more general, e.g. the pull of some other valuation via a field embedding.
    Also,`w` must be nontrivial, unless the domain `K` is a finite field (in
    which case every valuation on `K` is finite).

    OUTPUT:

    whether `v` and `w` are equivalent (which means they are equal up to scaling).

    .. NOTE::

        The assumption that `w` is nontrivial is important; we don't know how to
        prove that a valuation `v` is nontrivial if we have no knowledge about its
        construction.

    EXAMPLES::

        sage: from mclf import *
        sage: v = QQ.valuation(2)
        sage: w = QQ.valuation(2)/2
        sage: equivalence_of_valuations(v, w)
        True
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x^3 - 1)
        sage: v = K.valuation(x)
        sage: W = v.extensions(L)
        sage: equivalence_of_valuations(W[0], W[1])
        False

    """
    from mclf.field_extensions.standard_field_extensions import is_standard_field
    from sage.categories.number_fields import NumberFields
    K = v.domain()
    assert w.domain() is K, "v and w must have the same domain"
    assert is_standard_field(K), "the domain of v and w must be a standard field"
    if K.is_finite():
        # any discrete valuation on a finite field is trivial
        return True
    elif K in NumberFields:
        assert not w.is_trivial(), "w must be nontrivial"
        p = w.residue_field().characteristic()
        if v(p) == 0:
            return False
        # now we know that the restriction of v and w to QQ is the p-adic valuation
        # at lest up to scaling; we compute the scaling factor:
        s = v(p)/w(p)
        #
        test_elements = test_elements_for_equivalence_of_valuations(w)
        return all([v(a) == s*w(a) for a in test_elements])
    else:
        # K must be a function field
        assert not w.is_trivial(), "w must be nontrivial"
        test_elements = test_elements_for_equivalence_of_valuations(w)
        n = len(test_elements) - 1
        from sage.schemes.projective.projective_space import ProjectiveSpace
        P = ProjectiveSpace(n, QQ)
        p1 = P([v(a) for a in test_elements])
        p2 = P([w(a) for a in test_elements])
        return p1 == p2


def test_elements_for_equivalence_of_valuations(v):
    r""" Return a list of test elements that be used to show that another discrete
    valuation is equivalent to v.

    INPUT:

    - ``v`` -- a nontrivial discrete valuation on a standard field `K`

    OUTPUT:

    a finite list of elements `a_i` of `K` with the property that for any
    valuation `w` on `K` we have that `v` and `w` are equivalent if and only
    if `v(a_i)=w(a_i)` for all `i`.

    .. NOTE::

        If `K` is an infinite field, there can be no finite set of elements of
        `K` that can detect whether some valuation is trivial. Therefore, a test
        as above can never be used to prove that a valuation is trivial.

    .. WARNING::

        This method doesn't work for the case we are really interested in:

        1. p-adic valuations of *type II* on function fields over number fields.
        For any finite set of elements of the function field, the set of all
        p-adic valuations satisfying the equalities `v(a_i)=t_i` form an
        affinoid subdomain of the corresponding Berkovich analytic space. If it
        is not empty, it contains infinitely many valuations of type II.

        2. There may be a fix for 1. if we also look at the reduction of the test
        elements to the residue field. In any case, it is not enough to look at
        the norm of a parameter for `w`. Possibly, the set of all symmetric
        invariants suffices.

    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K.<alpha> = NumberField(x^3+x+4)
        sage: L.<beta> = K.extension(x^2+alpha+1)
        sage: v = QQ.valuation(3).extensions(L)[0]
        sage: test_elements_for_equivalence_of_valuations(v)
        [3, beta + 1, beta, alpha + 1/2, alpha]

        sage: K.<x> = FunctionField(GF(2))
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2+x^3+x+1)
        sage: v = K.valuation(x+1)
        sage: w = v.extensions(L)[0]
        sage: test_elements_for_equivalence_of_valuations(w)
        [0, y + x, y, x + 1]

        sage: K.<x> = FunctionField(QQ)
        sage: v0 = K.valuation(GaussValuation(K._ring, QQ.valuation(2)))
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^3 + x^3 + 2)
        sage: v = v0.extensions(L)[0]
        sage: test_elements_for_equivalence_of_valuations(v)
        [y + x, y, 2, x]

    """
    from mclf.field_extensions.standard_field_extensions import is_standard_field
    from sage.categories.number_fields import NumberFields
    assert not v.is_trivial(), "v must not be trivial"
    K = v.domain()
    assert is_standard_field(K), "K must be a standard field"
    if K.is_finite():
        # all valuations on a finite field are trivial, hence equivalent
        return []
    elif K in NumberFields:
        p = v.residue_field().characteristic()
        test_elements = [p]
        while K is not QQ:
            v0 = v._base_valuation
            if hasattr(v0, "_approximation"):
                v0 = v0._approximation
            for v1 in v0.augmentation_chain():
                test_elements.append(K(v1.phi()))
            K = K.base_field()
            v = v.restriction(K)
        return test_elements
    else:
        # now K is a function field
        K0 = K.rational_function_field()
        test_elements = []
        while K is not K0:
            v0 = v._base_valuation
            if hasattr(v0, "_approximation"):
                v0 = v0._approximation
            for v1 in v0.augmentation_chain():
                test_elements.append(K(v1.phi()))
            K = K.base_field()
            v = v.restriction(K)
        # now K is a rational function field
        k = K.constant_base_field()
        if not k.is_finite():
            p = v.residue_field().characteristic()
            if p > 0:
                # now v is p-adic
                test_elements.append(p)
                f = v.lift(v.residue_field().gen())
                for g, _ in f.factor():
                    test_elements.append(g)
                return test_elements
        # now v is a function field valuation
        x = K.gen()
        if v(x) != 0:
            test_elements.append(x)
            return test_elements
        else:
            test_elements.append(K(v._base_valuation.phi()))
            return test_elements


def restriction_of_valuation(phi, w):
    r""" Return the restriction of the valuation w along the embedding phi.

    INPUT:

    - ``phi`` -- an embedding of standard fields `\phi:K\to L`
    - ``w`` -- a discrete valuation on `L`

    Alternatively, the embedding `\phi` may also be given as an object of the
    class :class:`StandardFiniteFieldExtension`.

    OUTPUT:

    the discrete valuation `v` on `K` which is defined as the map `v:=w\circ\phi`.

    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(3)
        sage: K.<x> = FunctionField(k)
        sage: w = K.valuation(x)
        sage: phi = k.hom(K)
        sage: restriction_of_valuation(phi, w)
        Trivial valuation on Finite Field of size 3

        sage: phi = K.hom([x^2+x+1])
        sage: restriction_of_valuation(phi, w)
        (x + 2)-adic valuation

        sage: R.<x> = QQ[]
        sage: K.<alpha> = NumberField(x^4+1)
        sage: w = QQ.valuation(3).extensions(K)[0]
        sage: w
        [ 3-adic valuation, v(x^2 + 2*x + 2) = 1 ]-adic valuation
        sage: phi = K.hom([-alpha^3])
        sage: v = restriction_of_valuation(phi, w)
        sage: v
        [ 3-adic valuation, v(x^2 + x + 2) = 1 ]-adic valuation
        sage: equivalence_of_valuations(v, w)
        False

        sage: F.<z> = FunctionField(K)
        sage: u0 = GaussValuation(F._ring, w).augmentation(F._ring.gen(), 1)
        sage: u = F.valuation(u0)
        sage: phi = F.hom([alpha/z])
        sage: restriction_of_valuation(phi, u)


    """
    from mclf.field_extensions.standard_field_extensions import (
        is_standard_field, StandardFiniteFieldExtension)
    from sage.rings.valuation.trivial_valuation import TrivialValuation
    from sage.categories.number_fields import NumberFields
    from sage.rings.rational_field import QQ
    if isinstance(phi, StandardFiniteFieldExtension):
        return restriction_of_valuation_along_finite_extension(phi, w)
    K = phi.domain()
    assert is_standard_field(K), "K must be a standard field"
    v = phi.post_compose(w)
    if K.is_finite():
        return TrivialValuation(K)
    elif K in NumberFields:
        p = w.residue_field().characteristic()
        v_p = QQ.valuation(p)
        if K is QQ:
            return v_p
        else:
            V = v_p.extensions(K)
            for v1 in V:
                if equivalence_of_valuations(v, v1):
                    return v1
            # if we get here, something went wrong
            raise AssertionError("The correct extension of v_p could not be found")
    else:
        # now K must be a function field, and L must be a finite extension of K
        K0 = K.rational_function_field()
        phi0 = K0.hom(K).post_compose(phi)
        v0 = restriction_of_valuation_to_rational_function_field(phi0, w)
        V = v0.extensions(K)
        for v1 in V:
            if equivalence_of_valuations(v, v1):
                return v1
        # if we get here, something went wrong
        raise AssertionError()


def restriction_of_valuation_to_rational_function_field(phi, w):
    r""" Return the restriction of the valuation w along the embedding phi.

    INPUT:

    - ``phi`` -- an embedding of standard function fields `\phi:K\to L`,
                 where `K=k(x)` is a rational function field
    - ``w`` -- a discrete valuation on `L`

    OUTPUT:

    the discrete valuation `v` on `K` which is defined as the map `v:=w\circ\phi`,
    as an object of :class:`DiscreteValuation`.


    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(QQ)
        sage: w = K.valuation(GaussValuation(K._ring, QQ.valuation(2)))
        sage: phi = K.hom([2*(x^2+2)/x/(2*x+1)])
        sage: restriction_of_valuation_to_rational_function_field(phi, w)

    """

    from mclf.field_extensions.standard_field_extensions import standard_field_extension
    K = phi.domain()
    v = phi.post_compose(w)
    # first we compute the restriction of v to the constant base field
    k = K.constant_base_field()
    phi_k = k.hom(K).post_compose(phi)
    v_k = restriction_of_valuation(phi_k, w)
    assert K is K.rational_function_field()
    L_K = standard_field_extension(K.hom(K).post_compose(phi))

    if v_k.is_trivial():
        # we are looking for a function field valuation on k(x); it is
        # uniquely determined by an irreducible polynomial g (or g=1/x)
        # such that v(g) > 0
        f = L_K.norm(w.uniformizer())
        for g, _ in f.factor():
            if v(g) > 0:
                return K.valuation(g)
        assert v(K.gen()) < 0, "something went wrong: no prime element found"
        return K.valuation(1/K.gen())
    else:
        # now k is a number field and v_k a p-adic valuation
        on_unit_disk = (v(K.gen()) >= 0)
        f = L_K.norm(w.lift(w.residue_field().gen()))
        V = []
        for g, _ in f.factor():
            t = v(g)
            V_g = valuations_on_rational_function_field(v_k, g, t, on_unit_disk)
            assert all([v1(g) == t for v1 in V_g])
            print(V_g)
            V += V_g
        for v1 in V:
            if equivalence_of_valuations(v, v1):
                return v1
        # if we get here, something has gone wrong
        raise AssertionError()


def valuations_on_rational_function_field(v_k, f, t, on_unit_disk):
    r""" Return the list of discrete valuations on a rational function field
    satisfying certain conditions.

    INPUT:

    - ``v_k`` -- a discrete valuation on a field `k`
    - ``f`` -- a nonconstant element of a rational function field `K=k(x)` over `k`
    - ``t`` -- a rational number
    - ``on_unit_disk`` -- a boolean

    OUTPUT:

    the (finite) list of all discrete valuations `v` on `K` such that:

    1. `v|_k = v_k`,
    2. `v(f) = t`,
    3. `v(x) \geq 0` if and only if ``on_unit_disk`` is ``True``,
    3. `f` is not a `v`-unit wrt. the parameter `x` (replace `x` by `1/x`
        if `v(x) < 0`).

    EXAMPLES::

        sage: from mclf import *
        sage: K.<x> = FunctionField(QQ)
        sage: v_3 = QQ.valuation(3)
        sage: valuations_on_rational_function_field(v_3, x, 1, True)
        [Valuation on rational function field induced by [ Gauss valuation
         induced by 3-adic valuation, v(x) = 1 ]]
        sage: valuations_on_rational_function_field(v_3, x, 1, False)
        []
        sage: valuations_on_rational_function_field(v_3, (3*x-1)*x, 2, False)
        [Valuation on rational function field induced by [ Gauss valuation
         induced by 3-adic valuation, v(x - 3) = 4 ] (in Rational function field
         in x over Rational Field after x |--> 1/x)]

    """
    from mclf.berkovich.berkovich_line import BerkovichLine
    K = f.parent()

    # the following doesn't work when v_k is not the unique p-adic extension
    # on k; there is also a problem when f is not a polynomial in x or 1/x:
    X = BerkovichLine(K, v_k)
    points = X.points_from_inequality(f, t)
    return [xi.valuation() for xi in points if on_unit_disk == xi.is_in_unit_disk()]


def restriction_of_valuation_along_finite_extension(L_K, w):
    r""" Return the restriction of the valuation w along the embedding phi.

    INPUT:

    - ``L_K`` -- a finite extension of standard fields `L/K`
    - ``w`` -- a discrete valuation on `L`


    OUTPUT:

    the discrete valuation `v` on `K` which is defined as the map `v:=w|_K`.

    """
    raise NotImplementedError()
