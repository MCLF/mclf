# -*- coding: utf-8 -*-
r"""
Discrete valuations on function fields
======================================

In this module we implement the class :class:`DiscreteValuationOnFunctionField`,
and various subclasses. Its objects represent *nontrivial* discrete valuations
on a standard function field.

Recall that a standard function field `F` has a canonical representation
as a finite extension of a subfield `F_0\subset F`, where `F_0=k(x)` is a
*rational function field* over a standard field `k`, which is either finite or
a number field. We call `k` the *constant base field* and `F_0` the *rational
base field* of `F`. The sequence of subfields

.. MATH::

    k\subset F_0\subset F

is part of the canonical structure of `F` as a standard field.

If `F=F_0` then we say that `F` is a *rational function field*; otherwise
we say that `F` is a *nonrational* function field.

If `v` is a nontrivial discrete valutions


Function field valuations
-------------------------


`p`-adic valuations on function fields
--------------------------------------



AUTHORS:

- Stefan Wewers (2021): initial version



"""


from mclf.valuations.discrete_valuations import DiscreteValuationOnStandardField


def discrete_valuation_on_function_field(v):
    r""" Return the discrete valuation object.

    INPUT:

    ``v`` -- a discrete valuation on a function field

    OUTPUT:

    the object of :class:`DiscreteValuationOnFunctionField`
    corresponding to `v`.

    """
    raise NotImplementedError()


class DiscreteValuationOnFunctionField(DiscreteValuationOnStandardField):
    r""" Base class for discrete valuations on function fields.


    """


class DiscreteValuationOnRationalFunctionField(
        DiscreteValuationOnFunctionField):
    r""" A class for discrete valuations on a rational function field.

    """

    def is_equivalent_to(self, w):
        r""" Return whether this valuation is equvalent to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v`

        OUTPUT:

        whether `v = w`.

        This method must be implemented by the two primitive subclasses:

        - :class:`FunctionFieldValuationOnRationalFunctionField` and
        - :class:`pAdicValuationOnRationalFunctionField`.

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        raise NotImplementedError()


class DiscreteValuationOnNonrationalFunctionField(
        DiscreteValuationOnFunctionField):
    r""" Discrete valuation on a nonrational function field.


    """

    def is_equivalent_to(self, w):
        r""" Return whether this valuation is equal to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v`

        OUTPUT:

        whether `v` and `w` are equivalent (i.e. equal up to a scaling factor).

        ALGORITHM:

        Let `F` be the domain of `v`. Then `F` is naturally a finite extension
        of its *rational base field* `F_0=k(x)`.

        In the first step, we test whether the restrictions of `v` and `w` to
        `F_0` are equivalent. This step is implemented by the class
        :class:`DiscreteValuationOnRationalFunctionField`.

        Assuming that `v_0:=v|_{F_0}` and `w_0:=w_{F_0}` ar equivalent, it
        suffices to decide whether `w` is equivalent to one of the finitely
        many extensions of `v_0` to `F`. These finitely many extensions can be
        computed with MacLane's algorithm. A side effect of this algorithm
        (more precisely, the representation of an extension as an *inductive
        valuation*) furnishes a list `f_1,..,f_n\in F^\times` of *test elements*
        with the property that `v` and `w` are equivalent if and only if

        1. the restrictions `v_0` and `w_0` are equivalent, and
        2. the tuples `(v(f_1),\ldots,v(f_n))` and `(w(f_1),\ldots,w(f_n))`
           are projectively equivalent, i.e. agree up to a common scaling
           factor.

        A list of such elements is computed with the method
        :meth:`test_values <DiscreteValuationOnNonrationalFunctionField.\
        test_values>`

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        v0 = v.rational_base_valuation()
        w0 = w.rational_base_valuation()
        s = v.min_value()/w.min_value()
        if v0.is_equivalent(w0):
            return all(s*w(f) == t for f, t in v.test_values())
        else:
            # the restrictions to the rational base field are not equivalent
            return False

    def test_values(self):
        r""" Return a list of test values to test equivalence of this discrete
        valuation with another.

        OUTPUT:

        a list of pairs `(f_i, t_i)`, with `f_i` nonzero elements of the
        domain of this valuation `v`, the function field `F`, and
        `t_i\in\mathbb{Q}`, such that the following holds:

            If `w` is another discrete valuation on `F`, then `v` and `w` are
            equivalent if and only if

            - the restrictions on `v` on `w` to the rational base field of
              `F` are equivalent, and
            - we have `w(f_i) = s\cdot t_i`, where `s` is the ratio between `v`
              and `w`, i.e. such that `\Gamma_w = s\cdot\Gamma_v`.

        ALGORITHM:

        Let `v` denote this valuation, `F` its domain, `F_0\subset F` the
        rational base field and `v_0:=v|_{F_0}` the restriction of `v` to `F_0`.
        By construction, `F` has a presentation of a quotient of a polynomial
        ring over `F_0`,

        .. MATH::

            F = F_0[y]/(G),

        where `G` is an irreducible polynomial. We can thus identify discrete
        valuations on `F` with discrete *pseudo-valuations* on `F_0[y]` which
        take the value `\infty` on `G`.

        Let us assume that for our valuation `v` we have `v(y)\geq 0`. Then
        MacLane's theory lets us write such a pseudo-valuation quite explicitly
        in one of two ways: either as an *inductive pseudovaluation*, or as
        a *limit valuation*.

        In the first case we can write `v` as

        .. MATH::

            v = [v_0, v_1(\phi_1)=\lambda_1,\ldots,v_n(\phi_n)=\infty],

        for certain irreducible monic polynomiales `\phi_i` (the
        *key polynomials*), and where `\phi_n=G` and we identify the restriction
        `v_0` of `v` to `F_0` with its Gauss valuation on `F_0[y]`.

        Implicit in this presentation is the claim that the extension `v` of
        `v_0` is determined by the equalities

        .. MATH::

            v(\phi_i) = \lambda_i, \quad i=1,\ldots,n.

        As the last equality `v(\phi_n)=v(G)=\infty` is automatic, we can use
        the images of the key polynomials `\phi_1,\ldots,\phi_{n-1}` in `F`
        as our test elements.

        In the second case, we can write `v` as a limit of an inductive
        sequence f valuations,

        .. MATH::

            v = \lim_n v_n,

        where `v_0` is again the Gauss valuation and for `i>0`

        .. MATH::

            v_i = [v_{i-1}, v_i(\phi_i)=\lambda_i]

        is a *proper augmentation* of `v_{i-1}`.

        tbc.

        """
        if not hasattr(self, "test_values"):

            # this will probably not work quite right: the Sage valuation
            # v representing this valuation has to be the correct one,
            # adapted to the choice of the right parameter

            F = self.Domain()
            v = self.sage_valuation()
            test_elements = []
            v0 = v._base_valuation
            if hasattr(v0, "_approximation"):
                v0 = v0._approximation
            for v1 in v0.augmentation_chain():
                test_elements.append(F(v1.phi()))
            self._test_values = [(f, self(f)) for f in test_elements()]
        return self._test_values

# --------------------------------------------------------------------------

#               function field valuations


class FunctionFieldValuation(DiscreteValuationOnFunctionField):
    r""" Base class for function field valuations.

    A **function field valuation** is a discrete, normalized valuation on
    a function fields which is trivial on the constant base base field.

    """


class FunctionFieldValuationOnRationalFunctionField(
        FunctionFieldValuation, DiscreteValuationOnRationalFunctionField):
    r""" The class for function field valuations on a rational function field.


    """


class FunctionFieldValuationOnNonrationalFunctionField(
        FunctionFieldValuation, DiscreteValuationOnNonrationalFunctionField):
    r""" The class for function field valuations on a nonrational
    function field.


    """


# --------------------------------------------------------------------------

#          p-adic valuations on function fields


class pAdicValuationOnFunctionField(DiscreteValuationOnFunctionField):
    r""" A class for `p`-adic valuations on function fields.

    Let `F` be a standard function field, with constant base field `k`.
    A **`p`-adic valuation** on `F` is a discrete valuation `v` whose
    restriction to `k` is `p`-adic. The latter means that `k` is a number
    field and that there exists a unique prime number `p` with `v(p)>0`.


    """


class pAdicValuationOnRationalFunctionField(
        DiscreteValuationOnRationalFunctionField,
        pAdicValuationOnFunctionField):
    r""" A class for p-adic valuations on rational function fields.

    """


class pAdicValuationOnNonrationalFunctionField(
        DiscreteValuationOnNonrationalFunctionField,
        pAdicValuationOnFunctionField):
    r""" A class for p-adic valuations on nonrational function fields.

    """

# ----------------------------------------------------------------------------

#                    helper functions


def padic_valuations_on_rational_function_field(F, v_k, f, t, on_unit_disk):
    r""" Return the list of discrete valuations on a rational function field
    satisfying certain conditions.

    INPUT:

    - ``F`` -- a rational function field over a number field
    - ``v_k`` -- a discrete valuation on the constant base field `k` of `F`
    - ``f`` -- a nonconstant element of `F`
    - ``t`` -- a rational number
    - ``on_unit_disk`` -- a boolean

    OUTPUT:

    the (finite) list of all discrete valuations `v` on `F` such that:

    1. `v|_k = v_k`,
    2. `v(x) \geq 0` if and only if ``on_unit_disk`` is ``True``,
    3. `v(f) = t`,
    4. `f` is not a `v`-unit wrt. the parameter `x` (replace `x` by `1/x`
        if `v(x) < 0`).

    ALGORITHM:

        Let us first assume that ``on_unit_disk`` is ``True``. Then a valuation
        `v` with the desired properties is induced from a discrete valuation
        on the polynomial ring `R=k[x]`, the subring of `F` generated over `k`
        by the canonical generator `x` of `F/k`. By MacLane's theory, `v` can
        be represented as an inductive valuation of the form

        .. MATH::

            v = [v_0,v_1(\phi_1)=\lambda_1,\ldots,v_n(\phi_n)=\lambda_n],

        where `v_0` is the Gauss valuation with respect to `v_k`.

        There are now finitely many valuations `v` satisfying the additional
        conditions 3. and 4.; they can be determined with a variant of MacLane's
        algorithm, as follows:

        todo


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
    raise NotImplementedError()

    # this is the old code:

    # from mclf.berkovich.berkovich_line import BerkovichLine
    # K = f.parent()

    # the following doesn't work when v_k is not the unique p-adic extension
    # on k; there is also a problem when f is not a polynomial in x or 1/x:
    # X = BerkovichLine(K, v_k)
    # points = X.points_from_inequality(f, t)
    # return [xi.valuation() for xi in points if on_unit_disk == xi.is_in_unit_disk()]
