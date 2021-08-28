# -*- coding: utf-8 -*-
r"""
p-adic valuations on function fields
====================================





AUTHORS:

- Stefan Wewers (2021): initial version



"""


from mclf.valuations.discrete_valuations_on_function_fields import (
    DiscreteValuationOnFunctionField, DiscreteValuationOnRationalFunctionField,
    DiscreteValuationOnNonrationalFunctionField)


class pAdicValuationOnFunctionField(DiscreteValuationOnFunctionField):
    r""" A class for `p`-adic valuations on function fields.

    Let `F` be a standard function field, with constant base field `k`.
    A **p-adic valuation** on `F` is a discrete valuation `v` whose
    restriction to `k` is `p`-adic. The latter means that `k` is a number
    field and that there exists a unique prime number `p` with `v(p)>0`.

    """

    def is_equivalent_to(self, w):
        r""" Return whether this valuation is equivalent to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v`

        OUTPUT:

        whether `v` and `w` are equivalent.

        Since we assume that all `p`-adic valuations are `p`-adically
        normalized, `v` and `w` are equivalent if and only if they are equal.
        And this is the case if and only if their discoid representations
        are equal.

        .. TODO::

            Explain how to check this, somewhere, in more detail.

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        phi, r = v.discoid_representation()
        psi, s = w.discoid_representation()
        return v(psi) == s and w(phi) == r

    def discoid_representation(self):
        r""" Return the representation of this p-adic valuation in terms of
        its discoid.

        OUTPUT:

        a pair `(f, t)`, where `f \in K=k(x)` is either a `p`-adically
        irreducible, monic polynomial in `x`, or is equal to `1/x`, and where
        `t\geq 0` is a nonnegative ratinal number.

        The pair `(f, t)` is a concrete description of the *discoid* on the
        Berkovich projective line corresponding to this valuation `v`, via

        .. MATH::

            D_v = \{ \xi \mid v_\xi(f) \geq t \}.

        """
        raise NotImplementedError()


class pAdicValuationOnRationalFunctionField(
        DiscreteValuationOnRationalFunctionField,
        pAdicValuationOnFunctionField):
    r""" A class for p-adic valuations on rational function fields.

    INPUT:

    - `F` - - a standard rational function field over a number field `k`
    - `v` - - a `p`- adic valuation on the standard model of `F`

    OUTPUT:

    the object representing `v`.

    Let `F = k(x)` be a rational function field over a number field `k`, and
    let `v` be a `p`-adic valuation on `F`. We call `v` **integral** if
    `v(x) \geq 0`; otherwise we call `v` **nonintegral**.

    Let `v` be integral and let `v_k: = v | _k` denote the restriction of `v` to
    the constant base field. The valuation `v` is uniquely determined by its
    restriction to the subring `R: = k[x]\subset F`, which we call the *standard
    order* of `F`. By MacLane's theory, the restriction of `v` to `R` has a
    description as an *inductive valuation*, like so:

    .. MATH::

        v = [v_0, v_1(\phi_1) = t_1, \ldots, v_n(\phi_n) = t_n],

    where

    - `v_0` is the Gauss valuation with respect to `v_k` and the parameter `x`,
    - `\phi_i\in R` are certain monic, integral and irreducible polynomials,
      the * key polynomials*,
    - `t_i\geq 0` are rational numbers, contained in the value group of `v`.

    If `v` is given to us as a Sage valuation, this description is directly
    available, via the method :meth:`augmentation_chain`.

    A crucial fact is that the `p`-adic valuation `v` is already uniquely
    determined by the data `(v_k, \phi_n, t_n)`. A bit more precisely, `v` is
    the "minimal" `p`-adic integral valuation on `R` such that

    .. MATH::

        v|_k = v_k \quad\text{ and }\quad v(\phi_n) = t_n.

    If `v` is not integral, then we replace the order `R = k[x]` by the
    **inverse order** `R': = R[1/x]`, and we have essentially the same
    description of the restriction of `v` to `R'` as above.

    """

    def __init__(self, F, v):
        raise NotImplementedError()


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

    - ``F`` - - a rational function field over a number field
    - ``v_k`` - - a discrete valuation on the constant base field `k` of `F`
    - ``f`` - - a nonconstant element of `F`
    - ``t`` - - a rational number
    - ``on_unit_disk`` - - a boolean

    OUTPUT:

    the(finite) list of all discrete valuations `v` on `F` such that:

    1. `v | _k = v_k`,
    2. `v(x) \geq 0` if and only if ``on_unit_disk`` is ``True``,
    3. `v(f) = t`,
    4. `f` is not a `v`- unit wrt. the parameter `x` (replace `x` by `1/x`
        if `v(x) < 0`).

    ALGORITHM:

        Let us first assume that ``on_unit_disk`` is ``True``. Then a valuation
        `v` with the desired properties is induced from a discrete valuation
        on the polynomial ring `R = k[x]`, the subring of `F` generated over `k`
        by the canonical generator `x` of `F/k`. By MacLane's theory, `v` can
        be represented as an inductive valuation of the form

        .. MATH::

            v = [v_0, v_1(\phi_1)=\lambda_1, \ldots, v_n(\phi_n) =\lambda_n],

        where `v_0` is the Gauss valuation with respect to `v_k`.

        There are now finitely many valuations `v` satisfying the additional
        conditions 3. and 4.; they can be determined with a variant of MacLane's
        algorithm, as follows:

        todo

    EXAMPLES::

        sage: from mclf import *
        sage: K. < x > = FunctionField(QQ)
        sage: v_3 = QQ.valuation(3)
        sage: valuations_on_rational_function_field(v_3, x, 1, True)
        [Valuation on rational function field induced by[Gauss valuation
         induced by 3-adic valuation, v(x)= 1]]
        sage: valuations_on_rational_function_field(v_3, x, 1, False)
        []
        sage: valuations_on_rational_function_field(v_3, (3*x-1)*x, 2, False)
        [Valuation on rational function field induced by[Gauss valuation
         induced by 3-adic valuation, v(x - 3) = 4 ] (in Rational function field
         in x over Rational Field after x | - -> 1/x)]

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
