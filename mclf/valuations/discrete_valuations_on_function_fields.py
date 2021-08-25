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

Let `v` be a nontrivial discrete valuation on `F`. Then we obtain two further
discrete valuations:

- the restriction `v_0:=v|_{F_0}` of `v` to the rational base field `F_0`,
- the restriction `v_k:=v|_k` to the constant base field.

Since `F/F_0` is finite, the valuation `v_0` will be nontrivial as well. It
plays a crucial role for the explicit description of `v`.

The field of constant valuation `v_k` may be trivial; in this case we call `v`
a *place*. If it is nontrivial, then `k` must be a number
field and `v_k` a `p`-adic valuation. Then `v` is `p`-adic as well.

Places
------

A discrete valuation `v` on a function field `F/k` is called a **place** if the
restriction of `v` to the constant base field `k` is trivial.

Note that a place cannot be `p`-adic. Therefore, our
conventions on normalization of valuations imply that places
are always *one-normalized*, i.e. the value group is exactly
`\Gamma_v=\mathbb{Z}`. See :ref:`normalization`.

Geometrically, a place `v` on a function field `F/k`
corresponds to a closed point `P` on a smooth projective curve `X` over `k`.
Here `F=k(X)` is the function field of `X` and `v` is the 'order function'
of the point `P`, i.e. for a function `f\in F`,

.. MATH::

    v(f) = {\rm ord}_P(f) \in\mathbb{Z}

is the vanishing order of the function `f` at the point `P`.

Our treatment of smooth projective curves in
:mod:`smooth_projective_curves <mclf.curves.smooth_projective_curves>`
is completely based on function fields and places.

Places can be explicitly described as follows. Suppose first
that `F=k(x)` is a rational function field. Then any place
`v` on `F` has a *canonical uniformizer* `\pi_v`, which is either

- a monic irreducible polynomial in the generators `x`, or
- the element `1/x`.

In both cases, there exists a unique place which has this
element as a uniformizer.

If we identify the smooth projective model of `F` with the projective line
(this identification corresponds to the choice of `x` as a canonical generator
of `F/k`), then the points corresponding to irreducible polynomials in `x` are
the point on the affine line `\mathbb{A}_k^1={\rm Spec}\, k[x]`, whereas the
valuation with uniformizer `1/x` is the unique *point at infinity*.

In general, a function field `F/k` has a presentation as a finite simple
extension of a rational function field, as follows:

.. MATH::

    F = k(x)[y \mid f(y)=0].

Here `f` is an irreducible polynomial in `y` over the subfield `F_0=k(x)`.

An explicit description of a place `v` on `F` has two parts:

- the description of the restriction `v_0:=v|_{F_0}`,
- the description of `v` as one of the finitely many extensions of `v_0`
  to the finite extension `F/F_0`.

We have seen above how to describe `v_0`; for the second part we distinguish
two cases: whether `v(y)\geq 0` or `v(y) < 0`.

In the first case we restrict `v` to the polynomial ring `R:=F_0[y]` via the
map

.. MATH::

    R = F_0[y] \to F_0[y]/(f) \hookrightarrow F.

This restriction, which we still call `v`, is a discrete *pseudovaluation*
which takes the value `\infty` precisely on the prime ideal `(f)\lhd R`. Using
MacLane's theory of inductive valuations we have a good way to this
pseudovaluation explicitly.

The second case, `v(y)<0`, is similar; we simply have to replace the polynomial
ring `F_0[y]` by `F_0[1/y]`.



`p`-adic valuations on function fields
--------------------------------------

todo


.. TODO::

    - extension of places to a finite extension
    - everything about `p`-adic valuations


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

    The input `v` has to be an instance of
    :class:`DiscreteValuation <sage.rings.valuations.valuation.\
    DiscreteValuation>`, and the domain of `f` has to be a standard function
    field *in standard form*.

    """
    from sage.rings.valuation.valuation import DiscreteValuation
    assert isinstance(v, DiscreteValuation), "v is not a discrete valuation"
    K = v.domain()
    assert is_in_standard_form(K), "the domain of v must be a function field \
        in standard form"
    F = standard_field(K)
    assert F.is_function_field(), "the domain of v must be a function field"
    if (F.constant_base_field().is_number_field()
            and v.residue_characteristic() > 0):
        is_padic = True
    else:
        is_padic = False
    if F.is_rational_function_field():
        if is_padic:
            return pAdicValuationOnRationalFunctionField(F, v)
        else:
            return PlaceOnRationalFunctionField(F, v)
    else:
        if is_padic:
            return pAdicValuationOnNonrationalFunctionField(F, v)
        else:
            return PlaceOnNonrationalFunctionField(F, v)


class DiscreteValuationOnFunctionField(DiscreteValuationOnStandardField):
    r""" Base class for discrete valuations on function fields.


    """


class DiscreteValuationOnRationalFunctionField(
        DiscreteValuationOnFunctionField):
    r""" A class for discrete valuations on a rational function field.




    """


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

        There is a canonical presentation of the extension `F/F_0`,
        corresponding to the choice of the generator `y`. By modifying this
        choice, i.e. by choosing an appropriate *nonstandard generator*,
        we may assume that `v(y)\geq 0`.

        Then MacLane's theory lets us write such a pseudo-valuation quite
        explicitly in one of two ways: either as an *inductive pseudovaluation*,
        or as a *limit valuation*.

        In the first case we can write `v` as

        .. MATH::

            v = [v_0, v_1(\phi_1)=t_1,\ldots,v_n(\phi_n)=\infty],

        for certain irreducible monic polynomiales `\phi_i` (the
        *key polynomials*), and where `\phi_n=G` and we identify the restriction
        `v_0` of `v` to `F_0` with its Gauss valuation on `F_0[y]`.

        This is the case if and only if the defining polynomial `G` is
        irreducible over the `v_0`-adic completion of `F_0`, which is equivalent
        to the condition that `v` is the *unique* extension of `v_0` to `F`.
        Therefore, this method returns an empty list of test values.

        In the second case, we can write `v` as a limit of an inductive
        sequence of valuations,

        .. MATH::

            v = \lim_i v_i,

        where `v_0` is again the Gauss valuation and for `i>0`

        .. MATH::

            v_i = [v_{i-1}, v_i(\phi_i)=t_i]

        is a *proper augmentation* of `v_{i-1}`.

        MacLane's theory also allows to compute an index `n` such that the
        extension `v` of `v_0`, from `F_0` to `F`, is unqiuely determined
        by the condition

        .. MATH::

            v(\phi_n(y)) = t_n.

        So in the second case, the method returns a list with one test value,
        namely `[(\phi_n(y), t_n)]`.

        """
        if not hasattr(self, "test_values"):

            # this will probably not work quite right: the Sage valuation
            # v representing this valuation has to be the correct one,
            # adapted to the choice of the right parameter

            F = self.Domain()
            v = self.sage_valuation()
            raise NotImplementedError()
        return self._test_values

# --------------------------------------------------------------------------

#               places


class PlaceOnFunctionField(DiscreteValuationOnFunctionField):
    r""" Base class for places.

    A **place** is a discrete, normalized valuation on
    a function field which is trivial on the constant base base field.

    This class has two subclasses:

    - :class:`PlaceOnRationalFunctionField`,
    - :class:`PlaceOnNonrationalFunctionField`.

    Initialization is done by these subclass.

    """


class PlaceOnRationalFunctionField(
        PlaceOnFunctionField, DiscreteValuationOnRationalFunctionField):
    r""" The class for places on a rational function field.

    Let `F = k(x)` be a rational function field and `v` a function field
    valuation on `F`. Assume first that `v(x)\geq 0`. Then there exists a
    unique monic and irreducible polynomial `\pi_v\in k[x]` which is a
    uniformizer for `v` (since we assume places to be
    normalized, this means that `v(\pi_v)=1`).

    There is a unique place `v` on `F` such that `v(x)<0`,
    called the *place at infinity*. Then `\pi_v:=1/x` is a uniformizer for
    `v`, and we actually have `v(1/x)=1`.

    In any case, the place `v` is uniquely determined by its *canoncial
    uniformizer* `\pi_v`, which is either a monic irreducible polynomial in `x`,
    or equal to `1/x`.

    INPUT:

    - ``F`` -- a standard rational function field
    - ``v`` -- a place on `F`, either as a Sage valuation, or as a an element
      of `F`.

    OUTPUT:

    the place on `F` corresponding to `v`.

    If `v` is given as a Sage valuation then the domain of `v` must be equal
    to the standard model of `F`.

    If `v` is given as an element of `F`, then it must be either an irreducible
    monic polynomial in `x`, the standard generator of `F`, or be equal
    to `1/x`.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: F = standard_rational_function_field(k, "x")
        sage: x = F.generator()
        sage: v = F.place(x+1); v
        the place on Rational function field in x over Finite Field of size 2
        with uniformizer x + 1

        sage: v.domain()
        Rational function field in x over Finite Field of size 2

        sage: v.uniformizer()
        x + 1

        sage: v(x^2 + x)
        1

    """

    def __init__(self, F, v):
        from mclf.fields.standard_function_fields import (
            StandardRationalFunctionField)
        from sage.rings.valuation.valuation import DiscreteValuation
        assert isinstance(F, StandardRationalFunctionField)
        if isinstance(v, DiscreteValuation):
            assert F.is_equal(v.domain())
        elif v in F.standard_model():
            pi = v
            v = F.standard_model().valuation(pi)
        else:
            raise TypeError("wrong type of argument")
        self._domain = F
        self._sage_valuation = v

    def __repr__(self):
        return "the place on {} with uniformizer {}".format(
            self.domain(), self.uniformizer())

    def uniformizer(self):
        r""" Return the canonical uniformizer of this place.

        The domain of this place is a rational function
        field `k(x)`. So the canonical uniformizer is either a monic
        irreducible polynomial in `x`, or eqaul to `1/x`.

        """
        if not hasattr(self, "_uniformizer"):
            pi = self.sage_valuation().uniformizer()
            # we check that pi is really the canonical uniformizer
            factorization = pi.factor()
            assert len(factorization) == 1
            f, m = factorization[0]
            assert m == 1 or (m == -1 and f == self.domain().gen())
            self._uniformizer = pi
        return self._uniformizer

    def is_equivalent_to(self, w):
        r""" Return whether this place is equivalent to `w`.

        INPUT:

        - ``w`` -- another place on the domain of this
          valuation `v`

        OUTPUT:

        whether `v` and `w` are equivalent.

        A place on a rational function field `K=k(x)` is
        uniquely determined by the canonical uniformizer, which is either an
        irreducible polynomial `f\in k[x]`, or is equal to `1/x`.

        Also, by our convention places are always
        one-normalized. So `v` and `w` are equivalent iff they are equal iff
        they have the same canonical uniformizer.

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        return v.uniformizer() == w.uniformizer()

    def extensions(self, L):
        r""" Return the list of all extensions of this place to a  finite
        extension.

        INPUT:

        - ``L`` -- a finite field extension of the domain `K` of this place `v_0`

        OUTPUT:

        the list of all extensions of `v_0` to `L`.

        """
        raise NotImplementedError()
        from mclf.fields.standard_function_fields import (
            StandardNonrationalFunctionField)
        from mclf.fields.finite_field_extensions import (
            FiniteExtensionOfFunctionFields)

        v0 = self
        if isinstance(L, FiniteExtensionOfFunctionFields):
            return self.extensions_to_finite_field_extension(L)
        elif isinstance(L, StandardNonrationalFunctionField):
            K = L.rational_base_field()
            assert v0.Domain().is_equal(K), "the base field of L must be \
                the domain of this place"
            # this may not always work!
            V = v0.sage_valuation().extensions(L.standard_model())
            return [PlaceOnNonrationalFunctionField(L, v) for v in V]
        else:
            raise TypeError("L is not of the right type")


class PlaceOnNonrationalFunctionField(
        PlaceOnFunctionField, DiscreteValuationOnNonrationalFunctionField):
    r""" The class for places on a nonrational function field.

    Let `F` be a nonrational function field. Then `F` is a finite simple
    extension of its rational base field `F_0=k(x)`,

    .. MATH::

        F = F_0[y]/(G) = k(x, y \mid G(x,y)=0).

    Let `v` be a place on `F`, and `v_0:=v|_{F_0}` the restriction of `v`
    to `F_0`. Then there exists a pair `(f, m)`, with `f\in F` and
    `m\in\mathbb{Z}` with the following property:

        `v` is the unique place on `F` extending `v_0` such that
        `v(f) = m`.

    We call `(f, m)` a **test value** for `v`, and the triple `(v_0, f, m)`
    a **presentation** of `v`.

    INPUT:

    - ``F`` -- a nonrational function field
    - ``v`` -- a place on `F`.

    Here `v` can be given either as a disrete valuation on the standard model
    of `F`, or as a presentation `(v_0, f, m)`, as described above.

    OUTPUT:

    the place on `F` determined by `v`, as an instance of
    :class:`PlaceOnNonrationalFunctionField`.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: x, y = k.polynomial_generators("x", "y")
        sage: F = standard_function_field(y^2 + x^3 + 1)
        sage: F.place(x, y + 1)

    """

    def __init__(self, F, v):
        from mclf.fields.standard_function_fields import (
            StandardNonrationalFunctionField)
        from sage.rings.valuation.valuation import DiscreteValuation
        assert isinstance(F, StandardNonrationalFunctionField)
        if isinstance(v, DiscreteValuation):
            assert F.is_equal(v.domain())
        elif type(v) is tuple:
            assert len(v) == 3, "wrong number of parameters"
            v0 = v[0]
            assert isinstance(v0, PlaceOnRationalFunctionField), (
                "v0 must be a place on a rational function field")
            F0 = F.rational_base_field()
            assert F0.is_equal(v0.Domain()), "the domain of v0 must be the \
                rational base field"
            f = v[1]
            assert f in F.standard_model(), "f must be an element of F"
            m = v[2]
            V = v0.sage_valuation().extensions(F.standard_model())
            V = [v for v in V if v(f) == m]
            assert len(V) > 0, "the place does not exist"
            assert len(V) == 1, "the place is not uniquely determined"
            v = V[0]
        else:
            raise TypeError("wrong type of argument")
        self._domain = F
        self._sage_valuation = v

    def __repr__(self):
        v = self
        F = v.domain()
        x, y = F.generators()
        x_name, y_name = F.variable_names()
        return "the place on {} with v({}) = {} and v({}) = {}".format(
            F, x_name, v(x), y_name, v(y))

    def place(self, a, b):
        r""" Return the place on this function field determined by `a`, `b`.

        INPUT:

        - ``a`` -- a nonzero element of the rational base field of `F`
        - ``b`` -- a nonzero element of `F`

        OUTPUT:

        the unique place `v` on `F` such that `v(a)>0` and `v(b)>0`.

        If `v` is not uniquely determined by these conditions, an error
        is raised.

        """
        V = self.places(a, b)
        assert len(V) > 0, "there is no such place"
        assert len(V) == 1, "the place is not uniquely determined"
        return V[0]

    def places(self, a, *b):
        r""" Return the list of places determined by `a`, `b`.

        INPUT:

        - ``a`` -- a nonzero element of the rational base field of `F`
        - ``b`` -- a nonzero element of `F` (optional)

        OUTPUT:

        the list of places `v` on `F` such that `v(a)>0` and `v(b)>0`.

        If `b` is not given, then the second condition is ignored.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(2)
            sage: x, y = k.polynomial_generators("x", "y")
            sage: F = standard_function_field(y^2 + x^3 + 1)
            sage: x, y = F.generators()
            sage: F.places(x, y + 1)

            sage: F.places((x + 1)/x)

        """
        F = self
        F0 = F.rational_base_field()
        assert not a.is_zero(), "a must not be zero"
        a = F0(a)
        if len(b) > 0:
            b = F(b[0])
        else:
            b = None
        V0 = []
        for pi, m in a.factor():
            if m > 0:
                v0 = F0.place(pi)
                if v0(a) > 0:
                    V0.append(v0)
            elif m < 0 and pi == F0.generator():
                v0 = F0.place_at_infinity()
                if v0(a) > 0:
                    V0.append(v0)
        V = []
        for v0 in V0:
            if b is None:
                V += v0.extensions(F)
            else:
                V += [v for v in v0.extensions(F) if v(b) > 0]
        return V

# --------------------------------------------------------------------------

#          p-adic valuations on function fields


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
