# -*- coding: utf-8 -*-
r"""
Discrete valuations on function fields
======================================


In this module we implement the class :class:`DiscreteValuationOnFunctionField`.
Its objects represent *nontrivial* discrete valuations on a standard function
field. A special case of a discrete valuation on a function field is a
*place*. These are realized by the subclass :class:`PlaceOnFunctionField`.

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
a **place**. Places are realized by the class :class:`PlaceOnFunctionField`,
see below.

If `v_k` is nontrivial, then `k` must be a number
field and `v_k` a `p`-adic valuation. In this case we call `v` a
**p-adic valuation**. These are realized by the
:class:`pAdicValuationOnFunctionField <mclf.valuations.\
padic_valuations_on_function_fields.pAdicValuationOnFunctionField>`,
see the module :doc:`padic_valuations_on_function_fields`.


.. _places:

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

When working with places, the following concept turns out to be useful.

    **Definition:**
    Let `F/k` be a function field. An **equation** for `F` is a list of pairs
    `(f_i, m_i)`, `i=1,\ldots,r`, with `f_i\in F^\times` and `m_i\in\mathbb{N}`.
    A **solution** to such an equation is a place `v` on `F` such that

    .. MATH::

        v(f_i) = e\cdot m_i,

    for some `e\in\mathbb{N}`.

    If the equation `(f_i, m_i)_i` has a unique solution `v` then we say that
    `(f_i, m_i)_i` is a **presentation** for `v`.

Our approach for working with places is based on the following two facts:

1. Given a place `v` on `F`, e.g. via the existing implementation in Sage, we
   can easily find a presentation for `v`, and
2. given an equation `(f_i, m_i)_i` on `F`, we can determine its (finite!) set
   of solutions.

To see this, we first assume that `F=k(x)` is a rational function field.
Then any place `v` on `F` has a *canonical uniformizer* `\pi_v`, which is
either

- a monic irreducible polynomial in the generators `x`, or
- the element `1/x`.

In both cases, there exists a unique place which has this
element as a uniformizer. Indeed, if we identify the smooth projective model of
`F` with the projective line (this identification corresponds to the choice of
`x` as a canonical generator of `F/k`), then the points corresponding to
irreducible polynomials in `x` are the point on the affine line
`\mathbb{A}_k^1={\rm Spec}\, k[x]`, whereas the valuation with uniformizer
`1/x` is the unique *point at infinity*.

In the terminology introduced above, this means that `(\pi_v, 1)` is a
presentation for `v`.

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
MacLane's theory of inductive valuations we have a good way to describe this
pseudovaluation explicitly. Using this description, it is then easy to find
a pair `(f, m)`, with `f\in F^\times` and `m\in \mathbb{Z}` such that `v`
is the unique extension of `v_0` such that `v(f)=m`.

This means that we can find an equation for `v` by adding the pair `(f,m)` to
an equation for `v_0`.

The second case, `v(y)<0`, is similar; we simply have to replace the polynomial
ring `F_0[y]` by `F_0[1/y]`.



.. TODO::

    - extension of places to a finite extension
    - everything about `p`-adic valuations

EXAMPLES::

    sage: from mclf import *
    sage: k = standard_finite_field(4)
    sage: alpha = k.generator()
    sage: x, y = k.polynomial_generators(["x", "y"])
    sage: F = standard_function_field(y^2 + y + x^3)
    sage: F1 = standard_function_field(y^2 + y + x^3 + 1)
    sage: x, y = F.generators()
    sage: x1, y1 = F1.generators()
    sage: a = (x^3 + x +1)/(x^2 + 1)
    sage: b = (x^3*y + x^2*y + x*y + x + y)/(x^3 + x^2 + x + 1)
    sage: phi = F1.hom(F, [a, b])

The embedding of function fields `\phi:F_1\to F` corresponds to an isogeny
of supersingular elliptic curves of degree `3`. We first compute the inverse
image of the point `P: (x, y)=(1,0)`. ::

    sage: v_P = F1.place([x1 + 1, y1]); v_P
    the place on Function field in y defined by y^2 + y + x^3 + 1
    with v(x + 1) = 1, v(y + x + 1) = 3,

The inverse image of `P` corresponds to the extensions of `v_P` along `\phi`::

    sage: v_P.extensions(phi)




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

    def presentation(self):
        r""" Return a presentation for this place.

        OUTPUT:

        a list of pairs `(f_i, m_i)`, where `f_i` is a nonzero element of
        this function field and `m_i\in\mathbb{Z}`, such that the following
        holds:

            This place `v` is the unique place such that

            .. MATH::

                v(f_i) = e\cdot m_i, \quad \forall i,

            for some `e\in\mathbb{N}`.

        This method has to be implemented by the two subclasses.

        """
        raise NotImplementedError()

    def extensions(self, L):
        r""" Return the set of all extensions this place to a finite field
        extension.

        INPUT:

        - ``L`` -- a finite field extension of the domain `K` of this place;

        The extension field `L` may be either given as an embedding
        `\phi:K\to L` of function fields, or as an instance of
        :class:`FiniteExtensionOfFunctionFields <mclf.fields.\
        finite_field_extensions.FiniteExtensionOfFunctionFields>`.

        OUTPUT:

        a list containing all extensions of this place from `K` to `L`.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(3)
            sage: F = standard_rational_function_field(k, "x")
            sage: x = F.generator()
            sage: phi = F.hom(F, x^2)
            sage: v = F.place(x)
            sage: v.extensions(phi)
            [the place on Rational function field in x over Finite Field
             of size 3 with uniformizer x]

             sage: v = F.place(1/x)
             sage: v.extensions(phi)
             [the place on Rational function field in x over Finite Field of
              size 3 with uniformizer 1/x]

             sage: v = F.place(x - 1)
             sage: v.extensions(phi)
             [the place on Rational function field in x over Finite Field
              of size 3 with uniformizer x + 1,
              the place on Rational function field in x over Finite Field
              of size 3 with uniformizer x + 2]

        """
        from mclf.fields.standard_function_fields import (
            StandardNonrationalFunctionField)
        from mclf.fields.finite_field_extensions import (
            FiniteExtensionOfFunctionFields, finite_field_extension)
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFunctionField)

        v = self
        if isinstance(L, EmbeddingOfFunctionField):
            L = finite_field_extension(L)
        elif isinstance(L, FiniteExtensionOfFunctionFields):
            pass
        elif isinstance(L, StandardNonrationalFunctionField):
            L = finite_field_extension(L.embedding_of_rational_base_field())
        else:
            raise TypeError("Wrong type of input")

        K = L.relative_base_field()
        assert K.is_equal(v.Domain()), "this place is not defined \
            on the base field of L"
        n = L.relative_degree()
        phi = L.embedding_of_base_field()
        equation_for_w = [(phi(f), m) for f, m in v.presentation()]
        return places_as_solutions_to_equation(L, equation_for_w)


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

    def presentation(self):
        r""" Return a presentation for this place.

        OUTPUT:

        a list of pairs `(f_i, m_i)`, where `f_i` is a nonzero element of
        this function field and `m_i\in\mathbb{Z}`, such that the following
        holds:

            This place `v` is the unique place such that

            .. MATH::

                v(f_i) = e\cdot m_i, \quad \forall i,

            for some `e\in\mathbb{N}`.

        Since the domain of this place is a rational function field, the pair
        `(\pi_v, 1)`, where `\pi_v` is the canonical uniformizer, is an
        equation.

        """
        return [(self.uniformizer(), 1)]

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

    We call `f` a **test element** for `v`, and the triple `(v_0, f, m)`
    a **relative presentation** of `v`.

    INPUT:

    - ``F`` -- a nonrational function field
    - ``v`` -- a place on `F`.

    There are three different ways we can specify the place `v`:

    1. as a Sage disrete valuation on the standard model
       of `F`,
    2. as a relative presentation `(v_0, f, m)`, or
    3. as an absolute presentation `(f_i, m_i)_i`.

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
        from sage.rings.valuation.valuation import DiscretePseudoValuation
        assert isinstance(F, StandardNonrationalFunctionField)
        if isinstance(v, DiscretePseudoValuation):
            assert F.is_equal(v.domain())
        elif type(v) is tuple:
            assert len(v) == 3, "wrong number of parameters"
            v0 = v[0]
            assert isinstance(v0, PlaceOnRationalFunctionField), (
                "v0 must be a place on a rational function field")
            F0 = F.rational_base_field()
            assert F0.is_equal(v0.Domain()), "the domain of v0 must be the \
                rational base field"
            self._base = v0
            f = v[1]
            assert f in F.standard_model(), "f must be an element of F"
            m = v[2]
            V = v0.sage_valuation().extensions(F.standard_model())
            V = [v for v in V if v(f) == m]
            assert len(V) > 0, "the place does not exist"
            assert len(V) == 1, "the place is not uniquely determined"
            v = V[0]
        else:
            raise TypeError("wrong type of argument: v = {} has parent {}".format(
                v, v.parent()))
        e = v(v.uniformizer())
        self._domain = F
        self._sage_valuation = v/e

    def __repr__(self):
        v = self
        F = v.domain()
        presentation = ""
        for f, m in v.presentation():
            presentation += "v({}) = {}, ".format(f, m)
        return "the place on {} with ".format(F) + presentation

    def base(self):
        r""" Return the restriction of this place to the rational base field.

        """
        if not hasattr(self, "_base"):
            F = self.Domain()
            F0 = F.rational_base_field()
            v0 = self.sage_valuation().restriction(F0.standard_model())
            self._base = PlaceOnRationalFunctionField(F0, v0)
        return self._base

    def presentation(self):
        r""" Return a presentation for this place.

        OUTPUT:

        a list of pairs `(f_i, m_i)`, where `f_i` is a nonzero element of
        this function field and `m_i\in\mathbb{Z}`, such that the following
        holds:

            This place `v` is the unique place such that

            .. MATH::

                v(f_i) = e\cdot m_i, \quad \forall i,

            for some `e\in\mathbb{N}`.

        """
        v = self
        F = v.Domain()
        v0 = v.base()
        test_elements = [F(g) for g, _ in v0.presentation()]
        test_elements.append(v.test_element())
        return [(g, v(g)) for g in test_elements]

    def pseudovaluation(self):
        r""" Return the pseudovaluation from which this place is derived.

        OUTPUT:

        the pseudovaluation `v_1` on `F_0[y]` which induces this place `v`
        via the presentation

        .. MATH::

            F = F_0[y \mid G(y)=0]

        of its domain used in the construction of `v`.

        """
        if not hasattr(self, "_pseudovaluation"):
            # if this was not defined by the initialization, then
            # this place was constructed from a sage valuation
            # so we have to untangle it; there is a helper function
            # doing this
            v, y, G = valuation_via_pseudovaluation(self.sage_valuation())
            self._pseudovaluation = v
            self._parameter = y
            self._equation = G
        return self._pseudovaluation

    def parameter(self):
        r""" Return the parameter used in the definition of this place.

        """
        if not hasattr(self, "_parameter"):
            # if this was not defined by the initialization, then
            # this place was constructed from a sage valuation
            # so we have to untangle it; there is a helper function
            # doing this
            v, y, G = valuation_via_pseudovaluation(self.sage_valuation())
            self._pseudovaluation = v
            self._parameter = y
            self._equation = G
        return self._parameter

    def test_element(self):
        r""" Return a test element for this place.

        OUTPUT:

        a nonzero element `f` of the the domain `F` of this place `v` with
        the following property:

            Let `m:=v(f)` and let `v_0` be the restriction of `v` to the
            rational bae field `F_0`. Then `v` is the unique extension of `v_0`,
            from `F_0` to `F`, such that `v(f)=m`.

        """
        from sage.all import Infinity
        if not hasattr(self, "_test_element"):
            v1 = self.pseudovaluation()
            if hasattr(v1, "_approximation"):
                G = v1._G
                v2 = v1._approximation
                while not v2.effective_degree(G) == 1:
                    v1._improve_approximation()
                    v2 = v1._approximation
                if v2(G) == Infinity:
                    v2 = v2._base_valuation
                self._test_element = v2.phi()(self.parameter())
            else:
                v2 = v1._base_valuation
                self._test_element = v2.phi()(self.parameter())
        return self._test_element

# --------------------------------------------------------------------------


def places_as_solutions_to_equation(F, equation):
    r""" Return all the places on a function field satisfying an equation.

    INPUT:

    - ``F`` -- a standard function field
    - ``equation`` -- a nonempty list of pairs `(f_i, m_i)`,
      with `f_i\in F^\times` and `m_i\in\mathbb{Z}`, `m_i>0`

    OUTPUT:

    the list of all places `v` on `F` such that

    .. MATH::

        v(f_i) = s\cdot m_i,\quad \forall i,

    where `s` is a positive rational number, independent of `i`.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: x, y = k.polynomial_generators(["x", "y"])
        sage: F = standard_function_field(y^2 + x^3 + 1)
        sage: x, y = F.generators()
        sage: places_as_solutions_to_equation(F, [(x, 2), (y + 1, 3)])
        [the place on Function field in y defined by y^2 + x^3 + 1
         with v(x) = 2, v(y + 1) = 3, ]

        sage: places_as_solutions_to_equation(F, [(x + 1, 1)])
        [the place on Function field in y defined by y^2 + x^3 + 1
         with v(x + 1) = 2, v(y) = 1, ]

    """
    from mclf.fields.standard_function_fields import StandardFunctionField
    assert isinstance(F, StandardFunctionField)

    if F.is_rational_function_field():
        V = []
        f, m = equation[0]
        for pi, _ in f.factor():
            v = F.place(pi)
            s = v(f)/m
            if s > 0 and all(v(g) == s*n for g, n in equation):
                V.append(v)
        v = F.place_at_infinity()
        s = v(f)/m
        if s > 0 and all(v(g) == s*n for g, n in equation):
            V.append(v)
        return V

    else:
        # F is a nonrational function field
        F0 = F.rational_base_field()
        n = F.degree()
        base_equation = [(F.norm(f), m*n) for f, m in equation]
        V0 = places_as_solutions_to_equation(F0, base_equation)
        V = []
        for v0 in V0:
            # invoking the method "extensions" leads to an infinite loop,
            # because this function is used in there!
            for v in extensions_from_rational_base_field(F, v0):
                f, m = equation[0]
                s = v(f)/m
                if s > 0 and all(v(g) == s*i for g, i in equation):
                    V.append(v)
        return V


def places_as_common_zeroes(F, functions):
    r""" Return the places on a function field determined by a list of functions.

    INPUT:

    - ``F`` -- a standard function field
    - ``functions`` -- a nonempty list of nonzero elements of `F`

    OUTPUT:

    a list containing all places `v` on `F` such that `v(f)>0` for all `f`
    in ``functions``.

    """
    from mclf.fields.standard_function_fields import StandardFunctionField
    assert isinstance(F, StandardFunctionField)
    assert type(functions) is list, "functions must be a list"
    assert len(functions) > 0, "functions must be nonempty"
    assert all(not f.is_zero() for f in functions), "the given functions must \
        be nonzero"

    if F.is_rational_function_field():
        f = functions[0]
        V = []
        for g, _ in f.factor():
            v = F.place(g)
            if all(v(h) > 0 for h in functions):
                V.append(v)
        v = F.place_at_infinity()
        if all(v(h) > 0 for h in functions):
            V.append(v)
        return V

    else:
        # F is a nonrational function field
        F0 = F.rational_base_field()
        base_functions = [F.norm(f) for f in functions]
        V0 = places_as_common_zeroes(F0, base_functions)
        V = []
        for v0 in V0:
            for v in v0.extensions(F):
                if all(v(f) > 0 for f in functions):
                    V.append(v)
        return V


def extensions_from_rational_base_field(F, v0):
    r""" Return the extensions of a place from the rational base field.

    INPUT:

    - ``F`` -- a nonrational function field
    - ``v0`` -- a place on the rational base field of `F`

    OUTPUT:

    a list contaning all extensions of `v_0` to `F`.

    EXAMPLES::

        sage: from mclf import *
        sage: k = standard_finite_field(2)
        sage: x, y = k.polynomial_generators(["x", "y"])
        sage: F = standard_function_field(y^2 + x^3 + 1)
        sage: F0 = F.rational_base_field()
        sage: x = F0.generator()
        sage: v0 = F0.place(x)
        sage: extensions_from_rational_base_field(F, v0)
        [the place on Function field in y defined by y^2 + x^3 + 1
         with v(x) = 2, v(y + 1) = 3, ]

    """
    from mclf.fields.standard_function_fields import (
        StandardNonrationalFunctionField)
    assert isinstance(F, StandardNonrationalFunctionField)
    F0 = F.rational_base_field()
    assert F0.is_equal(v0.Domain())
    V = v0.sage_valuation().extensions(F.standard_model())
    return [PlaceOnNonrationalFunctionField(F, v) for v in V]


def valuation_via_pseudovaluation(v):
    r""" Return a presentation of a Sage valuation on a nonrational function
    field by a pseudovaluation.

    INPUT:

    - ``v`` -- a discrete valuation on a nonrational function field `F`

    OUTPUT:

    a triple `(v_1, y_1, G)`, where

    - `v_1` is an infinite pseudovaluation on a polynomial ring over the
      rational base field `F_0` of `F`,
    - `y_1` is a generator of `F/F_0`,
    - `G` is the minimal polynomial of `y_1` over `F_0`,

    such that the following holds:

    - the valuation `v` is the pushforward of the pseudovaluation `v_1` via
      the surjective ring homomorphism

      .. MATH::

        F_0[T] \to F, \quad T\mapsto y_1,

      and

    - `v(y_1)\geq 0`.

    EXAMPLES::

        sage: from mclf import *
        sage: F0.<x> = FunctionField(QQ)
        sage: R.<y> = F0[]
        sage: F.<y> = F0.extension(y^2 + x*y + 1); F
        Function field in y defined by y^2 + x*y + 1

        sage: v0 = F0.valuation(x)
        sage: v = v0.extension(F)
        sage: valuation_via_pseudovaluation(v)
        ([ Gauss valuation induced by (x)-adic valuation,
           v(y^2 + x*y + 1) = +Infinity ], y, y^2 + x*y + 1)

        sage: w0 = F0.valuation(1/x)
        sage: W = w0.extensions(F)
        sage: valuation_via_pseudovaluation(W[0])
        ([ Gauss valuation induced by Valuation at the infinite place,
           v(y + 1) = 2 , … ], 1/x*y, y^2 + y + 1/x^2)

        sage: valuation_via_pseudovaluation(W[1])
        ([ Gauss valuation induced by Valuation at the infinite place,
           v(y) = 2 , … ], 1/x*y, y^2 + y + 1/x^2)

    """
    from sage.rings.valuation.mapped_valuation import MappedValuation_base
    F = v.domain()
    F0 = F.base()
    v1 = v._base_valuation
    if not v1.is_discrete_valuation():
        v1 = v._base_valuation
        y1 = F.gen()
        G = v1._G
    else:
        v1 = v1._base_valuation
        G = v1._G
        y1 = v._from_base(v._base_valuation.domain().gen())
    assert G(y1).is_zero()
    assert v(y1) >= 0
    return v1, y1, G
