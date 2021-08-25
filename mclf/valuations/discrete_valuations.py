# -*- coding: utf-8 -*-
r"""
Discrete valuations on standard fields
======================================

In this module we implement a class :class:`DiscreteValuationOnStandardField`.
An instance `v` of this class can be treated more or less like a usual valuation
in Sage. The main difference is that it build on top of our notion of
:doc:`standard fields <standard_fields>`.

For instance, ::

    v.domain()

return the domain of `v`, which is the standard model of an instance of
:class:`StandardField <mclf.fields.standard_fields.StandardField>` and which can
be obtain like so::

    v.Domain()

Similarly, the commands ::

    v.residue_field()
    v.Residue_field()

return the residue field as a Sage field, and as an instance of
:class:`StandardField <mclf.fields.standard_fields.StandardField>`,
respectively.


.. _normalization:

Value groups and normalization
------------------------------

Let `v` be a discrete valuation on a field `K`. We write

.. MATH::

    \Gamma_v :=v(K^\times)

for the *value group* of `v`. We always assume that `\Gamma_v` is given as a
(discrete) subgroup of `(\mathbb{Q}, +)`, and write the group law additively.
We also set `v(0):=\infty` and observe all of the usual convention regarding
the symbol `+`.

A discrete valuation `v` on a field `K` is called **trivial** if `v(a)=0` for
all `a\in K^\times`, i.e. `\Gamma_v=0`. To include trivial valuations, we have
the class :class:`TrivialDiscreteValuation`, a primitive subclass of
:class:`DiscreteValuationOnStandardField`.

Let's assume from now on that `v` is nontrivial. Then

.. MATH::

    \Gamma_v = \mathbb{Z}\cdot \gamma_v,

where `\gamma_v>0` is the minimal positive element of `\gamma_v`. We call
`\gamma_v` the **minimal value** of `v`. An element `\pi\in K` with
`v(\pi)=\gamma_v` is called a **uniformizer**.

We call `v` **one-normalized** if `\gamma_v=1`, i.e. `\Gamma_v=\mathbb{Z}`.

We call `v` **p-adic** if the domain `K` has characteristic zero and if there
exists a (unique) prime number `p` such that `v(p)>0`. We call `v`
**p-adically normalized** if `v(p)=1`.

**Convention**: We assume that all discrete, nontrivial valuations on a standard
field are

    - `p`-adically normalized if the valuation is `p`-adic, and
    - one-normalized otherwise.


.. NOTE::

    The convention on normalization mentioned above has the following
    consequences for restrictions and extensions of valuations:

    - The property of being `p`-adically normalized is automatically preserved
      by restriction to a subfield and extension to an overfield. Thus, if we say that
      `w` is an extension of `v` to a field extension `L/K` (or that `v` is the
      restricition of `w` to the subfield `K\subset L`) we mean that
      `v=w|_K`.
    - The above is not true for one-normalized valuations (unless the extension is
      unramified). Nevertheless, we say that `w` is an extension of `v` (or that
      `v` is the restriction of `w`) if `w|_K` is *equivalent* to `v`.


Types of discrete valuations, and subclasses
--------------------------------------------

Recall that there are three main types of standard fields: finite fields,
number fields and function fields.

A discrete valuation on a finite field has to be trivial. Therefore, we can
essentially exclude finite fields from our classification of valuations.

Let `K` be a *number field* i.e. a finite extension of `\mathbb{Q}`. By
Ostrovski's Theorem, every nontrivial discrete valuation on `K` is `p`-adic.
So we need just one subclass of :class:`DiscreteValuationOnStandardField` if
the domain is a number field: this is
:class:`pAdicValuationOnNumberField`.

Finally, if `K/k` is a function field, there are two main cases:

- A discrete valuation `v` on a function field `K/k` is called a
  **function field valuation** if the restriction of `v` to the constant base
  field `k` is trivial.
- If the restriction of `v` to `k` is nontrivial, then `k` must be a number
  field and the restrictio `v_k` must be `p`-adic. Therefore, `v` is `p`-adic
  as well.

The base class and the corresponding subclasses are defined in the submodule
:mod:`discrete_valuations_on_function_fields <mclf.valuations.\
discrete_valuations_on_function_fields>`.

EXAMPLES::

    sage: from mclf import *
    sage: v = discrete_valuation_on_standard_field(QQ.valuation(2)); v
    2-adic valuation on Rational Field

    sage: v.domain()
    Rational Field

    sage: v.Domain()
    Rational Field as a standard field

    sage: v.residue_field()
    Finite Field of size 2

    sage: v.Residue_field()
    the standard field with 2 elements

    sage: R.<x> = QQ[x]
    sage: K = v.Domain().extension(x^4 + 1, "zeta8")
    sage: w = v.extensions(K)[0]; w
    2-adic valuation on Number Field in zeta8 with defining polynomial x^4 + 1

    sage: zeta8 = K.generator()
    sage: L = v.Domain().extension(x^2 + 1, "i")
    sage: i = L.generator()
    sage: phi = L.hom(K, zeta8^2)
    sage: u = w.restriction(phi); u
    2-adic valuation on Number Field in i with defining polynomial x^2 + 1

    sage: u(i+1)
    1/2

    sage: u.uniformizer()
    i + 1

    sage: u.reduce(i)
    1

    sage: u.lift(u.residue_field().one())
    1


AUTHORS:

- Stefan Wewers (2021): initial version


"""

from sage.all import SageObject, QQ, Infinity


def discrete_valuation_on_standard_field(v):
    r""" Return the discrete valuation object.

    INPUT:

    ``v`` -- a discrete valuation on a standard field

    OUTPUT:

    the object of :class:`DiscreteValuationOnStandardField`
    corresponding to `v`.

    .. NOTE::

        For the moment, we require that the domain of `v` is a standard field
        *in standard form*. It may be useful to drop this assumption in the
        future. But then we would have to reconstruct the valuation `v` on the
        standard model of the domain.

    """
    from sage.rings.valuation.valuation import DiscreteValuation
    from mclf.fields.standard_fields import standard_field, is_in_standard_form
    from mclf.valuations.discrete_valuations_on_function_fields import (
        discrete_valuation_on_function_field)
    assert isinstance(v, DiscreteValuation), "v is not a discrete valuation"
    K = v.domain()
    assert is_in_standard_form(K), "the domain of v has to be in standard form"
    K = standard_field(K)
    # because of the assumption, K.standard_model() is now the domain of v
    if v.is_trivial():
        return TrivialDiscreteValuation(K)
    elif K.is_number_field():
        return pAdicValuationOnNumberField(K, v)
    elif K.is_function_field():
        return discrete_valuations_on_function_field(v)
    else:
        raise NotImplementedError()


def trivial_valuation_on_standard_field(K):
    r""" Return the trivial valuation on a standard field.

    EXAMPLES::

        sage: trivial_valuation_on_standard_field(QQ)

    """
    from mclf.fields.standard_fields import StandardField, standard_field
    if not isinstance(K, StandardField):
        K = standard_field(K)
    return TrivialDiscreteValuation(K)


class DiscreteValuationOnStandardField(SageObject):
    r""" Base class for a discrete valuation on a standard field.

    There are three main subclasses:

    - :class:`TrivialDiscreteValuation`
    - :class:`pAdicValuationOnNumberField`
    - :class:`DiscreteValuationOnFunctionField <mclf.valuations.\
      discrete_valuations_on_function_fields.DiscreteValuationOnFunctionField>`

    The first two are primitive classes, the latter has a rather complicated
    graph of subclasses.

    Upon initialization, the following secret attributes have to be defined for
    every instance of this base class:

    - :meth:`_domain`
    - :meth:`_sage_valuation`


    """

    def Domain(self):
        r""" Return the domain of this discrete valuation, as a standard field.

        """
        return self._domain

    def domain(self):
        r""" Return the domain of this discrete valuation, as a sage field.

        """
        return self.Domain().standard_model()

    def Residue_field(self):
        r""" Return the standard residue field of this discrete valuation.

        The standard residue field of this valuation is constructed as follows:
        let `v` be the underlying Sage valuation. Then its residue field
        will be a standard field, which may not be in standard form.

        The standard residue field is then constructed by applying the function
        :func:`standard_field <mclf.fields.standard_fields.standard_field>`.
        As a result, the residue field von `v` is the original model of the
        standard residue field.

        .. NOTE::

            For discrete valuations on function fields this method has to be
            overwritten. The reason is that we want the residue field of a
            discrete valuation on a function field to be an extension of the
            residue field of the constant base field.

            **Question:** What if the domain is a subfield or a finite
            extension? Then we probably want something similar.

        """
        if not hasattr(self, "_residue_field"):
            from mclf.fields.standard_fields import standard_field
            v = self.sage_valuation()
            k = standard_field(v.residue_field())
            self._residue_field = k
        return self._residue_field

    def residue_field(self):
        r""" Return the residue field  of this discrete valuation, as a
        Sage field.

        """
        return self.Residue_field().standard_model()

    def __call__(self, a):
        r""" Return the value of this valuation on a field element.

        INPUT:

        - ``a`` -- an element of the domain of this valuation.

        OUTPUT:

        the rational number `v(a)`, where `v` is this valuation.

        If `a` is an element of the original model it is first transformed to
        an element of the standard model of the domain.

        """
        return self.sage_valuation()(self.Domain()(a))

    def reduce(self, a):
        r""" Return the reduction of an element of the domain to the
        residue field of this discrete valuation.

        INPUT:

        - ``a`` -- an integral element of the domain of this valuation

        OUTPUT:

        the image of `a` in the residue field.


        """
        a = self.Domain()(a)
        assert self(a) >= 0, "a is not integral"
        return self.sage_valuation().reduce(a)

    def lift(self, a):
        r""" Return a lift of an element of the residue field.

        INPUT:

        - ``a`` -- an element of the residue field of this discrete valuation

        OUTPUT:

        a unit element in the domain of this valuation, whose image in the
        resdue field is equal to `a`

        """
        Kb = self.Residue_field()
        # note that the residue field of the Sage valuation of v is the
        # original model of the Residue field
        if a not in Kb.original_model():
            a = Kb.to_original_model()(a)
        return self.sage_valuation().lift(a)

    def sage_valuation(self):
        r""" Return this discrete valuation, as a Sage valuation on the
        standard model.

        """
        return self._sage_valuation

    def value_group(self):
        r""" Return the value group of this discrete valuation.

        """
        return self.sage_valuation().value_group()

    def uniformizer(self):
        return self.sage_valuation().uniformizer()

    def min_value(self):
        if not hasattr(self, "_min_value"):
            self._min_value = self(self.uniformizer())
        return self._min_value

    def is_equal_to(self, w):
        r""" Return whether this valuation is equal to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v`

        OUTPUT:

        whether `v = w`.

        .. NOTE::

            If we assume our convention on normalization_ of discrete
            valuations, then `v` and `w` are equal if and only if they are
            equivalent. The code here doesn't assume this, though, and takes
            the possible scaling factor into account.

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        if v.is_equivalent_to(w):
            return v.value_group() == w.value_group()
        else:
            return False

    def is_equivalent_to(self, w):
        r""" Return whether this valuation is equal to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v`

        OUTPUT:

        whether `v = w`.

        This method must be implemented by the subclass.

        .. WARNING:

            Do not confuse this method with the method :meth:`is_equivalent`,
            which has a very different meaning and purpose.

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        raise NotImplementedError()

    def is_trivial(self):
        r""" Return whether this discrete valuation is trivial.

        For a valuation `v` on a field `K` being *trivial* means that
        `v(a)=0` for all `a\in K^\times`.

        If a valuaton is trivial, it must be an instance of
        :class:`TrivialDiscreteValuation`. The implementation of this
        method can therefore be left to the subclass.

        """
        raise NotImplementedError()

    def extensions(self, L):
        r""" Return the list of extensions of this discrete valuation to a
        finite extension of the domain.

        INPUT:

        - ``L`` -- a finite field extension of the domain of this valuation.

        OUTPUT:

        the list of all extensions of `v` to `L`.

        This method has to be implemented by an appropriate subclass.

        """
        raise NotImplementedError()

    def restriction(self, K):
        r""" Return the restriction of this discrete valuation to a subfield
        of its domain.

        INPUT:

        - ``K`` -- a subfield of the domain of this discrete valuation `v`

        OUTPUT:

        the discrete valuation `v|_K`.

        This method has to be implemented by an appropriate subclass.

        """
        raise NotImplementedError()

    def completion(self):
        r""" Return the completion of the domain at this discrete valuation.

        """
        raise NotImplementedError()


class TrivialDiscreteValuation(DiscreteValuationOnStandardField):
    r""" Return a trivial valuation on a standard field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the trivial valuation `v` on `K`, such that

    .. MATH::

        v(a) = 0,

    for all `a\in K^\times`.

    """

    def __init__(self, K):
        self._domain = K

    def __repr__(self):
        return "the trivial valuation on {}".format(self.domain())

    def __call__(self, a):
        r""" Return the value of this trivial valuation on a field element.

        INPUT:

        - ``a`` -- an element of the domain of this valuation.

        OUTPUT:

        the rational number `v(a)`, where `v` is this valuation.

        Actually, since this valuation is trivial, we return `\infty` if
        `a=0` and `0` otherwise.

        """
        a = self(a)
        if a.is_zero():
            return Infinity
        else:
            return QQ.zero()

    def is_trivial(self):
        r""" Return whether this discrete valuation is trivial.

        Since the domain of this valuation is a finite field, the answer is
        clearly *yes*.

        """
        return True

    def is_equal_to(self, w):
        r""" Return whether this discrete valuation is equal to `w`.

        """
        if isinstance(w, DiscreteValuationOnFiniteField):
            assert self.Domain().is_equal(w.Domain()), "w is not defined on \
                the same domain as this valuation"
        else:
            # I have to test f the domain of w is correct
            raise NotImplementedError()
        return w.is_trivial()

    def is_equivalent_to(self, w):
        r""" Return whether this discrete valuation is equivalent to `w`.

        Since all valuations on a finite field are trivial, they are also
        all equavalent.

        """
        if isinstance(w, DiscreteValuationOnFiniteField):
            assert self.Domain().is_equal(w.Domain()), "w is not defined on \
                the same domain as this valuation"
        else:
            # I have to test f the domain of w is correct
            raise NotImplementedError()
        return w.is_trivial()


class pAdicValuationOnNumberField(DiscreteValuationOnStandardField):
    r""" A class for p-adic valuations on number fields.

    INPUT:

    either

    - ``K`` -- a standard number field
    - ``v`` -- a nontrivial Sage valuation on the standard model of  `K`,

    or

    - ``K`` -- a standard number field
    - ``data`` -- a list of pairs `(a, t)`, with `a\in K` and `t\in\mathbb{Q}`

    OUTPUT:

    the valuation `v` on the number field `K` determined by the input

    If a Sage valuation `v` is given, we simply transform `v` into an instance
    of :class:`DiscreteValuationOnNumberField`.

    If a list `[(a_i,t_i)])` is given, then the unique
    discrete valuation `v` is returned  such that

    .. MATH::

        v(a_i) = t_i, \quad i=1,..,n.

    It is assumed that `a_0=p` is a prime number and that `t_0>0`. As a
    consequence, the valuation `v` will be `p`-adic for the given prime `p`.
    It is furthermore assumed that `v` with this properties exists and is
    unique. If this is not the case, an error is raised.

    """

    def __init__(self, K, v):
        from sage.rings.valuation.valuation import DiscreteValuation
        from mclf.fields.standard_fields import StandardNumberField
        assert isinstance(K, StandardNumberField)
        if isinstance(v, DiscreteValuation):
            assert v.domain() == K.standard_model()
            assert not v.is_trivial(), "v must not be trivial"
            self._domain = K
            self._sage_valuation = v
        elif type(v) is list:
            V = valuations_on_number_field_with_given_values(K, v)
            if len(V) == 0:
                raise ValueError("there is no valuation with the given values")
            elif len(V) > 1:
                raise ValueError("the valuation is not uniquely determined \
                    by the given values")
            else:
                self._domain = K
                self._sage_valuation = V[0]
        else:
            raise TypeError("Input v = {} is of wrong type".format(v))

    def __repr__(self):
        return "{}-adic valuation on {}".format(self.p(),
                                                self.domain())

    def is_trivial(self):
        r""" Return whether this valuation is trivial.

        Since this is a `p`-adic valuaton on a number field, it is by
        definition nontrivial.

        """
        return False

    def residue_characteristic(self):
        r""" Return the residue characteristique of this discrete valuation.

        """
        return self.sage_valuation().p()

    def p(self):
        r""" Return the residue characteristique of this discrete valuation.

        """
        return self.residue_characteristic()

    def is_equivalent_to(self, w):
        r""" Return whether this valuation is equal to `w`.

        INPUT:

        - ``w`` -- another discrete valuation on the domain of this
          valuation `v` (a number field)

        OUTPUT:

        whether `v` is equivalent to `w`, i.e. these discrete valuations are
        equal up to scaling.

        .. WARNING:

            Do not confuse this method with the method :meth:`is_equivalent`,
            which has a very different meaning and purpose.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^4 - 6, "a")
            sage: V = K.valuations(5)
            sage: v = V[0]
            sage: [v.is_equivalent_to(V[i]) for i in range(len(V))]
            [True, False, False, False]

        """
        v = self
        if not isinstance(w, DiscreteValuationOnStandardField):
            w = discrete_valuation_on_standard_field(w)
        assert v.Domain().is_equal(w.Domain()), "v and w do not have the \
            same domain"
        if w.is_trivial():
            return False
        return all(w(a) == t for a, t in v.test_values())

    def test_values(self):
        r""" Return a list of test values for this `p`-adic valuation.

        OUTPUT:

        a list of pairs `(a_i, t_i)`, where `a_i` is an element of the domain
        `K` of this `p`-adic valuation `v` and `t_i` is a rational number, with
        the following property:

        for any normalized `p`-adic valuation `w` on `K` we have

        .. MATH::

            v = w \quad\Leftrightarrow\quad w(a_i)=t_i,\forall i.

        as `v` is a normalized `p`-adic valuation, the first element of this
        list is `(p, 1)`. If `K\neq \mathbb{Q}`, the list will contain exactly
        one more pair `(a, t)`, which we compute using the internal
        representation of `v` as an inductive or a limit valuation.


        EXAMPLES::

            sage: from mclf import *
            sage: K0 = standard_field(QQ)
            sage: v_2 = K0.valuations(2)[0]
            sage: v_2.test_values()
            [(2, 1)]

            sage: x = K0.polynomial_generator("x")
            sage: K = K0.extension(x^3 + x^2 + 2, "a")
            sage: V = K.valuations(2)
            sage: V[0].test_values()
            [(2, 1), (a + 1, 1)]

            sage: V[1].test_values()
            [(2, 1), (a^2 + 2, 3/2)]

        """
        p = self.p()
        ret = [(p, QQ(1))]
        K = self.Domain()
        if K.degree() > 1:
            f, t = self.discoid_representation()
            ret.append((f(K.generator()), t))
        assert all(self(a) == t for a, t in ret)
        return ret

    def discoid_representation(self):
        r""" Return a discoid representation of this `p`-adic valuation.

        OUTPUT:

        a par `(f, t)`, where `f` is a polynomial over `\mathbb{Q}` and `t`
        is a rational number, or `\infty`, which determine this `p`-adic
        valuation `v` on the number field `K` in the following way.

        Let `\alpha\in K` be the standard absolute generator, and let `p` be
        the residue characteristic of `v`. Then `v` is the unique `p`-adic
        valuation on `K` with `v(p)=1` and

        .. MATH::

            v(f(\alpha)) \geq t.

        Moreover, we also guarantee that `v(f(\alpha))=t`.

        If `v` is the only `p`-adic valuation on `K` with `v(p)=1`, then
        the algorithm will return `(f, \infty)`, where `f` is the absolute
        minimal polynomial of `\alpha`.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^4 + 2*x^2 + 4, "a")
            sage: v = K.valuations(2)[0]
            sage: v.discoid_representation()
            (x^4 + 2*x^2 + 4, +Infinity)

            sage: V = K.valuations(5)
            sage: V[0].discoid_representation()
            (x^2 + 2*x + 3, 1)

            sage: V[1].discoid_representation()
            (x^2 + 3*x + 3, 1)

        """
        if not hasattr(self, "_discoid_representation"):
            K = self.Domain()
            if K.degree() == 1:
                # so K = QQ
                from sage.all import Infinity
                return (self.Domain().polynomial(), Infinity)
            else:
                v = self.sage_valuation()._base_valuation
                if hasattr(v, "_approximation"):
                    # v is a limit valuation
                    va = v._approximation
                    G = v._G
                    if va.effective_degree(G) > 1:
                        v._improve_approximation()
                        va = v._approximation
                    v = va
                return (v.phi(), v(v.phi()))
        return self._discoid_respresentation

    def extensions(self, L):
        r""" Return the list of extensions of this `p`-adic valuation to a
        finite extension of the domain.

        INPUT:

        - ``L`` -- a finite field extension of the domain of this valuation.

        OUTPUT:

        the list of all extensions of `v` to `L`.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^2 - 2, "a")
            sage: a = K.generator()
            sage: v = K.valuations(2)[0]
            sage: L = K.extension(x^3 + a*x + 2)
            sage: v.extensions(L)
            [2-adic valuation on Number Field in x with defining polynomial
             x^6 + 4*x^3 - 2*x^2 + 4,
             2-adic valuation on Number Field in x with defining polynomial
             x^6 + 4*x^3 - 2*x^2 + 4]

        """
        from mclf.fields.finite_field_extensions import (
            FiniteExtensionOfNumberFields)
        v = self
        assert isinstance(L, FiniteExtensionOfNumberFields)
        assert v.Domain().is_equal(L.relative_base_field())
        G = L.relative_polynomial()
        W = v.sage_valuation().mac_lane_approximants(G,
                                                     assume_squarefree=True,
                                                     require_incomparability=True)
        ret = []
        p = v.p()
        alpha = L.relative_model().gen()
        for w in W:
            phi = w.phi()
            t = w(phi)
            a = L.from_relative_model()(phi(alpha))
            values = [(p, 1), (a, t)]
            U = valuations_on_number_field_with_given_values(L, values)
            assert len(U) == 1, "something went wrong"
            ret.append(pAdicValuationOnNumberField(L, U[0]))
        return ret

    def restriction(self, phi):
        r""" Return the restriction of this `p`-adic valuation to a subfield.

        INPUT:

        - ``phi`` -- an embedding `\phi:K\to L` of a number fields `K` into
          the domain `L` of this `p`-adic valuation `w`,

        or

        - ``L_K`` -- a finite extension of number fields `L/K`, where `L` is
          the domain of this `p`-adic valuation

        OUTPUT:

        the `p`-adic valuation `v:=w\circ\phi` resp. `v:=w|_K`.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^2 + 6, "a")
            sage: a = K.generator()
            sage: L = standard_number_field(x^4 + 6, "b")
            sage: b = L.generator()
            sage: phi = K.hom(L, b^2)
            sage: w = L.valuations(5)[0]
            sage: w.restriction(phi)
            5-adic valuation on Number Field in a with defining polynomial
            x^2 + 6

        """
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfNumberField)
        from mclf.fields.finite_field_extensions import (
            FiniteExtensionOfNumberFields, finite_field_extension)

        w = self
        L = w.Domain()
        if isinstance(phi, EmbeddingOfNumberField):
            L_K = finite_field_extension(phi)
        elif isinstance(phi, FiniteExtensionOfNumberFields):
            L_K = phi
            phi = L_K.embedding_of_base_field()
        else:
            raise TypeError("phi is not of the right type")
        K = L_K.relative_base_field()
        assert w.Domain().is_equal(L)
        test_values_for_w = w.test_values()
        n = L_K.relative_degree()
        test_values_for_v = [(L_K.relative_norm(a), n*t)
                             for a, t in test_values_for_w]
        V = valuations_on_number_field_with_given_values(K, test_values_for_v)
        assert len(V) == 1, "something went wrong!"
        v = discrete_valuation_on_standard_field(V[0])
        # we test if v is correct:
        assert all(w(phi(a)) == t for a, t in v.test_values()), (
            "something went wrong")
        return v

    def completion(self):
        r""" Return the completion of the domain at this discrete valuation.

        OUTPUT:

        the `p`-adic number field `\hat{K}_v`, as an instance of
        :class:`pAdicNumberField <mclf.padic_extensions.padic_number_fields.\
        pAdicNumberField>`.


        """
        from mclf.padic_extensions.padic_number_fields import pAdicNumberField
        return pAdicNumberField(self.standard_model(), self.sage_valuation())


# ----------------------------------------------------------------------------

#                          helper functions


def valuations_on_number_field_with_given_values(K, values):
    r""" Return the list of discrete valuations on a number field with
    given values.

    INPUT:

    - ``K`` -- a number field
    - ``values`` -- a list of pairs `(a, t)`, where `a` is a nonzero element
      of `K` and `t` is a rational number

    OUTPUT:

    the list of all discrete valuations `v` on `K` such that `v(a)=t` for all
    pairs `(a,t)` in ``values``.

    In order for this list to be finite it is necessary and sufficient that
    there is at least one pair `(a, t)` with `t\neq 0`.


    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^7 + 2*x + 1)
        sage: valuations_on_number_field_with_given_values(K, [(2, 1)])
        [[ 2-adic valuation, v(x + 1) = 1 ]-adic valuation,
         [ 2-adic valuation, v(x^3 + x + 1) = 1 ]-adic valuation,
         [ 2-adic valuation, v(x^3 + x^2 + 1) = 1 ]-adic valuation]

        sage: valuations_on_number_field_with_given_values(K, [(2, 1), (a+1, 1)])
        [[ 2-adic valuation, v(x + 1) = 1 ]-adic valuation]

    """
    from sage.all import gcd
    from mclf.fields.standard_fields import StandardNumberField, standard_field
    if not isinstance(K, StandardNumberField):
        K = standard_field(K)
        assert K.is_number_field()
    values = [(K(a), t) for a, t in values]
    q = gcd(a.absolute_norm() for a, _ in values)
    V = []
    for p, _ in q.factor():
        v_p = QQ.valuation(p)
        V += v_p.extensions(K.standard_model())
    return [v for v in V if all(v(a) == t for a, t in values)]


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


def restriction_of_valuation_along_finite_extension(L_K, w):
    r""" Return the restriction of the valuation w along the embedding phi.

    INPUT:

    - ``L_K`` -- a finite extension of standard fields `L/K`
    - ``w`` -- a discrete valuation on `L`


    OUTPUT:

    the discrete valuation `v` on `K` which is defined as the map `v:=w|_K`.

    """
    raise NotImplementedError()
