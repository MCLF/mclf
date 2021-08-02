# -*- coding: utf-8 -*-
r"""
Valued field extensions
=======================


EXAMPLES::

    sage: from mclf import *
    sage: K.<x> = FunctionField(QQ)
    sage: v = K.valuation(x)
    sage: K_v = valued_field(K, v)
    sage: K_v
    Rational function field in x over Rational Field with (x)-adic valuation
    sage: K_v.residue_field()
    Rational Field

Valued fields have an inbuild method to compute the extensions of  their
valuation to a finite extension.::

    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2+x^3+x+1)
    sage: L_w = K_v.extensions(L)[0]; L_w
    [Function field in y defined by y^2 + x^3 + x + 1 with (x)-adic valuation,
     as an extension of  Rational function field in x over Rational Field
     with (x)-adic valuation]

Note that the residue field of a valued field extension is again
a field extension.::

    sage: L_w.residue_field()
    Number Field in u1 with defining polynomial y^2 + 1, as finite extension
    of Rational Field

This also works for extensions obtained from an arbitrary embedding
of fields.::

    sage: phi = K.hom([x^2+x])
    sage: extensions = K_v.extensions(phi)
    sage: K_w1 = extensions[0]
    sage: K_w1.residue_field()
    Rational Field, as finite extension of Rational Field
    sage: K_w1.uniformizer()
    x^2 + x
    sage: K_w1.valuation()(x)
    0
    sage: K_w1.valuation()(x+1)
    1

"""

from sage.all import SageObject
from mclf.field_extensions.standard_field_extensions import (
    StandardFieldExtension, StandardFiniteFieldExtension,
    StandardFunctionField)


def valued_field(K, v, is_complete=False):
    r""" Return the valued field `(K, v)`.

    By a *valued field* we mean a pair `(K, v)`, where `K` is a field and
    `v` is a valuation on `K`. We call `K` the *underlying field* and `v` the
    *valuation* of the valued field `(K, v)`.

    INPUT:

    - ``K`` -- a standard field
    - ``v`` -- a valuation on `K`
    - ``is_complete`` -- a boolean (default: ``False``)

    OUTPUT:

    The valued field determined by ´(K, v)`, as an object of the appropriate
    subclass of :class:`ValuedField`.

    If ``is_complete`` is ``True``, then we consider `(K, v)` as the
    *fake completion* of `K` at `v`.


    EXAMPLES::

        sage: from mclf import *
        sage: K = valued_field(QQ, QQ.valuation(3))
        sage: K
        Rational Field with 3-adic valuation
        sage: K.is_complete()
        False

    A p-adic number field is the fake completion of a number field.::

        sage: K = pAdicNumberField(QQ, 3)
        sage: K
        3-adic completion of Rational Field
        sage: isinstance(K, ValuedField)
        True
        sage: K.is_complete()
        True

    """
    from sage.categories.number_fields import NumberFields
    from mclf.padic_extensions.padic_number_fields import pAdicNumberField
    from mclf.field_extensions.standard_field_extensions import (
        is_standard_field)
    assert is_standard_field(K), "K must be a standard field"
    if is_complete and K in NumberFields:
        return pAdicNumberField(K, v)
    else:
        if K.is_finite():
            # the valuation v is trivial anyway
            return ValuedFiniteField(K)
        elif K in NumberFields:
            # is_complete is False
            return ValuedNumberField(K, v)
        else:
            # since K is a standard field, it must now be a function field;
            # there is a specialized function for this case:
            return valued_function_field(K, v, is_complete=is_complete)


def valued_function_field(F, v, k=None, is_complete=False):
    r""" Return the valued function field `(F, v)`
    with constant base field `k`.

    By a *valued function field* we mean a pair `(F/k, v)`, where `F/k` is a
    standard function field and `v` is a valuation on `F`. We call `F` the
    *underlying field* and `v` the *valuation* of the valued field `(F/k, v)`.

    INPUT:

    - ``F`` -- a function field over a finite or a number field
    - ``v`` -- a valuation on `F`
    - ``k`` -- a subfield of `F` such that `F/k` has transcendence degree one,
               or ``None`` (the default)
    - ``is_complete`` -- a boolean (default: ``False``)

    The function field `F` may be given either as a field, or as an object of
    the class :class:`StandardFunctionField`. If the second case, `k` must be
    ``None``, as it is already internally defined by `F`.

    OUTPUT:

    The valued function field determined by ´(F/k, v)`, as an object of the
    class :class:`ValuedFunctionField`.

    If `k` is not given, we understand that `k` is the internally defined
    constant base field of `F`.

    If ``is_complete`` is ``True``, then we consider `(K, v)` as the
    *fake completion* of `K` at `v`.


    EXAMPLES::

        sage: from mclf import *
        sage: F.<x> = FunctionField(QQ)
        sage: v = F.valuation(x)
        sage: F_v = valued_field(F, v); F_v

        sage: F_v.residue_field()

        sage: v = F.valuation(GaussValuation(F._ring, QQ.valuation(2)))
        sage: F_v = valued_field(F, v); F_v
        sage: F_v.residue_field()

    """
    from sage.categories.function_fields import FunctionFields
    from mclf.field_extensions.standard_field_extensions import (
        standard_field_extension)
    if isinstance(F, StandardFunctionField):
        assert k is None, "the constant base field is already defined,\
            so k must not be given"
        assert v.domain() is F.codomain(), "F must be the domain of v"
        v_k = F.restriction_of_valuation(v)
        if v_k.is_trivial():
            return ValuedFunctionFieldWithTrivialBaseValuation(F, v)
        else:
            return ValuedFunctionFieldWithpAdicBaseValuation(F, v, v_k)
    elif F in FunctionFields:
        if k is None:
            k = F.constant_base_field()
        F = standard_field_extension(F, k)
        return valued_function_field(F, v)
    else:
        raise ValueError("F is not of the right type")


class ValuedField(SageObject):
    r""" Base class for valued fields.

    By a *valued field* we mean a pair `(K, v)`, where `K` is a field and
    `v` is a valuation on `K`. We call `K` the *underlying field* and `v` the
    *valuation* of the valued field `(K, v)`.

    An object of this class should be created with the function
    :func:`valued_field`, or :func:`valued_function_field`.

    """

    def __init__(self, K, v):
        from mclf.field_extensions.standard_field_extensions import (
            is_standard_field)
        assert is_standard_field(K), "K has to be a standard field"
        self._underlying_field = K
        assert v.domain() is K, "K has to be the domain of v"
        self._valuation = v

    def __repr__(self):
        return "{} with {}".format(self.underlying_field(), self.valuation())

    def underlying_field(self):
        r""" Return the field underlying this valued field.
        """
        return self._underlying_field

    def valuation(self):
        r""" Return the valuation of this valued field.
        """
        return self._valuation

    def residue_field(self):
        r""" Return the residue field of this valued field.

        """
        return self.valuation().residue_field()

    def uniformizer(self):
        r""" Return a uniformizer of this discretely valued field.

        """
        return self.valuation().uniformizer()

    def reduce(self, a):
        r""" Return the reduction of an element.

        """
        return self.valuation().reduce(a)

    def lift(self, a):
        return self.valuation().lift(a)

    def is_complete(self):
        r""" Return whether this valeud field is complete.

        For the base class :class:`ValuedField`, ``False`` is returned.
        """
        return False

    def extensions(self, L):
        r""" Return the list of all extension of this valued field wrt to a
        finite field extension.

        INPUT:

        - ``L`` -- a finite field extension of the underlying field
                   of this valued field

        `L` may be given in one of the following forms:

        - as an object of :class:`StandardFiniteFieldExtension`,
        - as field with subfield `K`, the underlying field
          of this valued field,
        - as an embedding `\phi_K\to L`.

        OUTPUT:

        a list of all extension of this valued field, with underlying
        extension field `L`.

        Thus, if this valued field is given by the pair `(K, v)` and `L/K`
        is a finite field extension, then the elements of the list are given
        by the pairs `(L, w)`, where `w` runs over all extension of `v` to `L`.


        EXAMPLES::

            sage: from mclf import *
            sage: Q_2 = pAdicNumberField(QQ, 2)
            sage: R.<x> = QQ[]
            sage: L = NumberField(x^2 + x + 2, "a")
            sage: Q_2.extensions(L)
            [Number Field in a with defining polynomial x^2 + x + 2 with
             [ 2-adic valuation, v(x + 1) = 1 ]-adic valuation, as an extension
             of  2-adic completion of Rational Field,
             Number Field in a with defining polynomial x^2 + x + 2 with
              [ 2-adic valuation, v(x) = 1 ]-adic valuation, as an extension
             of  2-adic completion of Rational Field]

        """
        from mclf.field_extensions.standard_field_extensions import (
            standard_field_extension, is_finite_extension)
        from sage.categories.fields import Fields
        K = self.underlying_field()
        if L in Fields:
            assert K.is_subring(L), "K must be a subfield of L"
            phi = K.hom(L)
            assert is_finite_extension(phi)
            L_K = standard_field_extension(phi)
        elif isinstance(L, StandardFiniteFieldExtension):
            L_K = L
            phi = L.embedding()
            assert phi.domain() is K
            L = phi.codomain()
        else:
            phi = L
            assert phi.domain() is K
            L_K = standard_field_extension(phi)
        # now L_K is a standard finite field extension

        if L_K.has_standard_form():
            W = self.valuation().extensions(L_K.codomain())
        else:
            from mclf.field_extensions.valuations import (
                DiscreteValuationViaIsomorphism)
            L1 = L_K.standard_model()
            W1 = self.valuation().extensions(L1)
            L_to_L1 = L_K.to_standard_model()
            L1_to_L = L_K.from_standard_model()
            W = []
            for w1 in W1:
                W.append(DiscreteValuationViaIsomorphism(w1, L_to_L1, L1_to_L))
        return [FiniteValuedFieldExtension(self, L_K, w) for w in W]

    def restriction(self, L_K):
        r""" Return the restriction of this valuation to a subfield.

        INPUT:

        - ``L_K`` -- a standard field extension `L/K`, where `L` is the
                     underlying field of this valued field `(L, w)`

        OUTPUT:

        The valued field `(K, v)`, where `v:=w|_K` is the restriction of `w`
        to the subfield `K`.

        """
        raise NotImplementedError()

    def completion(self):
        r""" Return the completion of this valued field.

        """
        from sage.all import NumberFields, copy
        from mclf.padic_extensions.padic_number_fields import pAdicNumberField

        if self.underlying_field() in NumberFields:
            return pAdicNumberField(self.underlying_field(), self.valuation)
        else:
            completion = copy(self)
            completion._is_complete = True
            return completion


class ValuedFiniteField(ValuedField):
    r""" Return a finite field with trivial valuation.

    """

    def __init__(self, K):
        from sage.rings.valuation.trivial_valuation import TrivialValuation
        assert K.is_finite(), "K has to be a finite field"
        self._underlying_field = K
        self._valuation = TrivialValuation(K)


class ValuedNumberField(ValuedField):
    r""" Return a number fields equipped with a discrete valuation.

    """

    def __init__(self, K, v):
        from sage.categories.number_fields import NumberFields
        assert K in NumberFields, "K must be a number field"
        self._underlying_field = K
        assert v.domain() is K, "K must be the domain of v"
        self._valuation = v


# -----------------------------------------------------------------------------


class ValuedFieldExtension(ValuedField, StandardFieldExtension):
    r""" Abstract base class for a valued field extension.

    A *valued field extension* is a field extension `L/K`, together with
    valuations `v` on `K` and `w` on `L` such that `w|_K = v`.

    This class has two parents: :class:`ValuedField` and
    :class:`StandardFieldExtension`. From the first parent class the pair
    `(L, w)` inherits all methods of a valued field, from the second class the
    methods of a standard field extension.

    """

    def __repr__(self):
        return ValuedField.__repr__(self) + ", as an extension of  {}".format(
            self.base_field())

    def extension_field(self):
        r""" Return this extension field as a valued field.

        """
        return ValuedField(self.codomain(), self.valuation())

    def base_field(self):
        r""" Return the base field of this valued field extension.

        The returned value is an object of the class :class:`ValuedField`.

        """
        return self._base_field

    def residue_field(self):
        r""" Return the residue field of this valued field extension.

        The residue field of a valued field extension is again a field
        extension.

        The initialization of the residue field has to be done by the subclass.

        """
        return self._residue_field


class FiniteValuedFieldExtension(ValuedFieldExtension,
                                 StandardFiniteFieldExtension):
    r""" A finite extension of standard valued fields.

    A *finite valued field extension* is a finite field extension `L/K`,
    together with valuations `v` on `K` and `w` on `L` such that `w|_K = v`.

    INPUT:

    - ``K_v`` -- a valued field `(K, v)`
    - ``L_K`` -- a finite field extension `L` of `K`
    - ``w`` -- data defining a valuation on `L`, extension of the valuation `v`
               on `K`, or

    Here `K_v` has to be an object of the class :class:`ValuedField`, whereas
    the extension `L/K` can be given in one of the following forms:

    - as an object of :class:`StandardFieldExtension`, with domain `K`,
    - as a field `L` containing `K` as a subfield,
    - as an embedding `\phi:K\to L`.

    The valuation `w` can either be given as an object of the class
    :class:`DiscreteValuation`, or as a triple `(w_1, s, t)`, where `w_1` is
    a discrete valuation on a field `L_1`, which is a simple extension of `K`,
    such that `v=w_1|_K`, and `s:L\to L_1` and `t:L_1\to L` are mutually
    inverse, `K`-linear isomorphisms.

    OUTPUT:

    the object representing the valued field extension `(L,w)/(K,v)`.

    """

    def __init__(self, K_v, L_K, w):
        from sage.categories.fields import Fields
        from mclf.field_extensions.standard_field_extensions import (
            StandardFieldExtension, standard_field_extension)

        # reading the input and consistency checks
        assert isinstance(K_v, ValuedField), "K_v has to be a valued field"
        K = K_v.underlying_field()
        if isinstance(L_K, StandardFieldExtension):
            assert L_K.domain() is K, "the domain of L_K must be the field\
                underlying K_v"
        elif L_K in Fields:
            assert K.is_subring(L_K)
            L_K = standard_field_extension(L_K, K)
        elif L_K.domain() is K:
            L_K = standard_field_extension(L_K)
        else:
            raise ValueError("L_K does not have the right type")
        L = L_K.codomain()

        # we use the initializations of the two parent classes
        ValuedField.__init__(self, L, w)
        StandardFiniteFieldExtension.__init__(self, L_K.embedding())

        # we still have to initialize the base field and the residue field
        self._base_field = K_v
        # the residue field must be an object of StandardFiniteFieldExtension
        k_v = K_v.residue_field()
        k_w = w.residue_field()
        phib = k_v.hom(k_w)
        self._residue_field = StandardFiniteFieldExtension(phib)


class ValuedFunctionField(ValuedFieldExtension, StandardFunctionField):
    r""" A finite extension of standard valued fields.

    A *valued function field* is a function field `F/K`, together with
    valuations `v` on `K` and `w` on `F` such that `w|_K = v`.

    INPUT:

    - ``K_v`` -- a valued field `(K, v)`
    - ``F_K`` -- a function field with constant base field `k`
    - ``w`` -- data defining a valuation on `F`, extension of the valuation `v`
               on `K`

    Here `K_v` has to be an object of the class :class:`ValuedField`, whereas
    the extension `F/K` can be given in one of the following forms:

    - as an object of :class:`StandardFunctionField`, with domain `K`,
    - as a function field `F` with constant base field `K`,
    - as an embedding `\phi:K\to F`, with `F/K` of transcendence degree one.

    The valuation `w` can either be given as an object of the class
    :class:`DiscreteValuation`, or as a triple `(w_1, s, t)`, where `w_1` is
    a discrete valuation on a field `L_1`, which is a simple extension of `K`,
    such that `v=w_1|_K`, and `s:L\to L_1` and `t:L_1\to L` are mutually
    inverse, `K`-linear isomorphisms.

    OUTPUT:

    the object representing the valued function field `(F,w)/(K,v)`.

    """

    def __init__(self, K_v, F_K, w):
        from sage.categories.fields import Fields
        from mclf.field_extensions.standard_field_extensions import (
            StandardFunctionField, standard_field_extension)

        # reading the input and consistency checks
        assert isinstance(K_v, ValuedField), "K_v has to be a valued field"
        K = K_v.underlying_field()
        if isinstance(F_K, StandardFunctionField):
            assert F_K.domain() is K, "the domain of F_K must be the field\
                underlying K_v"
        elif F_K in Fields:
            assert K.is_subring(F_K)
            F_K = standard_field_extension(F_K, K)
        elif F_K.domain() is K:
            F_K = standard_field_extension(F_K)
        else:
            raise ValueError("F_K does not have the right type")
        F = F_K.codomain()

        # we use the initializations of the two parent classes
        ValuedField.__init__(self, F, w)
        StandardFunctionField.__init__(self, F_K.embedding())

        # we still have to initialize the base field and the residue field
        self._constant_base_field = K_v
        # the residue field must be an object of StandardFiniteFieldExtension
        k_v = K_v.residue_field()
        k_w = w.residue_field()
        phib = k_v.hom(k_w)
        self._residue_field = StandardFunctionField(phib)


class ValuedFunctionFieldWithTrivialBaseValuation(ValuedFunctionField):
    r""" Return a function field equipped with a discrete valuation which is
    trivial on the constant base field.

    INPUT:

    - ``F`` -- a standard function field
    - ``v`` -- a discrete valuation on `F` which is trivial on the constant
               base field

    Here `F` should be given as an object of :class:`StandardFunctionField` and
    `v` as an object of :class:`DiscreteValuation`. The domain of `v` must be
    identical to the codomain of the extension `F` (i.e. the field `F` itself).

    OUTPUT:

    an object representing the pair `(F, v)`.

    """


class ValuedFunctionFieldWithpAdicBaseValuation(ValuedFunctionField):
    pass
