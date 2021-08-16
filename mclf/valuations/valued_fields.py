# -*- coding: utf-8 -*-
r"""
Valued fields
=============


EXAMPLES::

    sage: from mclf import *
    sage: K.<x> = FunctionField(QQ)
    sage: v = K.valuation(x)
    sage: K_v = valued_field(K, v)
    sage: K_v
    Rational function field in x over Rational Field with (x)-adic valuation
    sage: K_v.residue_field()
    Rational Field

Valued fields have an inbuild method to compute the extensions of their
valuation to a finite extension.::

    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2+x^3+x+1)
    sage: L_w = K_v.extensions(L)[0]; L_w
    [Function field in y defined by y^2 + x^3 + x + 1 with (x)-adic valuation, as an extension of  Rational
     function field in x over Rational Field with (x)-adic valuation]

Note that the residue field of a valued field extension is again a field extension::

    sage: L_w.residue_field()
    Number Field in u1 with defining polynomial y^2 + 1, as finite extension of Rational Field

This also works for extensions obtained from an arbitrary embedding of fields.::

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

from mclf.fields.standard_fields import (StandardField,
                                         StandardFiniteField, StandardNumberField, StandardFunctionField)


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
    from mclf.field_extensions.standard_field_extensions import is_standard_field
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
    r""" Return the valued function field `(F, v)` with constant base field `k`.

    By a *valued function field* we mean a pair `(F/k, v)`, where `F/k` is a
    standard function field and `v` is a valuation on `F`. We call `F` the
    *underlying field* and `v` the *valuation* of the valued field `(F/k, v)`.

    INPUT:

    - ``F`` -- a function field over a finite or a number field
    - ``v`` -- a valuation on `F`
    - ``k`` -- a subfield of `F` such that `F/k` has transcendence degree one,
               or ``None`` (the default)
    - ``is_complete`` -- a boolean (default: ``False``)

    The function field `F` may be given either as a field, or as an object of the
    class :class:`StandardFunctionField`. If the second case, `k` must be ``None``,
    as it is already internally defined by `F`.

    OUTPUT:

    The valued function field determined by ´(F/k, v)`, as an object of the class
    :class:`ValuedFunctionField`.

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
    from mclf.fields.standard_fields import standard_function_field
    if isinstance(F, StandardFunctionField):
        assert k is None, "the constant base field is already defined, so k must not be given"
        assert v.domain() is F.codomain(), "F must be the domain of v"
        v_k = F.restriction_of_valuation(v)
        if v_k.is_trivial():
            return ValuedFunctionFieldWithTrivialBaseValuation(F, v)
        else:
            return ValuedFunctionFieldWithpAdicBaseValuation(F, v, v_k)
    elif F in FunctionFields:
        if k is None:
            k = F.constant_base_field()
        F = standard_function_field(F, k)
        return valued_function_field(F, v)
    else:
        raise ValueError("F is not of the right type")


class ValuedField(StandardField):
    r""" Base class for valued fields.

    By a *valued field* we mean a pair `(K, v)`, where `K` is a field and
    `v` is a valuation on `K`. We call `K` the *underlying field* and `v` the
    *valuation* of the valued field `(K, v)`.

    An object of this class should be created with the function
    :func:`valued_field`, or :func:`valued_function_field`. It will then be
    an instance of one of the subclasses :class:`ValuedFiniteField`,
    :class:`ValuedNumberField` or :class:`ValuedFunctionField`.

    Since this class is a subclass of :class:`StandardField`, the basic methods
    :meth:`underlying_field` and :meth:`standard_model` are available.

    """

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

        - ``L`` -- a finite field extension of the underlying field of this valued field

        `L` may be given in one of the following forms:

        - as an object of :class:`FiniteFieldExtension`,
        - as field with subfield `K`, the underlying field of this valued field,
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
            [Number Field in a with defining polynomial x^2 + x + 2 with [ 2-adic
             valuation, v(x + 1) = 1 ]-adic valuation, as an extension of  2-adic
             completion of Rational Field,
             Number Field in a with defining polynomial x^2 + x + 2 with [ 2-adic
             valuation, v(x) = 1 ]-adic valuation, as an extension of  2-adic
             completion of Rational Field]

        """
        from mclf.fields.finite_field_extensions import (
            FiniteFieldExtension, is_finite_extension, finite_field_extension)
        from sage.categories.fields import Fields
        K = self.underlying_field()
        if L in Fields:
            assert K.is_subring(L), "K must be a subfield of L"
            phi = K.hom(L)
            assert is_finite_extension(phi)
            L_K = finite_field_extension(phi)
        elif isinstance(L, FiniteFieldExtension):
            L_K = L
            phi = L.embedding()
            assert phi.domain() is K
            L = phi.codomain()
        else:
            phi = L
            assert phi.domain() is K
            L_K = finite_field_extension(phi)
        # now L_K is a standard finite field extension

        if L_K.has_standard_form():
            W = self.valuation().extensions(L_K.codomain())
        else:
            from mclf.field_extensions.valuations import DiscreteValuationViaIsomorphism
            L1 = L_K.standard_model()
            W1 = self.valuation().extensions(L1)
            L_to_L1 = L_K.to_standard_model()
            L1_to_L = L_K.from_standard_model()
            W = []
            for w1 in W1:
                W.append(DiscreteValuationViaIsomorphism(w1, L_to_L1, L1_to_L))
        return [valued_field(self, w) for w in W]

    def restriction(self, L_K):
        r""" Return the restriction of this valuation to a subfield.

        INPUT:

        - ``L_K`` -- a standard field extension `L/K`, where `L` is the underlying
                     field of this valued field `(L, w)`

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


class ValuedFiniteField(ValuedField, StandardFiniteField):
    r""" Return a finite field with trivial valuation.

    """

    def __init__(self, K):
        from sage.rings.valuation.trivial_valuation import TrivialValuation
        if isinstance(K, StandardField):
            assert isinstance(K, StandardFiniteField)
            self._underlying_field = K.underlying_field()
            self._standard_model = K.standard_model()
            self._to_standard_model = K.to_standard_model()
            self._from_standard_model = K.from_standard_model()
        else:
            assert K.is_finite(), "K has to be a finite field"
            # we use the initializations of the second parent class
            StandardFiniteField.__init__(self, K)
        self._valuation = TrivialValuation(K)


class ValuedNumberField(ValuedField, StandardNumberField):
    r""" Return a number fields equipped with a discrete valuation.

    """

    def __init__(self, K, v):
        from sage.categories.number_fields import NumberFields
        if isinstance(K, StandardField):
            assert isinstance(K, StandardNumberField)
            self._underlying_field = K.underlying_field()
            self._standard_model = K.standard_model()
            self._to_standard_model = K.to_standard_model()
            self._from_standard_model = K.from_standard_model()
        else:
            assert K in NumberFields, "K must be a number field"
            StandardNumberField.__init__(self, K)
        assert v.domain() is K, "K must be the domain of v"
        self._valuation = v


class ValuedFunctionField(ValuedField, StandardFunctionField):
    r""" A finite extension of standard valued fields.

    A *valued function field* is a function field `F/k`, together with
    a discrete pseudovaluation `v` on `F`.


    """

    def __init__(self, F):
        # this only initializes self as the standard function field
        # initialization of the valuation etc is done by the init method
        # of the subclass
        from sage.categories.fields import Fields
        from mclf.field_extensions.standard_field_extensions import (
            StandardFunctionField)

        # initializing F as a StandardFunctionField
        assert isinstance(F, StandardFunctionField)
        # we just have to copy the data from F
        self._underlying_field = F.underlying_field()
        self._constant_base_field = F.constant_base_field()
        self._embedding_of_constant_base_field = (
            F._embedding_of_constant_base_field())
        self._standard_model = F.standard_model()
        self._to_standard_model = F.to_standard_model()
        self._from_standard_model = F.from_standard_model()


class ValuedFunctionFieldWithTrivialBaseValuation(ValuedFunctionField):
    r""" Return a function field equipped with a discrete valuation which is
    trivial on the constant base field.

    INPUT:

    - ``F`` -- a standard function field
    - ``v`` -- a discrete valuation on `F` which is trivial on the constant base
               field

    Here `F` should be given as an object of :class:`StandardFunctionField` and
    `v` as an object of :class:`DiscreteValuation`. The domain of `v` must be
    identical to the codomain of the extension `F` (i.e. the field `F` itself).

    OUTPUT:

    an object representing the pair `(F, v)`.

    """

    def __init__(self, F, v):
        # call the initialization of th parent, which just copies all data
        # from F
        ValuedFunctionField.__init__(self, F)
        # it remains to initialize the valuation and the residue field
        assert v.domain() is F.underlying_field()
        self._valuation = v
        # the residue field of v is a finite extension of the constant base
        # field


class ValuedFunctionFieldWithpAdicBaseValuation(ValuedFunctionField):
    r""" Return a function field equipped with a discrete valuation which is
    a `p`-adic valuation on the constant base field.

    INPUT:

    - ``F`` -- a standard function field, whose constant base field `k`
               is a number field
    - ``v`` -- a discrete valuation on `F` which is `p`-adic on `k`
    - ``v_k`` -- the restriction of `v` to `k`

    Here `F` should be given as an object of :class:`StandardFunctionField` and
    `v` and `v_k` as objects of :class:`DiscreteValuation`. The domain of `v`
    must be identical to the underlying field of `F`.

    OUTPUT:

    an object representing the pair `(F/k, v)`.

    """

    def __init__(self, F, v, v_k):
        # call the initialization of th parent, which just copies all data
        # from F
        ValuedFunctionField.__init__(self, F)
        # it remains to initialize the valuation and the residue field
        assert v.domain() is F.underlying_field()
        assert v_k.domain() is F.constant_base_field()
        self._valuation = v
        self._base_valuation = v_k
        # the residue field of v is a finite *valued* field extension of the
        # constant base field
