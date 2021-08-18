# -*- coding: utf-8 -*-
r"""
Standard fields
===============

We call a field `K` a **standard field** if `K` is of one of the following
types:

1. `K` is a *finite field*,
2. `K` is a *number field* (i.e. a finite extension of `\mathbb{Q}`),
3. `K` is a *function field*, i.e. `K` is a finitely generated extension of
   transcendence degree one of a subfield `k`, which is itself either a finite
   field or a number field.

Basically all calculations done in MCLF involve calculations with such
standard fields.

One problem is that in Sage such fields do not occur in
any kind of standard form, which makes it hard to deal with
them in a systematic way. For instance, a number field may be represented as
an absolute number field, or as a tower of relative number fields. Depending
on which form the field is in, many operations (e.g. defining a homomorphism)
require very different forms of input.

To solve this problem, we create a class :class:`StandardField`.
An instance of this class represents a standard field `K`, which provides
internal access to a standard model of `K`. So if `K` is a standard field
(given as an object of the Sage category ``Rings`` such that ``K.is_field()``
is ``True``), we can define a new object ``Ks`` with the function
:func:`standard_field`. ::

    sage: K = standard_field(QQ); K
    Rational Field as a standard field

The object ``K`` represents the field `K` in two ways: by its
**original model** and by its **standard model**. The original model is simply
the field used as an input when creating `K`. The standard model
of `K` is a field which is isomorphic to the original model and is in
*standard form*.

For a field `K` to be in **standard form** means the following:

- If `K` is a finite field with `q` elements, then `K` is in standard form if
  it is identical to the result of the Sage command ``GF(q)``.
  Note that this means that the standard model of `K` is a unique object only
  depending on the cardinality `q` of `K`.
- If `K` is a number field, it is in standard form if it is an absolute number
  field.
  In particular, if `K` is already realized as an absolute number field then
  its standard form is the field `K` itself. Note that, unlike for finite
  fields, there is no unique standard form of `K`.
- If `K` is a function field with constant base field `k`, then it is in
  standard form if `K` is either a rational function field `k(x)`, or a finite,
  simple and separable extension of `k(x)`, where `k` is a finite field or a
  number field in standard form.

For example::

    sage: K = standard_field(GF(4, "a"))
    sage: K.original_model()
    Finite Field in a of size 2^2
    sage: K.standard_model()
    Finite Field in z2 of size 2^2


Coercion, equality and operations on field elements
---------------------------------------------------

In general, our aim is to make sure that replacing a standard field `K`
by the corresponding object of :class:`StandardField` does not lead
to confusion or errors. Handling these new objects should be very similar to
handling ordinary fields in Sage.

There is no extra element class for standard fields. However, if `a` is a field
element which can be coerced into the original model of `K`, we can coerce it
into the standard model a follows::

    sage: a = K.original_model().gen(); a
    a
    sage: K(a)
    z2

An element of the standard model is kept as it is. Therefore, ::

    sage: K(K(a)) == K(a)
    True

always returns ``True`` (or raises an error if `a` is of the wrong type).

For any function `f` defined in this module (e.g. all the methods of
:class:`StandardField`), the test ::

    f(a) == f(K(a))

should return ``True`` (or raise an error). Similarly, if `f` is a function
receiving as input a standard field `K`, which is not necessarily an instance
of :class:`StandardField`, then the result should be the same as when we apply
it to the corresponding object of :class:`StandardField`::

    f(K) == f(standard_field(K))

also returns ``True``.

Instances of :class:`StandardField` are not *unique objects*. For instance, if
we create two instances from the same input, we get two distinct Sage objects::

    sage: K1 = standard_field(QQ)
    sage: K2 = standard_field(QQ)
    sage: K1 == K2
    False

As a partial remedy, standard fields have a method
:meth:`is_equal <StandardField.is_equal>`. We then have ::

    sage: K1.is_equal(K2)
    True

This test is equivalent to ::

    sage: K1.standard_model() == K2.standard_model()
    True

Operations on
field elements should be perfomed via methods attached to the class
:class:`StandardField` or one of its subclasses. For instance, if `K` is an
instance of :class:`StandardField` representing a number field and `a` is an
element of `K` (so actually, an element of the original model or the standard
model of `K`), then the command ::

    f = K.polynomial(a)

returns a polynomial `f` with rational coefficients such that::

    f(K.generator()) == K(a)

returns ``True``. If `a` is actually an element of the *standard model* of `K`,
then ::

    K.polynomial(a) == a.polynomial()

also return  ``True``. It is preferable to use the first option, though,
because the result is more reliable and predictable.


Embeddings
----------

A special role is played by the method :meth:`hom <StandardField.hom>`. If `K`
and `L` are standard fields, and at least `K` is represented by an instance of
:class:`StandardField`, we can define a field homomorphism `\phi:K\to L`
with the command::

    phi = K.hom(L, image_gens, phi0)

Here ``image_gens`` is an element of `L` (or a list of one or two elements of
`L`) specifying the image under `\phi` of the generator(s) of the standard
model of `K`, and `\phi_0` is the *base morphism*, i.e. the restriction of
`\phi` to the natural subfield `K_0\subset K` such that `K/K_0` is generated
by ``image_gens``. If `K` is a finite or a number field, then `K_0` is
the prime subfield of `K` (so `K_0=\mathbb{F}_p` or `K_0=\mathbb{Q}`), and
`\phi_0` is uniquely determined and may be omitted. If `K` is a function field,
then `K_0` is either the constant base field, or the rational function field
`k(x)`, both of which a part of the standard model of `K`.

The output of the method :meth:`hom` is an instance of the class
:class:`EmbeddingOfStandardFields <mclf.fields.embeddings_of_standard_fields.\
EmbeddingOfStandardFields>` and represents an **embedding**, i.e. an
(automatically injective) field homomorphism `\phi:K\to L`.

See
:doc:`Embeddings of standard fields <embeddings_of_standard_fields>`.


Subfields of standard fields
----------------------------

Given an embedding of standard fields `\phi:K\hookrightarrow L`, the image
`\phi(K)` is a subfield of `L`, isomorphic to `K`. It is often convenient
to identify `K` with its image `\phi(K)` and hide the identificaton (which
depends on `\phi`) from the notation. For this purpose we have a class
:class:`StandardSubfield <mclf.fields.standard_subfields.StandardSubfield>`.
An instance of this class represents a standard field `K`, together with a
fixed embedding `\phi:K\hookrightarrow L` into another standard field `L`.

Note that
:class:`StandardSubfield <mclf.fields.standard_subfields.StandardSubfield>` is
a subclass of :class:`StandardField`. Therefore, a standard subfield `K`
inherits all methods from this class and can thus be treated like any other
standard field. The fixed embedding into its overfield is available via the
method
:meth:`embedding <mclf.fields.standard_subfields.StandardSubfield.embedding>`.

See :doc:`Subfields of standard fields <standard_subfields>`.

If `K` is a standard field, it has certain *natural subfields*; these are:

- the *prime subfield* of `K` (`\mathbb{Q}` or `\mathbb{F}_p`, depending on
  the characteristic of `K`),
- the field `K` itself,
- if `K` is a function field, in standard form `K=k(x)[y]/(f)`,

    * the *constant base field* `k` and
    * the *rational base field* `k(x)`.

When `K` is realized as an instance of :class:`StandardField`, we automatically
create instances of
:class:`StandardSubfield <mclf.fields.standard_subfields.StandardSubfield>`
representing these natural subfields.

.. NOTE::

    By convention, a standard field `K` is considered a subfield of itself.
    Therefore, instances of :class:`StandardField` have the method
    :meth:`embedding <StandardField.embedding>`, which return the identity
    map of this field. This makes standard fields a bit consistent with
    instances of
    :class:`StandardSubfield <mclf.fields.standard_subfields.StandardSubfield>`.

    To turn a standard field into a proper instance of this subclass, one can
    use the method
    :meth:`as_subfield_of_itself <StandardField.as_subfield_of_itself>`.


Finite extensions of standard fields
------------------------------------

In practise, interesting standard fields are constructed as finite extensions
of simpler standard fields. For instance, any number field `K` is (in a unique
way!) a finite extension of the field of rational numbers `\mathbb{Q}`. A
particular important example for us are function fields: these are usually
presented as a finite extension of a rational function field. Such a
presentation is not unique, but is often part of the data we keep fixed.

More generally, if `\phi:K\hookrightarrow L` is any embedding of standard
fields, where `K` and `L` are either both function fields or not, `L` is a
finite extension of `\phi(K)`.

We model this situation with the class
:class:`FiniteExtensionOfStandardFields <mclf.fields.finite_field_extensions.\
FiniteExtensionOfStandardFields>`. An instance of this class represents a
standard field `L`, together with an embedding `\phi:K\to L` which makes `L`
a finite extension of `K`.

As for
:class:`StandardSubfield <mclf.fields.standard_subfields.StandardSubfield>`,
the class
:class:`FiniteExtensionOfStandardFields <mclf.fields.finite_field_extensions.\
FiniteExtensionOfStandardFields>` is a subclass of :class:`StandardField`.
However, here we consider the *extension field* `L` as the main object, and its
presentation as a finite extension of the *base field* `K` as the additional
information.

It is an important fact that a finite extension `L/K` of standard fields is
automatically *simple*, i.e. generated by one element. Choosing such a
generator `\alpha\in L` we obtain a presentation

.. MATH::

    L\cong K[x]/(f),

where `f` is the minimal polynomial of `\alpha` over `K`. We call such a
presentation of a finite extension `L/K` a **relative model**. Internally,
an instance of
:class:`FiniteExtensionOfStandardFields <mclf.fields.finite_field_extensions.\
FiniteExtensionOfStandardFields>` has a fixed relative model, which is used for
all the important calculations.

See :doc:`Finite field extensions <finite_field_extensions>`

.. NOTE::

    By convention, a standard field `K` is considered as a finite extension of
    its **base field**, which is
    - the prime subfield if `K` is a finite or a number field,
    - the rational base field `k(x)\subset K`.

    Therefore, instances of :class:`StandardField` have a number of
    methods which emulate methods with the same name belonging to the class
    :class:`FiniteExtensionOfStandardFields <mclf.fields.\
    finite_field_extensions.FiniteExtensionOfStandardFields>`

    For instance,

      todo

Valuations on standard fields
-----------------------------

todo



.. TODO::

    Many things, e.g.

    - base change for function fields is not yet fully implemented
    - so far, the condition *separable* in *standard field* is ignored
    - clarify the convention about the base field of a standard field

    But these things may be done by and by. The most important missing piece
    are valuations!


EXAMPLES::

    sage: from mclf import *
    sage: k0.<a> = GF(4)
    sage: R.<t> = k0[]
    sage: k1.<t> = k0.extension(t^3 + t^2 + t + a); k1
    Univariate Quotient Polynomial Ring in t over Finite Field in a of size 2^2
    with modulus t^3 + t^2 + t + a

This is the kind of fields that can make trouble. For instance, the method
:meth:`is_perfect` is not implemented, and therefore many algorithms involving
function fields over `k` do not work. We therefore compute its
standard model.::

    sage: k = standard_field(k1); k
    the standard field with 64 elements

This new object contains the original field, and a standard model.::

    sage: k.original_model()
    Univariate Quotient Polynomial Ring in t over Finite Field in a of size 2^2
    with modulus t^3 + t^2 + t + a
    sage: k.standard_model()
    Finite Field in z6 of size 2^6

We can coerce elements of the original field into its standard model.::

    sage: k(a+t)
    z6^3 + z6^2

It works similarly for number fields and function fields.::

    sage: from mclf.fields.standard_function_fields import standard_function_field
    sage: F0.<x> = FunctionField(k1)
    sage: R.<y> = F0[]
    sage: F.<y> = F0.extension(y^2+x^3+a); F
    Function field in y defined by y^2 + x^3 + a
    sage: F = standard_function_field(F); F
    standard function field in [x_, y_] over Finite Field in z6 of size 2^6,
    with equation y_^3 + x_^2 + (z6^3 + z6^2 + z6)

"""

from sage.all import SageObject, lcm
from sage.categories.rings import Rings
from sage.categories.fields import Fields
from sage.categories.number_fields import NumberFields
from sage.categories.function_fields import FunctionFields
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


# ---------------------------------------------------------------------------

#                    test functions


def is_standard_field(K):
    r""" Return whether `K` is a standard field.

    INPUT:

    - ``K`` -- a Sage object

    OUTPUT:

    Whether `K` is a standard field; this means that `K` is of one of the
    following types:

    1. `K` is a finite field
    2. `K` is a number field
    3. `K` is a function field, and the constant base field is either finite or
       a number field

    If the input ``K`` is an instance of :class:`StandardField`, we also return
    ``True``.

    EXAMPLES::

        sage: from mclf import *
        sage: is_standard_field(QQ)
        True
        sage: is_standard_field(RR)
        False

    """
    if isinstance(K, StandardField):
        return True
    if K not in Fields and (K not in Rings or not K.is_field()):
        return False
    if K.is_finite() or K in NumberFields:
        return True
    elif K in FunctionFields:
        k = K.constant_base_field()
        return k.is_finite() or k in NumberFields
    else:
        return False


def is_in_standard_form(K):
    r""" Return whether the field `K` is in standard form.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    whether `K` is in standard form; this means the following:

    - if `K` is finite, then `K` is the uniquely determined field with `q=|K|`
      elements, which results from the command ``GF(q)``,
    - if `K` is a finite field extension of `\mathbb{Q}`, then `K` is
      actually an absolute number field,
    - if `K` is a function field, then there are two cases:

      1. `K` is a rational function field over a finite or number field
      which is itself in standard form

      2. `K` is a finite, simple and separable extension of degree `> 1` of
      a rational function field in standard form.

    If `K` is given as an instance of the class :class:`StandardField`
    we return ``True`` as well.

    The result should be equivalent to::

        K is standard_field(K).standard_model()

    EXAMPLES::

        sage: from mclf import *

    A finite field is in standard form iff it is given by ``GF(q)``.::

        sage: is_in_standard_form(GF(4))
        True

    If other options are passed to ``GF``, the result is not in standard form::

        sage: is_in_standard_form(GF(4, "z"))
        False

    Number fields are in standard form iff they are absolute number fields.::

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+2)
        sage: is_in_standard_form(K)
        True
        sage: L.<b> = K.extension(x^2+3)
        sage: is_in_standard_form(L)
        False

    Function fields are in standard form iff they are finite, simple and
    separable extensions of a rational function field over a field `k`
    in standard form.::

        sage: is_in_standard_form(FunctionField(K, "x"))
        True
        sage: is_in_standard_form(FunctionField(L, "x"))
        False

    A finite extension of a rational function field is in standard form if
    the constant base field is in standard form, and if the extension is
    finite, simple, separable and of degree `>1`:

    """
    if isinstance(K, StandardField):
        return True
    assert K in Fields or K in Rings and K.is_field(), "K must be a field"
    assert is_standard_field(K), "K must be a standard field"
    if K.is_finite():
        from sage.all import GF
        q = K.cardinality()
        return K is GF(q)
    elif K in NumberFields:
        # not sure this is the right test..
        return hasattr(K, "is_absolute") and K.is_absolute()
    elif K in FunctionFields:
        k = K.constant_base_field()
        K0 = K.rational_function_field()
        if is_in_standard_form(k):
            if K0 is K.base_field():
                # K is a rational function field
                return True
            else:
                # we test whether K/K_0 is simple, separable and of degree >1
                return (K.rational_function_field() is K.base_field()
                        and K.is_separable() and K.degree() > 1)
        else:
            # the constant base field is not in standard form
            return False

# ----------------------------------------------------------------------------

#                     constructor functions


def standard_field(K):
    r""" Return the standard form of this field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the object representing `K` and its standard model.

    If the input ``K`` is an instance of :class:`StandardField`, then
    ``K`` itself is returned. Otherwise, an instance ``Ks`` of
    :class:`StandardField` is returned such that ``Ks.original_model()``
    is equal to the input ``K``

    EXAMPLES::

        sage: from mclf import *
        sage: standard_field(QQ)
        Rational Field as a standard field

        sage: R.<x> = GF(2)[]
        sage: k.<z> = GF(2).extension(x^3+x^2+1)
        sage: k = standard_field(k); k
        the standard field with 8 elements

        sage: k.generator()
        z3
        sage: k.polynomial()
        x^3 + x + 1

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+x+1)
        sage: L.<b> = K.extension(x^3+a*x+1)
        sage: LL = standard_field(L)
        sage: LL.original_model()
        Number Field in b with defining polynomial x^3 + a*x + 1 over its base
            field
        sage: LL.standard_model()
        Number Field in b with defining polynomial
            x^6 - x^4 + 2*x^3 + x^2 - x + 1
        sage: LL.from_original_model()(b)
        b
        sage: LL.generator()
        b
        sage: LL.polynomial()
        x^6 - x^4 + 2*x^3 + x^2 - x + 1

        sage: k0 = GF(2)
        sage: K0.<x> = FunctionField(k0)
        sage: R.<y> = K0[]
        sage: K.<y> = K0.extension(y^2+y+x^3+1)
        sage: S.<z> = K[]
        sage: L.<z> = K.extension(z^3 +y*z - x^2)
        sage: F = standard_field(L); F
        standard function field in [x, z] over Finite Field of size 2,
        with equation z^6 + x^3*z^2 + x^4 + z^4 + x^2*z + z^2

        sage: F.standard_model()
        Function field in z defined by z^6 + z^4 + (x^3 + 1)*z^2 + x^2*z + x^4

        sage: F.from_original_model()(y)
        1/x^2*z^5 + 1/x^2*z^3 + z^2 + ((x^3 + 1)/x^2)*z + 1

    """
    if isinstance(K, StandardField):
        return K
    assert is_standard_field(K), "K must be a standard field"
    if K.is_finite():
        return StandardFiniteField(K)
    elif K in NumberFields:
        return StandardNumberField(K)
    else:
        from mclf.fields.standard_function_fields import standard_function_field
        return standard_function_field(K)


def standard_prime_field(p):
    r""" Return the prime field of characteristic `p`, as a standard field.

    """
    if p == 0:
        from sage.all import QQ
        return standard_field(QQ)
    else:
        return standard_finite_field(p)


def standard_finite_field(q):
    r""" Return the finite field with `q` elements, as a standard field.

    INPUT:

    - ``q`` -- a prime power `q=p^r>1`

    OUTPUT:

    the field with `q` elements, as a standard field.

    """
    from sage.all import GF
    return standard_field(GF(q))


def standard_number_field(f, gen_name):
    r""" Return the number field given by a polynomial `f`,
    as a standard field.

    INPUT:

    - ``f`` -- an irreducible polynomial over `\mathbb{Q}`
    - ``gen_name`` -- an alphanumeric string

    OUTPUT:

    the number field `K` with one generator with minimal polynomial `f`,
    as a standard field.

    """
    from sage.all import NumberField
    return standard_field(NumberField(f, gen_name))


# --------------------------------------------------------------------------

#                   standard field classes

class StandardField(SageObject):
    r""" The base class for standard fields.

    An instance of this class represents a standard field; it gives access to:

    - the *original* model, i.e. the field used to initialize the object
    - the *standard model*; this is a field in standard form isomorphic to
      the original model. If the original model is in standard form, then both
      models are equal.
    - isomorphisms between the two models
    - most of the usual functionality of a Sage field, or at least all that
      is important for MCLF.

    INPUT:

    - `K` -- a standard field (which may not be in standard form)

    OUTPUT:

    the object representing the field `K`, and its standard model.


    To create an instance of this class you should use the constructor function
    :func:`standard_field`::

        standard_field(K),

    or the more specialized functions :func:`standard_finite_field`,
    :func:`standard_number_field` or :func:`standard_function_field`.

    The following methods must be implemented by the appropriate subclass:

    - :class:`hom <StandardField.hom>`

    """

    def __init__(self, K):
        raise NotImplementedError("No initialization via the base class!")

    def original_model(self):
        r""" Return the *original model* of this standard field.

        This is the field from which this standard field was originally
        constructed.

        """
        return self._original_model

    def standard_model(self):
        r""" Return the standard model of this field.

        The *standard model* of a standard field `K` is a field `K'`,
        isomorphic to `K`, whose internal representation is of the following
        form:

        - the field ``GF(q)``, where `q` is the cardinality of `K`,
          if `K` is finite,
        - an absolute number field, i.e. a simple extension of `\mathbb{Q}`,
          if `K` is a number field,
        - a finite, simple and separable extension of a rational function field
          `k(x)`, where `k` is the constant base field of `K`.

        """
        return self._standard_model

    def from_original_model(self):
        r""" Return the distinguished isomorphism from the original model of
        this field to its standard model.

        """
        return self._from_original_model

    def to_original_model(self):
        r""" Return the distinguished isomorphism from the standard model
        of this field to its original model.

        """
        return self._to_original_model

    def __call__(self, a):
        r""" coerce an element into this field.

        INPUT:

        - ``a`` -- a field element, either from the original model, or
                   coercible into the standard model

        OUTPUT:

        If `a` is an element of the standard model, then we return `a` itself.
        Otherwise, we try to coerce `a` into the original model.

        """
        if a.parent().is_subring(self.standard_model()):
            return self.standard_model()(a)
        else:
            return self.from_original_model()(a)

    def is_finite(self):
        r""" Return whether this is a finite field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def is_number_field(self):
        r""" Return whether this is a number field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def is_function_field(self):
        r""" Return whether this is a function field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def characteristic(self):
        r""" Return the characteristic of this standard field.

        """
        return self.standard_model().characteristic()

    def cardinality(self):
        r""" Return the cardinality of this standard field.

        """
        return self.standard_model().cardinality()

    def generator(self):
        r""" Return the standard generator of this standard field.

        OUTPUT:

        an element of this standard field `K` which generates the simple
        extension `K/K_0`. Here the subfield `K_0` is

        - the prime subfield if `K` is a finite or a number field,
        - the constant base field if `K` is a rational function field,
        - the rational base field if `K` is a nonrational function field

        """
        return self._generator

    def gen(self):
        r""" Return the standard generator of this standard field.

        OUTPUT:

        an element of this standard field `K` which generates the simple
        extension `K/K_0`. Here the subfield `K_0` is

        - the prime subfield if `K` is a finite or a number field,
        - the constant base field if `K` is a rational function field,
        - the rational base field if `K` is a nonrational function field

        This is equivalent to :meth:`generator <StandardField.generator>`.

        """
        return self._generator

    def generators(self):
        r""" Return the list of the standard generators of this standard field.

        OUTPUT:

        a list of elements of this standard field `K` which generates the
        extension `K/K_0`, where the subfield `K_0` is

        - the prime subfield if `K` is finite or a number field
        - the constant base field if `K` is a function field.

        If `K` is a nonrational function field, then this list contains
        exactly two elements:

        1. the standard generator of the rational base field `K_0` of `K`,
        2. the standard generator of the finite extension `K/K_0`.

        In all other cases, the list contains exactly one element, the standard
        generator of `K`.

        """
        if self.is_function_field() and not self.is_rational_function_field():
            return [self.rational_base_field().generator(), self.generator()]
        else:
            return [self.generator()]

    def absolute_generators(self):
        r""" Return the list of absolute generators of this standard field.

        OUTPUT:

        a list of elements of the standard model of this field, which generates
        the field over its prime subfield.

        If this standard field `K` is a finite field or a number field, this
        method is equavalent to :meth:`generators <StandardField.generators>`.
        For function field, we may have to add the generator of the constant
        base field.

        """
        if (self.is_finite() or self.is_number_field()
                or self.constant_base_field().is_prime_field()):
            return self.generators()
        else:
            return [self.constant_base_field().generator()] + self.generators()

    def degree(self):
        r""" Return the degree of this standard field.

        A standard field `K` may be considered as a finite extension of its
        base field `K_0` - which is either the prime subfield  of `K` (if
        `K` is a finite or a number field), or the rational base field if
        `K` is a function field.

        The **degree** of `K` is the degree `[K:K_0]`.

        """
        return self.polynomial().degree()

    def is_natural_subfield_of(self, L):
        r""" Return whether this standard field is the natural subfield of
        another standard field.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_finite_field(4)
            sage: L = standard_finite_field(16)

        Even though `K` can be embedded into `L`, it is not a
        *natural subfield* ::

            sage: K.is_natural_subfield_of(L)
            False
            sage: L.is_natural_subfield_of(L)
            True

        """
        assert isinstance(L, StandardField)
        return any(K.is_equal(self) for K in L.natural_subfields())

    def natural_embedding(self, L):
        r""" Return the natural embedding of this standard field into another
        standard field.

        If no such embedding exists, we return ``None``.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: x = K.polynomial_generator("x")
            sage: L = standard_number_field(x^2 - 2, "a")
            sage: K.natural_embedding(L)
            the natural embedding of Rational Field into Number Field in a
            with defining polynomial x^2 - 2
        """
        assert isinstance(L, StandardField)
        for K in L.natural_subfields():
            if K.is_equal(self):
                return K.embedding()
        return None

    def embedding_of_prime_subfield(self):
        r""" Return the embedding of the prime subfield into this standard
        field.

        """
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfPrimeSubfield)
        if not hasattr(self, "_embedding_of_prime_subfield"):
            self._embedding_of_prime_subfield = EmbeddingOfPrimeSubfield(self)
        return self._embedding_of_prime_subfield

    def prime_subfield(self):
        r""" Return the prime subfield of this standard field.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_prime_field(0)
            sage: K.prime_subfield()
            Rational Field, as a subfield of Rational Field

            sage: x = K.polynomial_generator("x")
            sage: K = standard_number_field(x^2 - 2, "a")
            sage: K.prime_subfield()
            Rational Field, as a subfield of Number Field in a
            with defining polynomial x^2 - 2

        """
        from mclf.fields.standard_subfields import standard_subfield
        if not hasattr(self, "_prime_subfield"):
            iota = self.embedding_of_prime_subfield()
            self._prime_subfield = standard_subfield(iota)
        return self._prime_subfield

    def identity(self):
        r""" Return the identity map of this standard field.

        """
        if not hasattr(self, "_identity"):
            from mclf.fields.embeddings_of_standard_fields import (
                IdentityEmbedding)
            self._identity = IdentityEmbedding(self)
        return self._identity

    def embedding(self):
        r""" Return the embedding of this standard field into itself.

        This method is equivalent to :meth:`identity <StandardField.identity>`.

        It is defined for compatibility with the subclass
        :class:`StandardSubfield <mclf.fields.standard_subfields.\
        StandardSubfield>`.
        """
        return self.identity()

    def as_subfield_of_itself(self):
        r""" Return this standard field as subfield of itself.

        """
        from mclf.fields.standard_subfields import standard_subfield
        if not hasattr(self, "_as_subfield_of_itself"):
            id = self.identity()
            self._as_subfield_of_itself = standard_subfield(id)
        return self._as_subfield_of_itself

    def as_extension_of_itself(self):
        r""" Return this field as a finite extension of itself.

        Output:

        the object of
        :class:`FiniteFieldExtension <mclf.fields.finite_field_extension.\
        FiniteFieldExtension>` whose embedding is the identity map on this
        standard field.

        """
        from mclf.fields.finite_field_extensions import trivial_extension
        if not hasattr(self, "_as_extension_of_itself"):
            self._as_extension_of_itself = trivial_extension(self)
        return self._as_extension_of_itself

    def as_extension_of_prime_field(self):
        r""" Return this field as a finite extension of its prime subfield.

        Output:

        the object of
        :class:`FiniteFieldExtension <mclf.fields.finite_field_extension.\
        FiniteFieldExtension>` whose embedding is the natural embedding of the
        prime subfield into this standard field.

        """
        raise NotImplementedError()

    def is_prime_field(self):
        r""" Return whether this standard field is a prime field,
        i.e. either the field of rational numbers, or a field with `p`
        elements, for a prime `p`.

        """
        return self.standard_model().is_prime_field()

    def is_equal(self, L):
        r""" Return whether this standard field is equal to `L`.

        INPUT:

        - ``L`` -- another standard field

        OUTPUT:

        whether this standard field `K` is equal to `L`. By our definition,
        this means that the standard models of the two fields are equal,
        i.e. ::

            K.standard_model() == L.standard_model()

        returns ``True``.

        """
        assert isinstance(L, StandardField), "L must be a standard field"
        return self.standard_model() == L.standard_model()

    def is_element(self, a):
        r""" Return whether `a` is an element of this standard field.

        """
        K = a.parent()
        return (self.standard_model().has_coerce_map_from(K)
                or self.original_model().has_coerce_map_from(K))

    def contains_as_subfield(self, k):
        r""" Return whether elements of `k` can be coerced into
        this standard field.

        INPUT:

        - ``k`` -- a standard field

        OUTPUT:

        whether any element of `k` can be coerced into this standard field `K`.

        This means that for any element of `k`, the command `K(a)` does not
        raise an error and produces a meaningful result. In fact, this is true
        iff `a` can be coerced into the standard model of `K` or into the
        original model.

        If this method returns ``True`` we can define the embedding of `k` into
        this field via::

            K.embedding_of_subfield(k)

        .. WARNING::

            The above is not quit true; at the moment we only allow *natural*
            subfields to be considered as subfields.


        EXAMPLES::

            sage: from mclf import *
            sage: K0 = GF(4)
            sage: R.<t> = K0[]
            sage: K.<a> = K0.extension(t^2+t+K0.gen())
            sage: Ks = standard_field(K)
            sage: Ks.contains_as_subfield(K)
            True

        """
        # if L is an instance of StandardField, an "element" of L is an
        # element of the standard model
        if isinstance(k, StandardField):
            k = k.standard_model()
        return (self.standard_model().has_coerce_map_from(k)
                or self.original_model().has_coerce_map_from(k))

    def embedding_of_subfield(self, k):
        r""" Return the embedding of a subfield into this standard field.

        INPUT:

        - ``k`` -- a standard field, which can be coerced into this field `K`

        OUTPUT:

        the natural embedding `k\to K`.

        If there is no natural embedding, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K1.<a> = NumberField(x^2+2)
            sage: K2.<b> = K1.extension(x^2 + a)
            sage: K = standard_field(K2)
            sage: K.embedding_of_subfield(K1)
            the embedding of Number Field in a with defining polynomial x^2 + 2
            into Number Field in b with defining polynomial x^4 + 2,
            sending a to -b^2

        """
        assert is_standard_field(k), "k must be a standard field"
        assert self.contains_as_subfield(k), (
            "k must be a natural subfield of K")
        if not isinstance(k, StandardField):
            k = standard_field(k)
        return k.hom(self)

    def polynomial_ring(self, var_names):
        r""" Return a polynomial ring over this standard field.

        INPUT:

        - ``var_names`` -- a list of alphanumeric strings

        OUTPUT:

        the polynomial ring over the standard model of this field,
        with variable names ``var_names``.

        """
        return PolynomialRing(self.standard_model(), var_names)

    def polynomial_generator(self, var_name):
        r""" Return the generator of a univariate  polynomial ring
        over this field.

        INPUT:

        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the generator of the univariate polynomial ring over this field with
        the given variable name.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: K.polynomial_generator("x")
            x

        """
        from sage.all import PolynomialRing
        R = PolynomialRing(self.standard_model(), var_name)
        return R.gen()

    def polynomial_generators(self, var_names):
        r""" Return generators of a polynomial ring over this field.

        INPUT:

        - ``varnames`` -- a list of alphanumeric strings

        OUTPUT:

        the list of generators of the polynomial ring over this field with
        the given variable names.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: K.polynomial_generators(["x", "y"])
            (x, y)

        """
        from sage.all import PolynomialRing
        R = PolynomialRing(self.standard_model(), var_names)
        return R.gens()

    def change_coefficients(self, f):
        r""" Return the base change of a polynomial to this standard field.

        INPUT:

        - ``f`` -- a polynomial over a subring of this field

        OUTPUT:

        the base change of `f` to this standard field.

        This means that the base ring of the returned polynomial is the
        standard model of this standard field.

        """
        return f.map_coefficients(self, self.standard_model())

    def roots(self, f):
        r""" Return the roots of a polynomial over this standard field.

        INPUT:

        - ``f`` -- a univariate nonzero polynomial over this standard field

        OUTPUT:

        The list of of roots of `f` (in this standard field).

        """
        assert not f.is_zero(), "f must not be zero"
        if f.degree() == 0:
            return []
        f = self.change_coefficients(f)
        if self.is_function_field() and not self.is_rational_function_field():
            from mclf.fields.factor_polynomial_over_function_field \
                import roots_of_polynomial_over_function_field
            roots_of_f = roots_of_polynomial_over_function_field(
                self.standard_model(), f)
        else:
            roots_of_f = [alpha for alpha, _ in f.roots()]
        return roots_of_f

    def prime_factors(self, f):
        r""" Return the list of irreducible factors of a polynomial.

        INPUT:

        - ``f`` -- a univariate polynomial over a subring of this field.

        OUTPUT:

        The list of monic irreducible factors of the base change of `f`
        to this standard field.

        """
        f = self.change_coefficients(f)
        if self.is_function_field() and not self.is_rational_function_field():
            from mclf.fields.factor_polynomial_over_function_field \
                import factor_polynomial_over_function_field
            factors_of_f = factor_polynomial_over_function_field(
                self.standard_model(), f)
        else:
            factors_of_f = f.factor()
        return [g for g, _ in factors_of_f]

    def extension(self, f, gen_name=None):
        r""" Return the finite extension of this field given by an irreducible
        polynomial.

        INPUT:

        - ``f`` -- an irreducible univariate polynomial over this field.
        - ``gen_name`` -- an alphanumeric string (optional)

        OUTPUT:

        The finite simple extension `L/K` given by `f`. This is an object of
        :class:`StandardFiniteFieldExtension <mclf.fields.\
        finite_field_extensions.StandardFiniteFieldExtension`.


        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: x = K.polynomial_generator("x")
            sage: K.extension(x^2+2)
            Number Field in x with defining polynomial x^2 + 2,
            as finite extension of Rational Field
            sage: K.extension(x^2+2, "a")
            Number Field in a with defining polynomial x^2 + 2,
            as finite extension of Rational Field

        """
        # we make sure the base ring of f is the standard model
        f = self.change_coefficients(f)
        # we make sure that f is irreducible
        assert len(self.prime_factors(f)) == 1, "f must be irreducible"
        from mclf.fields.finite_field_extensions import (
            finite_field_extension)
        return finite_field_extension(self, f, gen_name)

    def structure(self):
        r""" Return the structure of this standard field.

        This is a presentation of this standard field `K` as a sequence of
        simple extensions.

        OUTPUT:

        a list of triples `(K_i, \alpha_i, f_i)`, `i=1,\ldots,r`, such that

        - `K_0\subset K_1\subset \ldots \subset K_r` is an increasing sequence
          of subfields of (the standard model of) this field `K`, where `K_0`
          is the prime field and `K_r=K`,
        - `\alpha_i\in K_i` is a generator of the extension `K_i/K_{i-1}`,
        - `f_i` is the minimal polynomial of `\alpha_i` over `K_{i-1}`,
          or `f_i=0` if `\alpha_i` is transcendental over `K_{i-1}`.

        Note that if `K` is a finite or a number fields, then `r=1`, and if `K`
        is a function field we have `r=2` or `r=3`.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_field(GF(4))
            sage: k.structure()
            [(the standard field with 4 elements, z2, x^2 + x + 1)]

            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: K = standard_function_field(x^3 + y^2)
            sage: K.structure()
            [(Finite Field in z2 of size 2^2, as a subfield of Rational
             function field in x over Finite Field in z2 of size 2^2,
             z2, x^2 + x + 1),
             (Rational function field in x over Finite Field in z2 of size 2^2,
             as a subfield of Function field in y defined by y^2 + x^3, x, 0),
             (standard function field in [x, y] over Finite Field in z2
             of size 2^2, with equation x^3 + y^2, y, y^2 + x^3)]

        """
        K = self
        if K.is_finite() or K.is_number_field():
            return [(K, K.generator(), K.polynomial())]
        elif K.is_function_field():
            k = K.constant_base_field()
            if K.is_rational_function_field():
                x = K.generator()
                f = K.polynomial_ring(["xx"]).zero()
                return k.structure() + [(K, x, f)]
            else:
                K0 = K.rational_base_field()
                y = K.generator()
                f = K.polynomial()
                return K0.structure() + [(K, y, f)]
        else:
            raise NotImplementedError()

    def natural_subfields(self):
        r""" Return the list of the natural subfields of this standard field.

        OUTPUT:

        a list of subfields of this standard field `K`.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(4)
            sage: k.natural_subfields()
            [Finite Field of size 2, as a subfield of Finite Field in z2
             of size 2^2,
             Finite Field in z2 of size 2^2, as a subfield of Finite Field
             in z2 of size 2^2]

            sage: K0 = standard_rational_function_field(k, "x")
            sage: K0.natural_subfields()
            [Finite Field of size 2, as a subfield of Rational function field
             in x over Finite Field in z2 of size 2^2,
             Finite Field in z2 of size 2^2, as a subfield of Rational function
             field in x over Finite Field in z2 of size 2^2,
             Rational function field in x over Finite Field in z2 of size 2^2,
             as a subfield of Rational function field in x over Finite Field
             in z2 of size 2^2]

            sage: y = K0.polynomial_generator("y")
            sage: K = K0.extension(y^2+y+K0.generator())
            sage: L = K.natural_subfields()

        """
        if self.is_prime_field():
            return [self.as_subfield_of_itself()]
        elif self.is_finite() or self.is_number_field():
            return [self.prime_subfield(), self.as_subfield_of_itself()]
        elif self.is_function_field():
            ret = [self.prime_subfield()]
            k = self.constant_base_field()
            if not k.is_prime_field():
                ret.append(k)
            if not self.is_rational_function_field():
                ret.append(self.rational_base_field())
            ret.append(self.as_subfield_of_itself())
            return ret
        else:
            raise NotImplementedError()

# --------------------------------------------------------------------------

#            these methods must be implemented by each subclass

    def hom(self, L, image_gens, phi0):
        r""" Return a homomorphism from this standard field to another standard
        field.

        INPUT:

        - ``L`` -- a standard field
        - ``image_gens`` -- an element, or a list of elements, of `L`
        - ``phi0`` -- an embedding of a subfield `K_0` of this field `K`
          into `L`

        If this field `K` is finite or a number field, then ``image_gens``
        must consist of a single element of `L`, and the domain `K_0` of
        `\phi_0` is the prime subfield of `K`.

        If `K` is a function field, then ``image_gens`` may contain one or two
        elements of `L`, and `K_0` may be either the constant base field or
        the rational base field of `K`; see :meth:`StandardFunctionField.hom`
        for the exact rules.

        OUTPUT:

        the embedding `\phi:K\to L` which extends `\phi_0` and maps the
        generators of `K/K_0` to the elements of ``image_gens``.

        The result is an instance of the class
        :class:`EmbeddingOfStandardFields <mclf.fields.\
        embeddings_of_standard_fields.EmbeddingOfStandardFields>`.

        This method must be implemented by each terminal subclass.

        """
        raise NotImplementedError()


class StandardFiniteField(StandardField):

    def __init__(self, K):

        # if K is already an instance of StandardField, we simply
        # make a copy
        if isinstance(K, StandardFiniteField):
            self._original_model = K._original_model
            self._standard_model = K._standard_model
            self._from_original_model = K._from_original_model
            self._to_original_model = K._to_original_model
            self._generator = K._generator
            self._polynomial = K._polynomial
        else:
            from sage.categories.rings import Rings
            assert K in Rings and K.is_field(), "K must be a field"
            assert K.is_finite(), "K must be a finite field"
            self._original_model = K
            # compute the normal form of K
            # for finite field, our normal form is created with GF(q)
            # GF's docstring warns that creating a finite field like this,
            # without giving a variable name comes with a speed penalty for
            # large finite fields. We accept this since we mainly work with
            # small finite fields
            from sage.all import GF
            Ks = GF(K.cardinality())
            zs = Ks.gen()
            f = zs.minpoly()
            assert f(zs).is_zero()
            z = f.roots(K)[0][0]
            Ks_to_K = Ks.hom([z])
            K_to_Ks = inverse_of_field_isomorphism(Ks_to_K)
            self._standard_model = Ks
            self._from_original_model = K_to_Ks
            self._to_original_model = Ks_to_K
            self._generator = K_to_Ks(z)
            self._polynomial = f

    def _repr_(self):
        return "the standard field with {} elements".format(
                self.cardinality())

    def is_finite(self):
        r""" Return whether this is a finite field.

        """
        return True

    def is_number_field(self):
        r""" Return whether this is a number field.

        """
        return False

    def is_function_field(self):
        r""" Return whether this is a function field.

        """
        return False

    def is_rational_function_field(self):
        r""" Return whether this is a rational function field.

        """
        return False

    def polynomial(self):
        r""" Return the minimal polynomial of the standard generator over the
        prime field.

        """
        return self._polynomial

    def as_polynomial(self, a):
        r""" Return the polynomial representing the field element `a`.

        INPUT:

        - ``a`` -- an element of this finite field `K`

        OUTPUT:

        a polynomial `f` over the prime field of `K` such that
        `a=f(z)`, where `z` is the standard generator of `K`.

        """
        return self(a).polynomial()

    def minimal_polynomial(self, a, var_name="x"):
        r""" Return the absolute minimal polynomial of a field element.

        INPUT:

        - ``a`` -- an element of this finite field
        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the absolute minimal polynomial of `a`; this is an irreducible
        polynomial over the prime field.

        We use ``var_name`` for the name of the variable of the minimal
        polynomial. The default value is "x".

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_finite_field(9)
            sage: K.minimal_polynomial(K.generator()^2 + 1)
            x^2 + x + 2
            sage: K.minimal_polynomial(5)
            x + 1

        """
        a = self(a)
        if self.is_prime_field():
            R = PolynomialRing(self.prime_field(), var_name)
            return R.gen() - a
        else:
            return a.minpoly(var_name)

    def hom(self, L, *args):
        r""" Return a homomorphism from this finite field to another standard
        field.

        INPUT:

        - ``L`` -- a standard field
        - ``a`` -- an element of `L` (optional)
        - ``psi0`` -- the embedding of the prime field of this field `K`
                      into `L` (optional)

        OUTPUT:

        The embedding `\phi:K\to L` sending the standard generator of `K`
        to `a`. If no such embedding exists, an error is raised.

        If `a` is not given, there must be a canonical embedding of `K`
        into `L`. If not, an error is raised.

        The optional argument ``psi0`` is allowed for compatibility reasons.
        It is not needed because either there is a unique embedding of the
        prime field of `K` into `L`, ot the desired embedding `\phi` doesn't
        exist anyway.

        The result is an instance of the class :class:`EmbeddingOfFiniteField`.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_finite_field(4)
            sage: L = standard_finite_field(16)
            sage: K.hom(L)
            the embedding of Finite Field in z2 of size 2^2 into Finite Field
            in z4 of size 2^4, sending z2 to z4^2 + z4

            sage: a = K.generator()
            sage: K.hom(L, a + 1)
            the embedding of Finite Field in z2 of size 2^2 into Finite Field
            in z4 of size 2^4, sending z2 to z4^2 + z4 + 1

        """
        if not isinstance(L, StandardField):
            assert is_standard_field(L), "L must be a standard field"
            L = standard_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(args) == 0:
            assert L.contains_as_subfield(self)
            a = L(self.generator())
        elif len(args) == 1:
            a = L(args[0])
        elif len(args) == 2:
            a = L(args[0])
            phi0 = args[1]
            # even though phi0 is useless, we test whether it is the right
            # thing:
            assert phi0.is_equal(L.prime_subfield().embedding())
        else:
            raise ValueError("wrong number of arguments")
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFiniteField)
        return EmbeddingOfFiniteField(self, L, a)


class StandardNumberField(StandardField):

    def __init__(self, K):
        # if K is already an instance of StandardField, we simply
        # make a copy
        if isinstance(K, StandardNumberField):
            self._original_model = K._original_model
            self._standard_model = K._standard_model
            self._from_original_model = K._from_original_model
            self._to_original_model = K._to_original_model
            self._generator = K._generator
            self._polynomial = K._polynomial
        else:
            from sage.all import QQ
            from sage.categories.number_fields import NumberFields
            assert K in NumberFields, "K must be a number field"
            self._original_model = K
            # compute the normal form of K
            if K is QQ:
                self._standard_model = K
                self._from_original_model = identity_map(K)
                self._to_original_model = identity_map(K)
                self._generator = K.one()
                R = PolynomialRing(K, "T")
                self._polynomial = R.gen() - K.one()
            elif K.is_absolute():
                self._standard_model = K
                self._from_original_model = identity_map(K)
                self._to_original_model = identity_map(K)
                self._generator = K.gen()
                self._polynomial = K.polynomial()
            else:
                Ka = K.absolute_field(K.variable_name())
                Ka_to_K, K_to_Ka = Ka.structure()
                self._standard_model = Ka
                self._from_original_model = K_to_Ka
                self._to_original_model = Ka_to_K
                self._generator = Ka.gen()
                self._polynomial = Ka.polynomial()

    def _repr_(self):
        return "{} as a standard field".format(self.standard_model())

    def is_finite(self):
        r""" Return whether this is a finite field.

        """
        return False

    def is_number_field(self):
        r""" Return whether this is a number field.

        """
        return True

    def is_function_field(self):
        r""" Return whether this is a function field.

        """
        return False

    def is_rational_function_field(self):
        r""" Return whether this is a rational function field.

        """
        return False

    def polynomial(self):
        r""" Return the minimal polynomial of the standard generator over the
        prime field.

        """
        return self._polynomial

    def as_polynomial(self, a):
        r""" Return the polynomial representing the field element `a`.

        INPUT:

        - ``a`` -- an element of this number field `K`

        OUTPUT:

        a polynomial `f` over `\mathbb{Q}` such that
        `a=f(z)`, where `z` is the standard generator of `K`.

        """
        if self.is_prime_field():
            R = PolynomialRing(self.standard_model(), "T")
            return R(a)
        else:
            return self(a).polynomial()

    def minimal_polynomial(self, a, var_name="x"):
        r""" Return the absolute minimal polynomial of a field element.

        INPUT:

        - ``a`` -- an element of this number field
        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the absolute minimal polynomial of `a`; this is an irreducible
        polynomial over `\mathbb{Q}`.

        We use ``var_name`` for the name of the variable of the minimal
        polynomial. The default value is "x".

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^3 - 2, "a")
            sage: K.minimal_polynomial(K.generator()^2 + 1)
            x^3 - 3*x^2 + 3*x - 5
            sage: K.minimal_polynomial(2)
            x - 2

        """
        a = self(a)
        if self.is_prime_field():
            R = PolynomialRing(self.prime_field(), var_name)
            return R.gen() - a
        else:
            return a.minpoly(var_name)

    def hom(self, L, *args):
        r""" Return a homomorphism from this number field to another standard
        field.

        INPUT:

        - ``L`` -- a standard field
        - ``a`` -- an element of `L` (optional)
        - ``phi0`` -- the unique embedding of the prime field of `K`
                      into `L` (optional)

        OUTPUT:

        The embedding `\phi:K\to L` sending the standard generator of `K`
        to `a`. If no such embedding exists, an error is raised.

        If `a` is not given, there must be a canonical embedding of `K`
        into `L`. If not, an error is raised.

        The argument ``psi0`` is useless and only allowed for compatibility
        reasons: there either exists a unique embedding of the prime field
        of `K` into `L`, or the desired embedding `\phi` does not exist anyway.

        The result is an instance of the class
        :class:`EmbeddingOfNumberField <mclf.fields.\
        embeddings_of_standard_fields.EmbeddingOfNumberField>`.


        EXAMPLES::

            sage: from mclf import *
            sage: K0 = standard_field(QQ)
            sage: x = K0.polynomial_generator("x")
            sage: K1 = standard_number_field(x^2 - 2, "a")
            sage: K0.hom(K1)
            the embedding of Rational Field into Number Field in a with
            defining polynomial x^2 - 2, sending 1 to 1

            sage: K2 = standard_number_field(x^4 - 2, "b")
            sage: b = K2.generator()
            sage: K1.hom(K2, b^2)
            the embedding of Number Field in a with defining polynomial x^2 - 2
            into Number Field in b with defining polynomial x^4 - 2,
            sending a to b^2

        """
        if not isinstance(L, StandardField):
            assert is_standard_field(L), "L must be a standard field"
            L = standard_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(args) == 0:
            assert L.contains_as_subfield(self)
            a = L(self.generator())
        elif len(args) == 1:
            a = L(args[0])
        elif len(args) == 2:
            a = L(args[0])
            phi0 = args[1]
            # even though phi0 is useless, we test whether it is the right
            # thing:
            assert phi0.is_equal(L.prime_subfield().embedding())
        else:
            raise ValueError("wrong number of arguments")
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfNumberField)
        return EmbeddingOfNumberField(self, L, a)


# ----------------------------------------------------------------------------

#                       helper functions, new version


def inverse_of_field_isomorphism(phi):
    r""" Return the inverse of a given field isomorphism.

    INPUT:

    - ``phi`` -- a homomorphism of fields `\phi:K\to L` which is bijective

    We assume that the domain `K` is a field in standard form. In particular,
    both `K` and `L` are standard fields.

    OUTPUT:

    the homomorphism `\psi:L\to K` which is the inverse of `\phi`.

    """
    return inverse_of_field_isomorphism_on_subfield(phi, phi.codomain())


def inverse_of_field_isomorphism_on_subfield(phi, L1):
    r""" Return the restriction of the inverse of a given field isomorphism
    to a subfield.

    INPUT:

    - ``phi`` -- a homomorphism of fields `\phi:K\to L` which is bijective
    - ``L1`` -- a subfield of `L`

    OUTPUT:

    the embedding `\psi:L_1\to K` such that `\phi\circ\psi` is the natural
    inclusion `L_1\to L`.

    """
    from sage.categories.function_fields import FunctionFields
    K = phi.domain()
    L = phi.codomain()
    assert L1.is_subring(L)
    if L1.is_prime_field():
        # there is a canonical embedding of L1 into K
        return L1.hom(K)
    elif hasattr(L1, "base_field") and L1.base_field() is L1:
        # this should only happen if L1 is a rational function field
        assert L1 in FunctionFields
        raise NotImplementedError()
    else:
        # now L1 should be a simple finite extension of its base field
        beta = L1.gen()
        f = beta.minpoly()
        L0 = f.base_ring()
        assert L0.is_subring(L1)
        psi0 = inverse_of_field_isomorphism_on_subfield(phi, L0)
        f_K = f.map_coefficients(psi0, K)
        for alpha, _ in f_K.roots():
            if phi(alpha) == L(beta):
                if L0.is_prime_field():
                    psi = L1.hom([alpha])
                else:
                    psi = L1.hom([alpha], base_map=psi0)
                return psi
        # if we get here, something was wrong
        raise AssertionError("couldn't find the inverse of beta")


def homomorphism_on_standard_field(K, L, *args):
    r""" Return the homomorphism between fields determined by the
    input data.

    INPUT:

    - ``K``, ``L`` -- two fields

    - ``args`` -- optional additional arguments, of the following form:

    1. an element `\alpha\in L`,
    2. a list `[\alpha, \beta]` of two elements of `L`,
    3. an element `\alpha\in L`, and a field homorphism `\phi_0:K_0\to L`,
       defined on a certain subfield of `K`,
    4. a list `[\alpha, \beta]` of two elements of `L`, and a field homorphism
       `\phi_0:K_0\to L`, defined on a certain subfield of `K`.

    OUTPUT:

    the homomorphism `\phi:K\to L` determined by ``args``.

    The rules that determine `\phi` are as follows:

    - If `K` is a subfield of `L`, then the extra arguments may be omitted, and
      then `\phi` is the natural inclusion `K\subset L`.
    - If one element `\alpha\in L` is given, then `K` must be a simple extension
      of its base field `K_0`; we then try to find a homomorphism `\phi:K\to L`
      sending the canonical generator of `K/K_0` to `\alpha`. The restriction
      of `\phi` to `K_0` is either the homomorphism `\phi_0:K_0\to L` given as
      the fourth argument, or the natural inclusion `K_0\subset L`.
    - If a list of two elements `\alpha,\beta\in L` is given, then `K` must be
      a function field in standard form, i.e. a simple finite extension
      `K/K_0`, where `K_0=k(x)` is a rational function field and `y\in K` is a
      generator of `K/K_0`. In this case, we try to find a homomorphism
      `\phi:K\to L` with `\phi(x)=\alpha` and `\phi(y)=\beta`. The restriction
      of `\phi` to `k`is either the homomorphism `\phi_0:k\to L` given as
      the fourth argument, or the natural inclusion `k\subset L`.

      The necessity of such a function stems from the inconsistent way
      arguments are processed by the method :meth:`hom` attached to various kind
      of fields and rings in Sage. By implementing this funciton we hope to
      provide a more uniform way of defining homomorphisms on the kind of
      fields occuring in this project.


      EXAMPLES::

        sage: from mclf import *
        sage: R.<t> = QQ[]
        sage: K.<i> = NumberField(t^2+1)
        sage: homomorphism_on_standard_field(K, K, [-i])
        Ring endomorphism of Number Field in i with defining polynomial
        t^2 + 1
          Defn: i |--> -i

    """
    from sage.categories.rings import Rings
    assert K in Rings and K.is_field(), (
        "K = {} with base field {} must be a field".format(K, K.base_field()))
    # get some easy cases out of the way
    if len(args) == 0:
        assert K.is_subring(L), "if no further arguments are given, K = {} \
            must be a subfield of L = {}".format(K, L)
        try:
            return K.hom(L)
        except TypeError:
            return L.coerce_map_from(K)
    if K.is_prime_field():
        # there can be only one homomorphism; we ignore the other arguments
        assert K.characteristic() == L.characteristic(), "there is no \
            homomorphism from K = {} to L = {}.".format(K, L)
        return K.hom(L)

    image_gens = args[0]
    if not type(image_gens) is list:
        image_gens = [L(image_gens)]
    else:
        assert len(image_gens) == 1 or len(image_gens) == 2, (
            "wrong type of arguments!")
        image_gens = [L(alpha) for alpha in image_gens]
    # now image_gens is a list with exactly one or two elements
    # and these are elements of L

    if len(image_gens) == 2:
        K0 = K.base_field()
        k = K0.constant_base_field()
        assert K0 is not K0, "wrong type of arguments!"
        if len(args) == 2:
            phi0 = args[1]
            assert k.is_subring(phi0.domain()), "phi0 must be defined on the \
                constant base field of K"
        else:
            assert k.is_subring(L), "the constant base field of K must be \
                a subfield of L"
            phi0 = k.hom(L)
        return K.hom(image_gens, L, base_morphism=phi0)

    # now len(image_gens)=1
    if hasattr(K, "base_field"):
        K0 = K.base_field()
        if K is K0:
            # now K is a rational function field, so the "base field"
            # should be the constant base field
            K0 = K0.constant_base_field()
    else:
        K0 = K.prime_subfield()
    # phi0 should be defined on K0
    if len(args) == 2:
        phi0 = args[1]
        assert K0.is_subring(phi0.domain()), "phi0 must be defined on the \
            base field K0 = {} of K = {}".format(K0, K)
    else:
        assert K0.is_subring(L), "the base field K0 = {} of K must be \
            a subfield of L = {}".format(K0, L)
        phi0 = K0.hom(L)
    if K.base_ring().is_prime_field() or (
                hasattr(K, "is_absolute") and K.is_absolute()):
        try:
            K.hom(image_gens, L)
        except ValueError:
            print("error in K.hom(image_gens, L):")
            print("K = ", K)
            print("image_gens = ", image_gens)
            print("L = ", L)
            raise ValueError()
        return K.hom(image_gens, L)
    else:
        # we need to specify the codomain! It should be L
        try:
            return K.hom(image_gens, base_morphism=phi0)
        except TypeError:
            return K.hom(image_gens, base_map=phi0)


def identity_map(K):
    r""" Return the identity map for a standard field `K`.

    """
    from sage.categories.homset import Hom
    return Hom(K, K).identity()


def primitive_element(K):
    r""" Return a primitive element for a tower of finite extensions.

    INPUT:

    - ``K`` -- a standard sage field

    OUTPUT:

    a primitive element for the extension `K/K_0`, where `K_0` is either the
    prime subfield (if `K` is finite or a number field) or the rationa base
    field if `K` is a function field.

    """
    if hasattr(K, "primitive_element"):
        return K.primitive_element()
    elif hasattr(K, "absolute_generator"):
        return K.absolute_generator()
    else:
        return standard_field(K).generator()
