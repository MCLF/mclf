# -*- coding: utf-8 -*-
r"""
Subfields of standard fields
============================

In this module we implement a class :class:`StandardSubfield`. Instances of
this class are standard fields, together with an embedding into an overfield
(which must be a standard field, too).

For instance, if `K` is a standard field, then the command ::

    sage: K.natural_subfields()

produces a list of instances of this class.

EXAMPLES::

    sage: from mclf import *
    sage: k = standard_finite_field(4)
    sage: k.natural_subfields()
    [Finite Field of size 2, as a subfield of Finite Field in z2 of size 2^2,
     the standard field with 4 elements]

For any embedding of standard fields, we obtain a subfield::

    sage: F = standard_rational_function_field(k, "x")
    sage: x = F.generator()
    sage: phi = F.hom(F, x^2+1)
    sage: FF = standard_subfield(phi); FF
    Rational function field in x over Finite Field in z2 of size 2^2,
    as a subfield of Rational function field in x over Finite Field in z2
    of size 2^2

The new object carries the following information::

    sage: FF.Subfield()
    Rational function field in x over Finite Field in z2 of size 2^2
    as standard rational function field
    sage: FF.Overfield()
    Rational function field in x over Finite Field in z2 of size 2^2
    as standard rational function field
    sage: FF.embedding()
    the embedding of Rational function field in x over Finite Field in z2
    of size 2^2 into Rational function field in x over Finite Field in z2 of
    size 2^2, sending [x] to [x^2 + 1]

If we want the sub- or overfield as ordinary fields, we use lowercases::

    sage: FF.subfield()
    Rational function field in x over Finite Field in z2 of size 2^2
    sage: FF.overfield()
    Rational function field in x over Finite Field in z2 of size 2^2

We can also say something about the nature of the subfield::

    sage: FF.is_prime_subfield()
    False
    sage: FF.is_canonical_subfield()
    False
    sage: FF.is_constant_base_field()
    False
    sage: FF.is_rational_base_field()
    False
    sage: FF.is_overfield()

"""


from mclf.fields.standard_fields import (StandardField, StandardFiniteField,
                                         StandardNumberField,
                                         StandardFunctionField)
from mclf.fields.embeddings_of_standard_fields import (
    EmbeddingOfStandardFields)


def standard_subfield(*args):
    r""" Return the standard subfield determined by the input.

    INPUT:

    - ``args`` -- data of the following form:

      * an embedding of standard fields `\phi:K\to L`, as a Sage morphism,
        or as an instance of :class:`EmbeddingOfStandardFields \
        <mclf.fields.embeddings_of_standard_fields.EmbeddingOfStandardFields>`
      * standard fields `K, L` such that there is a natural embedding of
        `K` into `L`.

    OUTPUT:

    the object representing `K` as a subfield of `L`, via the given embedding.

    The output is an instance of :class:`StandardSubfield`.

    """
    from mclf.fields.standard_fields import standard_field
    if len(args) == 1:
        phi = args[0]
        if not isinstance(phi, EmbeddingOfStandardFields):
            phi = embeddings_of_standard_fields(phi)
        K = phi.Domain()
    elif len(args) == 2:
        K = args[0]
        L = args[1]
        if not isinstance(K, StandardField):
            K = standard_field(K)
        if not isinstance(L, StandardField):
            L = standard_field(L)
        assert L.contains_as_subfield(K), "K is not a subfield of L"
        phi = L.embedding_of_subfield(K)
    else:
        raise TypeError("wrong number of arguments")
    if K.is_finite():
        return FiniteSubfield(phi)
    elif K.is_number_field():
        return NumberSubfield(phi)
    elif K.is_function_field():
        return FunctionSubfield(phi)
    else:
        raise NotImplementedError()


class StandardSubfield(StandardField):
    r""" Base class for subfields of a standard field.

    An object of this class is a standard field, together with an embedding
    into an overfield.

    INPUT:

    - ``phi`` - an embedding `\phi:K\to L` of standard fields

    OUTPUT:

    the object representing `K` as a subfield of `L`, via the embedding `\phi`.

    Instances of this class should be initialized by the constructor function
    :func:`standard_subfield`.

    """

    def __init__(self, phi):
        # initialize via subclasses
        raise NotImplementedError()

    def __repr__(self):
        return "{}, as a subfield of {}".format(self.subfield(),
                                                self.overfield())

    def Subfield(self):
        r""" Return this subfield, as a standard field.

        """
        return self._subfield

    def subfield(self):
        r""" Return this subfield, as an ordinary field.

        """
        return self.embedding().domain()

    def Overfield(self):
        r""" Return the overfield of this subfield, as a standard field.

        """
        return self._overfield

    def overfield(self):
        r""" Return the overfield of this subfield, as an ordinary field.

        """
        return self.embedding().codomain()

    def embedding(self):
        r""" Return the embedding of this subfield into its overfield.

        """
        return self._embedding

    def is_equal_as_subfield(self, K):
        r""" Return whether this subfield is equal to another one.

        By our definition this means that the two embeddings into the
        overfield are equal as embeddings.

        """
        assert isinstance(K, StandardSubfield)
        return self.embedding().is_equal(K.embedding())

    def is_prime_subfield(self):
        r""" Return whether this standard subfield is the prime subfield
        of its overfield.

        """
        return self.is_prime_field()

    def is_overfield(self):
        r""" Return whether this standard subfield is equal to its overfield.

        """
        return self.embedding().is_surjective()

    def is_canonical_subfield(self):
        r""" Return whether the embedding of this subfield into its overfield
        is a *canonical* embedding of standard fields.

        """
        return self.embedding().is_canonical_embedding()


class FiniteSubfield(StandardSubfield, StandardFiniteField):
    r""" A finite field as a subfield of a standard field.

    An object of this class is a finite field, together with an embedding
    into an overfield.

    INPUT:

    - ``phi`` - an embedding `\phi:K\to L` of standard fields

    `\phi` must be an instance of :class:`EmbeddingOfFiniteField \
    <mclf.fields.embeddings_of_standard_fields.EmbeddingOfFiniteField>`.

    OUTPUT:

    the object representing `K` as a subfield of `L`, via the embedding `\phi`.

    Instances of this class should be initialized by the constructor function
    :func:`standard_subfield`.

    """

    def __init__(self, phi):
        K = phi.Domain()
        L = phi.Codomain()

        # initialize as a finite field
        StandardFiniteField.__init__(self, K)

        # initialize the rest
        self._subfield = K
        self._overfield = L
        self._embedding = phi


class NumberSubfield(StandardSubfield, StandardNumberField):
    r""" A number field as a subfield of a standard field.

    An object of this class is a number field, together with an embedding
    into an overfield.

    INPUT:

    - ``phi`` - an embedding `\phi:K\to L` of standard fields

    `\phi` must be an instance of :class:`EmbeddingOfNumberField \
    <mclf.fields.embeddings_of_standard_fields.EmbeddingOfNumberField>`.

    OUTPUT:

    the object representing `K` as a subfield of `L`, via the embedding `\phi`.

    Instances of this class should be initialized by the constructor function
    :func:`standard_subfield`.

    """

    def __init__(self, phi):
        K = phi.Domain()
        L = phi.Codomain()

        # initialize as a number field
        StandardNumberField.__init__(self, K)

        # initialize the rest
        self._subfield = K
        self._overfield = L
        self._embedding = phi


class FunctionSubfield(StandardSubfield, StandardFunctionField):
    r""" A function field as a subfield of a standard field.

    An object of this class is a function field, together with an embedding
    into an overfield.

    INPUT:

    - ``phi`` - an embedding `\phi:K\to L` of function fields

    `\phi` must be an instance of :class:`EmbeddingOfFunctionField \
    <mclf.fields.embeddings_of_standard_fields.EmbeddingOfFunctionField>`.

    OUTPUT:

    the object representing `K` as a subfield of `L`, via the embedding `\phi`.

    Instances of this class should be initialized by the constructor function
    :func:`standard_subfield`.

    """

    def __init__(self, phi):
        K = phi.Domain()
        L = phi.Codomain()

        # initialize as a function field
        StandardFunctionField.__init__(self, K)

        # initialize the rest
        self._subfield = K
        self._overfield = L
        self._embedding = phi

    def is_constant_base_field(self):
        r""" Return whether this subfield is the constant base field
        of its overfield.

        """
        return self.is_equal(self.Overfield().constant_base_field())

    def is_rational_base_field(self):
        r""" Return whether this subfield is the rational base field
        of its overfield.

        """
        return self.is_equal(self.Overfield().rational_base_field())
