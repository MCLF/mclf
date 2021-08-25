# -*- coding: utf-8 -*-
r"""
Extensions of discrete valuations
=================================

By an **extension of discrete valuations** we mean a triple `(L/K, v, w)`,
where `L/K` is a field extension, `v` is a discrete valuation on `K` and
`w` is a discrete valuation on `L` such that `w|_K` and `v` are equivalent.
We usually just write `w/v` to denote the triple `(L/K, v, w)`.
If `L/K` is finite then we say `w/v` is finite.

To an extension `w/v` of discrete valuations we can associate

- the induced inclusion of value groups `\Gamma_v\hookrightarrow\Gamma_w`,
- the induced embedding of residue fields `\bar{K}_v\hookrightarrow\bar{L}_w`,
- invariants of the above maps, like the *ramification index* and the
  *inertia degree*.

In this module we define a class :class:`ExtensionOfDiscreteValuation`, and a
subclass :class:`FiniteExtensionOfDiscreteValuation` to capture this concept.
An instance of theses classes is defined by the input of `(L/K, v, w)`, and
gives access to the invariants of `w/v` mentioned above.


AUTHORS:

- Stefan Wewers (2021): initial version



"""


from sage.all import SageObject


def extensions_of_discrete_valuation(v, L):
    r""" Return the list of all extensions of a discrete valuation to a
    finite field extension.

    INPUT:

    - ``v`` -- a discrete valuation on a standard field `K`
    - ``L`` -- a finite field extension of `K`, as an instance of
      :class:`FiniteExtensionOfStandardFields <mclf.fields.\
      finite_field_extensions.FiniteExtensionOfStandardFields>`

    OUTPUT:

    the list of all extensions `w` of `v` to `L`, as instances of
    :class:`ExtensionOfDiscreteValuation`.


    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K = standard_number_field(x^2 - 2, "a")
        sage: a = K.generator()
        sage: v = K.valuations(3)[0]
        sage: L = K.extension(x^2 - a)
        sage: extensions_of_discrete_valuation(v, L)[0]
        3-adic valuation on Number Field in x with defining polynomial x^4 - 2
        as a finite extension of 3-adic valuation on Number Field in a
        with defining polynomial x^2 - 2

    """
    from mclf.valuations.discrete_valuations import (
        DiscreteValuationOnStandardField)
    from mclf.fields.finite_field_extensions import (
        FiniteExtensionOfStandardFields)
    assert isinstance(v, DiscreteValuationOnStandardField)
    assert isinstance(L, FiniteExtensionOfStandardFields)
    assert v.Domain().is_equal(L.relative_base_field())
    V = v.extensions(L)
    ret = []
    for w in V:
        ret.append(FiniteExtensionOfDiscreteValuation(L, v, w))
    return ret


def extension_of_restriction(w, phi):
    r""" Return the discrete valuation `w` as an extension of its restriction
    to a subfield.

    INPUT:

    - ``w`` -- a discrete valuation on a standard field `L`
    - ``phi`` -- an embedding of another standard field `K` into `L`,
      `\phi:K\to L`

    OUTPUT:

    the extension `w/v`, where `v:=w\circ\phi` is the restriction of `w` to
    `K` along `\phi`, as an instance of :class:`ExtensionOfDiscreteValuation`.

    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K = standard_number_field(x^2 + x - 1, "a")
        sage: L = standard_number_field(x^4 + x^3 + x^2 + x + 1, "zeta")
        sage: zeta = L.generator()
        sage: phi = K.hom(L, zeta + zeta^4)
        sage: w = L.valuations(2)[0]
        sage: extension_of_restriction(w, phi)
        2-adic valuation on Number Field in zeta with defining polynomial
        x^4 + x^3 + x^2 + x + 1 as an extension of 2-adic valuation on Number
        Field in a with defining polynomial x^2 + x - 1

    """
    from mclf.valuations.discrete_valuations import (
        DiscreteValuationOnStandardField)
    from mclf.fields.embeddings_of_standard_fields import (
        EmbeddingOfStandardFields)
    assert isinstance(w, DiscreteValuationOnStandardField)
    assert isinstance(phi, EmbeddingOfStandardFields)
    assert w.Domain().is_equal(phi.Codomain())
    v = w.restriction(phi)
    return ExtensionOfDiscreteValuation(phi, v, w)


class ExtensionOfDiscreteValuation(SageObject):
    r""" Base class for an extension of discrete valuations.

    INPUT:

    - ``phi`` -- an embedding of standard fields `\phi:K\to L`
    - ``v`` -- a discrete valuation on `K`
    - ``w`` -- a discrete valuation on `L`

    It is assumed that `w` is an **extension** of `v` along `\phi`, meaning
    that the restriction of `w` to `K` via `\phi`, i.e. the valuation
    `w\circ\phi`, is equivalent to `v`.

    OUTPUT:

    the object representing the extension `w/v` of discrete valuations.

    This object gives access to information about this extension, e.g.

    - the ramification index,
    - the induced embedding of residue fields,
      `\bar{\phi}:\bar{K}_v\to\bar{L}_w`,
    - etc.


    """

    def __init__(self, phi, v, w):
        # missing: consistency checks!
        self._valuation = w
        self._base_valuation = v
        self._embedding = phi

    def __repr__(self):
        return "{} as an extension of {}".format(
            self.valuation(), self.base_valuation())

    def valuation(self):
        r""" Return the top valuation of this extension of discrete valuations.

        """
        return self._valuation

    def extension_field(self):
        r""" Return the domain of the top valuation of this extension of
        discrete valuations.

        """
        return self.valuation().domain()

    def base_valuation(self):
        r""" Return the base valuation of this extension of discrete valuations.

        """
        return self._base_valuation

    def base_field(self):
        r""" Return the domain of the base valuation of this extension of
        discrete valuations.

        """
        return self.base_valuation().domain()

    def embedding(self):
        r""" Return the embedding of the base field into the extension field
        of this extension of discrete valuations.

        """
        return self._embedding

    def residue_field_extension(self):
        r""" Return the extension of residue fields induced by this extension
        of discrete valuations.

        OUTPUT:

        the embedding of residue fields

        .. MATH::

            \bar{\phi}:\bar{K}_v \to\bar{L}_w

        induced by this extension `w/v` of discrete valuations.

        .. NOTE::

            In case the residue field extension is finite, it would be neater
            to return the *finite field extensions*. But maybe it is better
            to be consistent rather than neat.

            Therefore, we have the method
            :meth:`finite_residue_field_extension \
            <ExtensionOfDiscreteValuation.finite_residue_field_extension>`

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^2 + x - 1, "a")
            sage: L = standard_number_field(x^4 + x^3 + x^2 + x + 1, "zeta")
            sage: zeta = L.generator()
            sage: phi = K.hom(L, zeta + zeta^4)
            sage: w = L.valuations(2)[0]
            sage: w_v = extension_of_restriction(w, phi)
            sage: w_v.residue_field_extension()
            the embedding of Finite Field in z2 of size 2^2 into Finite Field
            in z4 of size 2^4, sending z2 to z4^2 + z4

        """
        if not hasattr(self, "_residue_field_extension"):
            Kb = self.base_valuation().Residue_field()
            Lb = self.valuation().Residue_field()
            gens = Kb.absolute_generators()
            image_gens = [self._embedding_of_residue_fields(a) for a in gens]
            phib = Kb.hom(Lb, image_gens)
            self._residue_field_extension = phib
        return self._residue_field_extension

    def _embedding_of_residue_fields(self, a):
        r""" Helper function for :meth:`residue_field_extension`.

        INPUT:

        - ``a`` -- an element in the residue field of the base field

        OUTPUT:

        the image of `a` under the induced embedding of residue fields,
        `\bar{K}_v\to\bar{L}_w`.

        """
        v = self.base_valuation()
        w = self.valuation()
        phi = self.embedding()
        return w.reduce(phi(v.lift(a)))

    def finite_residue_field_extension(self):
        r""" Return the finite extension of residue fields induced by this
        extension of discrete valuations.

        OUTPUT:

        the finite extension of residue fields

        .. MATH::

            \bar{L}_w/\bar{K}_v

        induced by this extension `w/v` of discrete valuations, as an instance
        of :class:`FiniteExtensionOfStandardFields <mclf.fields.\
        finite_field_extensions.FiniteExtensionOfStandardFields>`.


        """
        if not hasattr(self, "_finite_residue_field_extension"):
            from mclf.fields.finite_field_extensions import (
                finite_field_extension)
            phib = self.residue_field_extension()
            assert phib.is_finite(), "the residue field extension is not finite"
            self._finite_residue_field_extension = finite_field_extension(phib)
        return self._finite_residue_field_extension


class FiniteExtensionOfDiscreteValuation(ExtensionOfDiscreteValuation):
    r""" Class for a finite extension of discrete valuations.

    INPUT:

    - ``L`` -- a finite extension of standard fields, `L/K`
    - ``v`` -- a discrete valuation on `K`
    - ``w`` -- a discrete valuation on `L`, extending `v`

    OUTPUT:

    the object representing the finite extension `w/v` of discrete valuations.

    """

    def __init__(self, L, v, w):
        # missing: consistency checks!
        self._valuation = w
        self._base_valuation = v
        self._embedding = L.embedding_of_base_field()
        self._finite_field_extension = L

    def __repr__(self):
        return "{} as a finite extension of {}".format(
            self.valuation(), self.base_valuation())

    def finite_field_extension(self):
        r""" Return the finite extension of fields underlying this extension
        of discrete valuations.

        """
        return self._finite_field_extension

    def degree(self):
        r""" Return the degree of this finite extension of discrete valuations.

        """
        return self.finite_field_extension().degree()

    def inertia_degree(self):
        r""" Return the inertia degree of this finite extension of discrete
        valuations.

        """
        return self.finite_residue_field_extension().degree()
