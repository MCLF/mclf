# -*- coding: utf-8 -*-
r"""
Valued field extensions
=======================



"""

from mclf.field_extensions.field_extensions import FieldExtension, FiniteFieldExtension


class ValuedFieldExtension(FieldExtension):
    pass


class FiniteValuedFieldExtension(ValuedFieldExtension, FiniteFieldExtension):
    pass
