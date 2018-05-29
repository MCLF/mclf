r"""


AUTHORS:

- Stefan Wewers (2017-09-01): initial version


EXAMPLES:



TO DO:



"""

#*****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import SageObject


class ElementOfFakepAdicCompletion(SageObject):
    r"""
    Return an element of an `p`-adic number field.

    INPUT:

    - ``K`` -- a `p`-adic number field (an instance of ``FakepAdicCompletion``)
    - ``alpha0`` -- an object representing or approximating an element of `K`

    OUTPUT:

    the element `\alpha` of `K` corresponding to `\alpha_0`.

    More precisely, ``alpha0`` can be any one of the following objects:

    - an element of the number field `K_0` underlying `K`
    - a pair `(\alpha_0, N)`, where `\alpha_0` is in `K_0` and `N` is a positive integer
    - a discrete valuation `v` on `K_0[x]` which extends the base valuation `v_K`
      on `K_0`, which is augmented from the Gauss valuation `v_0` and of the form

      .. MATH::

            v = [v_0, v(x-\alpha) = s],

      with `\alpha_0\in K_0` and `s>0`.
    - a limit pseudo valuation `v` on `K_0[x]` which is approximated by a
      valuation as before.

    """
    pass
