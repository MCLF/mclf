r""" Piecewise affine functions on the positive real line.




"""

from sage.structure.sage_object import SageObject
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import Infinity


class PiecewiseAffineFunction(SageObject):
    r""" Defines a piecewise affine function on `[0,\infty]`.

    INPUT:

    - ``c0`` -- a rational number
    - ``kinks`` -- a strictly increasing list of positive rational numbers
    - ``slopes`` -- a list of rational numbers; with one elements less then ``kinks``

    OUTPUT:

    The continous, piecewise affine function `f` on the interval `[0,\infty]`
    such that
    1. `f` takes the value ``c0`` at zero
    2.  `f` is not continous at most at the points in ``kinks``
    3.  on the intervals between the kinks, `f` is affine with slopes given by
        the entries of ``slopes``; the first interval start with zero.

    """


    def __init__(self, c0, kinks, slopes):

        assert len(kinks) == len(slopes) - 1
        kinks.append(Infinity)
        for s in kinks:
            print s
        self._c0 = c0
        self._kinks = kinks
        self._slopes = slopes


    def __call__(self, t):

        value = self._c0
        t0 = 0
        for kink, slope in zip(self._kinks, self._slopes):
            if t <= kink:
                return value + (t-t0)*slope
            else:
                value = value + (kink-t0)*slope
                t0 = kink
        return value
