# -*- coding: utf-8 -*-
from sage.all import QQ, PolynomialRing, FunctionField
from mclf import SuperellipticCurve, SemistableModel, SmoothProjectiveCurve

class PicardCurve:
    r"""
    Performance benchmarks for the curve from our
    README.

    TESTS::

        sage: import mclf.benchmarks.semistable
        sage: mclf.benchmarks.semistable.PicardCurve().time_is_semistable()
        True

    """
    def time_is_semistable(self):
        R = PolynomialRing(QQ, 'x')
        x = R.gen()
        Y = SuperellipticCurve(x**4 - 1, 3)
        v_2 = QQ.valuation(2)
        Y2 = SemistableModel(Y, v_2)
        return Y2.is_semistable()

class JSMCurve:
    r"""
    A test case that Jan Steffen Müller came up with and that caused trouble at
    some point.

    TESTS::

        sage: import mclf.benchmarks.semistable
        sage: mclf.benchmarks.semistable.JSMCurve().time_is_semistable()
        doctest:warning
        ...
        UserWarning: ...
        True

    """
    def time_is_semistable(self):
        K = FunctionField(QQ, 'x')
        x = K.gen()
        R = PolynomialRing(K, 'T')
        T = R.gen()
        f = 64*x**3*T - 64*x**3 + 36*x**2*T**2 + 208*x**2*T + 192*x**2 + 9*x*T**3 + 72*x*T**2 + 240*x*T + 64*x +T**4 + 9*T**3 + 52*T**2 + 48*T
        L = K.extension(f, 'y')
        Y = SmoothProjectiveCurve(L)
        v = QQ.valuation(13)
        M = SemistableModel(Y, v)
        return M.is_semistable()
