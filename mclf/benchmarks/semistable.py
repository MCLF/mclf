from sage.all import QQ, PolynomialRing
from mclf import SuperellipticCurve, SemistableModel

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
