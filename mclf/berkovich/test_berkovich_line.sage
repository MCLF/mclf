from mac_lane import *
from mclf.berkovich.berkovich_line import BerkovichLine
from mclf.berkovich.berkovich_trees import BerkovichTree
from mclf.berkovich.berkovich_path import AscendingBerkovichPath


vK = pAdicValuation(QQ, 2)
F.<x> = FunctionField(QQ)
X = BerkovichLine(F, vK)

D = X.divisor((x^2+7)*(x^8+4*x+4)*(4*x^4+2*x^2+1)*(x^4+2*x^2+4))

T = BerkovichTree(X)

for xi, m in D:
    T, T1 = T.add_point(xi)


def enumerate_paths(T0, gamma_list):
    for T1 in T0.subtrees():
        gamma_list.append(AscendingBerkovichPath(T0.root(), T1.root()))
        enumerate_paths(T1, gamma_list)

gamma_list = []
enumerate_paths(T, gamma_list)

f = x^8+4*x+4
for gamma in gamma_list:
    xi0 = gamma.initial_point()
    print "xi0 = ", xi0
    print "xi1 = ", gamma.terminal_point()
    s0 = gamma._s0
    print "s0 =", s0
    print "sr =", gamma._sr
    print "h_f(s_0) = ", xi0.v(f)
    if gamma.length() == Infinity:
        t = 1
    else:
        t = gamma.length()/2
    print "t =", t
    print "h_f(s_0+t) =", gamma.point(s0+t).v(f)
    print "delta(s_0)= ", gamma.derivative(f, s0)
    print "---------------------"
