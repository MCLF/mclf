from mclf.berkovich.berkovich_line import *
from mclf.berkovich.berkovich_trees import *

K = QQ
vK = pAdicValuation(K, 2)

F.<x> = FunctionField(K)
X = BerkovichLine(F, vK)

f = (x^2+7)*(x^2-7)/x/(2*x-1)*(x^4+4)/(x^2+2)*(x+1)*(4*x+1)*(x^8-4)
D = X.divisor(f)
xi = [xi1 for xi1, m in D]

T = BerkovichTree(X)
for xi1 in xi:
    T = T.add_point(xi1)
