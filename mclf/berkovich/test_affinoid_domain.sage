

from mclf.berkovich.berkovich_trees import BerkovichTree
from mclf.berkovich.affinoid_domain import AffinoidTree, AffinoidDomainOnBerkovichLine, RationalDomainOnBerkovichLine


K = QQ
vK = pAdicValuation(K, 2)
F.<x> = FunctionField(K)
X = BerkovichLine(F, vK)
X


R = F._ring
y = R.gen()
xi0 = X.gauss_point()
xi1 = X.point_from_discoid(x^2+2, 3/2)
xi2 = X.point_from_discoid(x^4+2, 3/2)
xi3 = X.point_from_discoid(x^2+x+1, 1)
xi4 = X.point_from_discoid(x^2+2, 2, False)

U1 = AffinoidTree(X)
U1 = U1.add_points([xi0], [xi1, xi3])
U2 = AffinoidTree(X)
U2 = U2.add_points([xi2], [xi4])

U = U1.union(U2)
U
