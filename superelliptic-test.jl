using Nemo
include("superelliptic.jl")


Br,w= FiniteField(107,1,"l")
Ri,x = PolynomialRing(Br,'x')
M = matrix(Ri,2,2,[x,x,1,x+1])
L = [11,13]
R = [13,15]
#print(LinearRecurrence(M, L, R))
ZetaFunction(2, x^3+ 1)



