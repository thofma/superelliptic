using Nemo
include("superelliptic.jl")

Br,w = FiniteField(379,1,"l")

Ri,x = PolynomialRing(Br,'x')

print(ZetaFunction(3, x^7+x+ 1))
