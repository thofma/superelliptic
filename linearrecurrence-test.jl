using Nemo
include("linearrecurrence.jl")


Br= QadicField(107,2,2)
Ri,t = PolynomialRing(Br,'t')
M = matrix(Ri,5,5,[0, 0, 0, 0, 3*t, 131079598*t+520, 0, 0, 0, 3*t+131079497, 0, 131079598*t+520, 0, 0, 0, 0, 0, 131079598*t+520, 0, 0, 0, 0, 0, 131079598*t+520, 0])
L =[0, 107, 214, 321]
R = [101, 208, 315, 422]
s=4
DDi= Br(84664426)
println(LinearRecurrence(M, L, R, DDi, s))
