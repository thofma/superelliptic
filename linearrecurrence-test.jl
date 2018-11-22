using Nemo
include("linearrecurrence.jl")


Br= ResidueRing(ZZ,107)
Ri,x = PolynomialRing(Br,'x')
M = matrix(Ri,3,3,[0,0,2,105,0,0,0,105,0])
L = [0];
R = [103];
s=Int64(floor(log(4,R[length(R)])));
DDi= UpperCaseDD(Br(1),Br(2)^s,2^s)^(-1);
println(parent(DDi))
println(parent(M))
println(LinearRecurrence(M, L, R, DDi, s))
