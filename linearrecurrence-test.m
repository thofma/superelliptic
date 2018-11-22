AttachSpec("superelliptic");

Br:=Integers(107);
Ri<x> := PolynomialRing(Br);
M := Matrix(Ri, [[0,0,2],[105,0,0],[0,105,0]]);
L := [0];
R := [103];
s:=Floor(Log(4,R[#R]));
DDi:= UpperCaseDD(Br!1,Br!(2^s),2^s)^(-1);
LinearRecurrence(M, L, R, DDi, s);
print "expected";
