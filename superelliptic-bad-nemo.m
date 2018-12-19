AttachSpec("superelliptic");


Br:=GF( 379^1);
w := Br.1;
Ri<x> := PolynomialRing(Br);


print(ZetaFunction(3, x^7+x+ 1));

