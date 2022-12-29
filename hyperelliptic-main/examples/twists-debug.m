//////// Hyperelliptic case
SetSeed(1);

NormalizedM := function(M)
  N := Nrows(M);
  for j in [1 .. N] do
    for i in [1 .. N] do
      if M[i,j] ne 0 then
        return 1/M[i,j]*M;
      end if;
    end for;
  end for;
  printf("Error, your matrix is zero");
  return 0;
end function;

P<x>:=PolynomialRing(GF(7));
f:=x^8+1;
//f:=x^8+14*x^4+1;
//f:=x^7-1;
//f:=x*(x^6-1);
f:=x^12-1;
//f:=x^5-x;
//f:= x^6 + x^3 + 3;
C:=HyperellipticCurve(f);
g:=Genus(C);
T1:=Twists(C);

X1 := T1[1];
X2 := T1[2];
print IsIsomorphicHyperellipticCurves(X1, X2);
