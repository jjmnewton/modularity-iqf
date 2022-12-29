SetVerbose("IsGL2Equiv", 0);
SetSeed(1340053158);

R<x> := PolynomialRing(Rationals());
f := x^2 + x + 1; K := NumberField(f);
K := Rationals();
P<x> := PolynomialRing(K);
f1 := x^12 - 1;
C1 := HyperellipticCurve(f1);
f2 := 173*(x^12 + 1);
C2 := HyperellipticCurve(f2);

time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2);
print test; print Ts;
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true);
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true, commonfield := true);

R<x> := PolynomialRing(Rationals());
f := x^2 + x + 1; K := NumberField(f);
K := Rationals();
P<x> := PolynomialRing(K);
f1 := x^6 + x + 1;
C1 := HyperellipticCurve(f1);
f2 := 173*(x^6 + x + 1);
C2 := HyperellipticCurve(f2);

time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2);
print test; print Ts;
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true);
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true, commonfield := true);
print test; print Ts;

R<x> := PolynomialRing(Rationals());
f := x^2 + x + 1; K := NumberField(f);
K := Rationals();
P<x> := PolynomialRing(K);
f1 := x^6 + x + 1;
C1 := HyperellipticCurve(f1);
f2 := f1^Matrix(K, [[2,3],[5,17]]);
C2 := HyperellipticCurve(f2);

time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2);
print test; print Ts;
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true);
time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true, commonfield := true);
print test; print Ts;
