import "magma/TernaryForms.m": Dehomogenization,Homogenization;

SetSeed(1);
SetVerbose("IsGL2Equiv", 0);

F := FiniteField(NextPrime(10^6));
F := FiniteField(NextPrime(10^6), 3);
F := Rationals();
F := NumberField(x^2+x+1);
_<x> := PolynomialRing(F);

f := x^6 + x^5 + 2*x^3 + 5*x^2 + x + 1; g := f; deg := 6;
f := x^5 + x; g := f; deg := 6;
f := 4*x^6 + 1; g := f; deg := 6;

_, IsoLst := IsGL2EquivalentExtended(f, g, deg : commonfield := false, covariant := true);
_, IsoLst := IsGL2EquivalentExtended(f, g, deg : commonfield := false, covariant := false);
print "Covariant:";
time _, IsoLst := IsGL2EquivalentExtended(f, g, deg : commonfield := true, covariant := true);
print "Direct:";
time _, IsoLst := IsGL2EquivalentExtended(f, g, deg : commonfield := true, covariant := false);
print #IsoLst;
print IsoLst;
print BaseRing(IsoLst[1]);

deg := 50; B := 100; D := [-B..B];
while true do
    repeat
        f := &+[ Random(D)*x^i : i in [0..deg] ];
    until Degree(f) eq deg and Discriminant(f) ne 0;
    repeat
        T := Matrix(F, 2, 2, [ Random(D) : i in [1..4] ]);
        //T := Matrix(F, 2, 2, [ 0 ] cat [ Random(D) : i in [1..3] ]);
    until Determinant(T) ne 0;
    g := f^T;
    X := HyperellipticCurve(f); Y := HyperellipticCurve(g);
    print "Covariant:";
    time _, IsoLst := IsIsomorphicHyperellipticCurves(X, Y : geometric := false, covariant := true);
    print "Direct:";
    time _, IsoLst := IsIsomorphicHyperellipticCurves(X, Y : geometric := false, covariant := false);
    print T;
    print IsoLst[1];
end while;
