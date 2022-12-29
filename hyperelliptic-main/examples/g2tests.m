/***
 *  Examples of use of the g2twists package
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright 2007-2020 R. Lercier & C. Ritzenthaler
 */

// SetVerbose("Hyperelliptic", 2);

/* Finite Field Enumeration
 ***************************/

/* Data structures */
FFEnum  := recformat< FF, p, n, q, t, x>;

/* Initialisation */
FFEnumInit := function(FF, t)
    FFCtxt := rec<FFEnum |
                  FF := FF,
                  p := Characteristic(FF),
                  n := Degree(FF),
		  q := #FF,
		  t := t,
		  x := 0>;
   return FFCtxt;
end function;

/* Enumeration of a vector of finite fields elements */
FFEnumNext := procedure(~V, ~FFCtxt)
    q := FFCtxt`q; p := FFCtxt`p; n := FFCtxt`n;
    x := FFCtxt`x; t := FFCtxt`t;

    X := Intseq(x+q^t, p)[1..n*t];
    FFCtxt`x +:= 1;
    FFCtxt`x := FFCtxt`x mod q^(n*t);

    V := [FFCtxt`FF!X[1+k*n .. (k+1)*n] : k in [0..(t-1)]];
end procedure;


/* Genus 2 Curves Enumeration
 ****************************/
G2Enumerate := function(FF)
    FFCtxt := FFEnumInit(FF, 3);
    AllCurves := [];
    for i := 1 to #FF^3 do
	FFEnumNext(~S, ~FFCtxt);
	Curves, G := Twists(S);
	AllCurves cat:= [[* G, Curves*]];
    end for;
    return AllCurves;
end function;

ExtractCurves := function(Ecs, v)
    L := [];
    for e in Ecs do
	if #e[1] eq #v then
	    Append(~L, e[2]);
	end if;
    end for;
    return L;
end function;

G2NonIsomorphic := function(Ecs)
   crvs := [];
   for E1 in Ecs do
       old := &or[ IsIsomorphic(E1,E0) : E0 in crvs ];
       if not old then Append(~crvs,E1); end if;
  end for;
  return crvs;
end function;

/* Some tests in function fields
 *******************************/

/* Characteristic 2 fields */
F<a,b,c> := FunctionField(GF(2),3);
errors := false;

GI := [a,b,c]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [0,b,c]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [b^2*c,b^2,c]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [c^3,c^2,c]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [0,0,c^2]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [0,0,0]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

if not errors then
    "\nEverything's ok in function fields of characteristic 2";
else
    "\nARGHH, errors in function fields of characteristic 2";
end if;

/* Characteristic 3 fields */
F<a,b,c> := FunctionField(GF(3),3);
errors := false;

//GI := [a,b,c]; H := HyperellipticCurveFromG2Invariants(GI);
//errors or:= G2Invariants(H) ne GI;

GI := [0,0,0]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [F!50000, 3750, -125]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [2*a^3,0,1]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

if not errors then
    "\nEverything's ok in function fields of characteristic 3";
else
    "\nARGHH, errors in function fields of characteristic 3";
end if;

/* Characteristic 5 fields */
F<a,b,c> := FunctionField(GF(5),3);
errors := false;

//GI := [a,b,c]; H := HyperellipticCurveFromG2Invariants(GI);
//errors or:= G2Invariants(H) ne GI;

GI := [0,0,0]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [
    3/(a^5 + 3*a^4 + 3*a^3 + a^2),
    2/(a^4 + 2*a^3 + a^2),
    4/(a^3 + a^2)
    ]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [
    2/(a^5 + 2*a^4 + a^3),
    (2*a + 3)/(a^5 + 2*a^4 + a^3),
    1/a^3
    ]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

if not errors then
    "\nEverything's ok in function fields of characteristic 5";
else
    "\nARGHH, errors in function fields of characteristic 5";
end if;

/* Characteristic 7 fields */
F<a,b,c> := FunctionField(GF(7),3);
errors := false;

//GI := [a,b,c]; H := HyperellipticCurveFromG2Invariants(GI);
//errors or:= G2Invariants(H) ne GI;

GI := [0,0,0]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [F!50000, 3750, -125]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [
    (4*a^5 + 3*a^4 + 3*a^3 + 5*a^2 + 3*a + 1)/(a^5 + a^4 + 5*a^3 + 6*a^2),
    (4*a^4 + a^2 + 3*a + 1)/(a^4 + 3*a^3 + 4*a^2),
    (a^3 + 4*a^2 + 5*a + 6)/(a^3 + 5*a^2)
]; H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

GI := [
    (6*a^5 + a^4 + a^3 + 4*a^2 + a + 5)/(a^5 + 3*a^4 + 4*a^3),
    (5*a^5 + 5*a^4 + 4*a^3 + 3*a^2 + 4*a + 4)/(a^5 + 3*a^4 + 4*a^3),
    (a^3 + 2*a^2 + 3*a + 2)/a^3
    ];H := HyperellipticCurveFromG2Invariants(GI);
errors or:= G2Invariants(H) ne GI;

if not errors then
    "\nEverything's ok in function fields of characteristic 7";
else
    "\nARGHH, errors in function fields of characteristic 7";
end if;

/* Some tests in finite fields
 *****************************/
CheckThatEverythingIsOK := procedure(FF)

     Grps, NbGrps := GeometricAutomorphismGroupGenus2Classification(FF);
     AllCurves := G2Enumerate(FF);

     errors := false;

    FFCtxt := FFEnumInit(FF, 3);
    for i := 1 to #FF^3 do
	FFEnumNext(~S, ~FFCtxt);

	if Characteristic(FF) ne 2 and
	    #G2NonIsomorphic(AllCurves[i][2]) ne #AllCurves[i][2] then
	    "\nARGHH, Isomorphic twists in", AllCurves[i];
	     errors := true;
	end if;

	for h in AllCurves[i][2] do
	    if IgusaToG2Invariants(JInvariants(h)) ne S then
		"\nARGHH, unconsistent G2 invariants at S=", S;
		errors := true;
	    end if;
	    if Genus(h) ne 2 then
		"\nARGHH, non-genus 2 curve in", AllCurves[i];
		errors := true;
	    end if;
	end for;

    end for;

    for i := 1 to #Grps do
	extracted := ExtractCurves(AllCurves, Grps[i]);
	if #extracted ne NbGrps[i] then
	    "\nARGHH,",
		NbGrps[i],
		"isomorphic classes of curves ewith automorphism group",Grps[i], "expected";
	    "    .... but", #extracted, "computed.";
	    errors := true;
	end if;
    end for;
    if #AllCurves ne &+NbGrps then
	"\nARGHH,", &+NbGrps, "isomorphic classes of curves expected";
	"    .... but", #AllCurves, "classes computed";
	errors := true;
    end if;

    if not errors then
	"\nEverything's ok in a", FF;
    end if;

end procedure;

/* In characteristic 2 */
FF := GF(2^1); CheckThatEverythingIsOK(FF);
FF := GF(2^2); CheckThatEverythingIsOK(FF);
FF := GF(2^3); CheckThatEverythingIsOK(FF);
FF := GF(2^4); CheckThatEverythingIsOK(FF);

/* In characteristic 3 */
FF := GF(3^1); CheckThatEverythingIsOK(FF);
FF := GF(3^2); CheckThatEverythingIsOK(FF);

/* In characteristic 5 */
FF := GF(5^1); CheckThatEverythingIsOK(FF);
//FF := GF(5^2); CheckThatEverythingIsOK(FF);

/* In characteristic 7 */
FF := GF(7^1); CheckThatEverythingIsOK(FF);

/* In characteristic 11 */
FF := GF(11^1); CheckThatEverythingIsOK(FF);

/* In characteristic 23 */
//FF := GF(23^1); CheckThatEverythingIsOK(FF);

/* Over the rationals
 *********************/
CheckRationalCurves := procedure(Deg, CoeffBound)

    errors := false;

    Px<x> := PolynomialRing(RationalField()); x := Px.1;
    for e := 0 to (2*CoeffBound)^Deg-1 do
	Coeffs := Intseq(e, 2*CoeffBound);
	Coeffs := [0 : c in [1..(Deg-#Coeffs)]] cat Coeffs;
        Pol :=x^Deg+Px![c-CoeffBound+1 : c in Coeffs];
	ret, H := IsHyperellipticCurve([Pol, 0]);
        if ret then
            // ""; "*** Pol :", Pol;
	    GI := G2Invariants(H);
	    _H := HyperellipticCurveFromIgusaInvariants(IgusaInvariants(H));
	    if G2Invariants(_H) ne GI then
		"\nARGHH, unconsistent G2 invariants at H =", H;
		errors := true;
	    end if;
	end if;
    end for;

    if not errors then
	"\nEverything's ok in the Rational Field for Deg =", Deg, "and coeff. bound =", CoeffBound;
    end if;

end procedure;

/* Exhaustive test of degree 5 polynomials */
CheckRationalCurves(5, 2);

/* Exhaustive test of degree 6 polynomials */
CheckRationalCurves(6, 2);

/* 100 random curves of medium size */
allok := true;
Px<x> := PolynomialRing(RationalField()); x := Px.1;
for k := 1 to 100 do
    Pol :=x^6+Px![Random(-10^100,10^100) : i in [1..5]];

    ret, H := IsHyperellipticCurve([Pol, 0]);
    if ret then
        // "H :", H;
        GI := G2Invariants(H);
        _H := HyperellipticCurveFromIgusaInvariants(IgusaInvariants(Pol : extend := true));
        if G2Invariants(_H) ne GI then
            "\nARGHH, unconsistent invariants at H =", H;
            allok := false;
            break k;
        end if;
        // "_H :", _H;
    end if;
end for;
if allok then
    "\nEverything's ok for 100 random rational curves of medium size";
end if;
