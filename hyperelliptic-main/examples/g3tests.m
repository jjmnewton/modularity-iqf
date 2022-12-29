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
	    SI := ShiodaInvariants(H);
	    _H := HyperellipticCurveFromShiodaInvariants(SI);
            if not ShiodaInvariantsEqual(ShiodaInvariants(_H), SI) then
		"\nARGHH, unconsistent Shioda invariants at H =", H;
		errors := true;
	    end if;
	end if;
    end for;

    if not errors then
	"\nEverything's ok in the Rational Field for Deg =", Deg, "and coeff. bound =", CoeffBound;
    end if;

end procedure;

/* Exhaustive test of degree 5 polynomials */
CheckRationalCurves(7, 1);

/* Exhaustive test of degree 6 polynomials */
CheckRationalCurves(8, 1);

/* 100 random curves of medium size */
allok := true;
Px<x> := PolynomialRing(RationalField()); x := Px.1;
for k := 1 to 100 do
    Pol :=x^8+Px![Random(-10^100,10^100) : i in [1..7]];

    ret, H := IsHyperellipticCurve([Pol, 0]);
    if ret then
        "H :", H;
        SI := ShiodaInvariants(H);
        _H := HyperellipticCurveFromShiodaInvariants(SI);
        if not ShiodaInvariantsEqual(ShiodaInvariants(_H), SI) then
            "\nARGHH, unconsistent invariants at H =", H;
            allok := false;
            break k;
        end if;
        "_H :", _H; "";
    end if;
end for;
if allok then
    "\nEverything's ok for 100 random rational curves of medium size";
end if;
