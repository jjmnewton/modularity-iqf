//freeze;

/***
 *  Reconstructing genus 2 hyperelliptic curves with the conic and cubic method.
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
 *  Copyright 2011-2020, R. Lercier & C. Ritzenthaler & J. Sijsling
 */

import "g2conic_123.m"    : Genus2ConicAndCubic123;

import "g2conic_uv1245.m" : Genus2ConicAndCubicUV1245;
import "g2conic_uv1246.m" : Genus2ConicAndCubicUV1246;

import "../toolbox/sl2invtools.m" : WPSMinimizeQQ;
import "../toolbox/diophantine.m" : LimitedFactorization, ConicParametrization, MinimizeLinearEquationOverRationals;

function Genus2ConicAndCubic(JI : models := true, RationalModel := true, Deterministic := false)

    FF := Universe(JI);

    R := FF!0;
    if true and Type(FF) eq FldRat and RationalModel eq true then

        Puv := PolynomialRing(FF, 2); u := Puv.1; v := Puv.2;
        R := Puv!0;

        ret := true; sqrQ := 1;
        if #JI eq 6 then
            JI := WPSMinimizeQQ([2, 4, 6, 8, 10, 15], JI);
        else

            /* Let us recover J15
             ***/
            JI := WPSMinimizeQQ([1, 2, 3, 4, 5], JI);
            J2, J4, J6, J8, J10 := Explode(JI);

            J15_2 := 2^22 * (
                J2^6*J6^3-2*J2^5*J4^2*J6^2+J2^4*J4^4*J6-72*J10*J2^5*J4*J6+8*J10*J2^4*J4^3-72*J2^4*J4*J6^3+136*J2^3*J4^3*J6^2-64*J2^2*J4^5*J6-432*J10^2*J2^5-48*J10*J2^4*J6^2+4816*J10*J2^3*J4^2*J6-512*J10*J2^2*J4^4 +216*J2^3*J6^4+1080*J2^2*J4^2*J6^3-2304*J2*J4^4*J6^2+1024*J4^6*J6+28800*J10^2*J2^3*J4-12960*J10*J2^2*J4*J6^2-84480*J10*J2*J4^3*J6+8192*J10*J4^5-7776*J2*J4*J6^4+6912*J4^3*J6^3-96000*J10^2*J2^2*J6-512000*J10^2*J2*J4^2-129600*J10*J2*J6^3+691200*J10*J4^2*J6^2+11664*J6^5+11520000*J10^2*J4*J6+51200000*J10^3
                );

            if J15_2 lt 0 then
                J2  *:= -1; J6  *:= -1; J8  *:= -1; J10 *:= -1; J15_2 *:= -1;
            end if;

            vprintf Hyperelliptic, 2 :  "J15_2 := %o;\n", J15_2;

            /* Let us make J15_ 2 be a square (if not too hard) */
            F, Q := TrialDivision(Numerator(J15_2), 10^6 : Proof := false);
            if #Q gt 0 then
                ret, _ := IsSquare(&*Q);
            end if;

            if ret eq false then
                F, _, Q := LimitedFactorization(Numerator(J15_2));
                if assigned(Q) then
                    ret, _ := IsSquare(&*Q);
                end if;
            end if;

            vprintf Hyperelliptic, 2 :  "J15_2 := %o * %o;\n", F, Q;

            if ret then
                for fct in F do
                    if fct[2] mod 2 eq 1 then
                        J2  *:= fct[1]; J4  *:= fct[1]^2; J6  *:= fct[1]^3;
                        J8  *:= fct[1]^4; J10 *:= fct[1]^5; J15_2 *:= fct[1]^15;
                    end if;
                end for;
                ret, J15 := IsSquare(AbsoluteValue(J15_2));
            end if;

            if ret then JI := [J2, J4, J6, J8, J10, J15]; end if;

        end if;

        if ret then
            vprintf Hyperelliptic, 2 :  "[J2, J4, J6, J8, J10, J15] = %o\n\n", JI;

            Genus2ConicAndCubicUVFct := Genus2ConicAndCubicUV1245;
            R, _, _ := Genus2ConicAndCubicUVFct([u, v], JI : models := false);

            if R eq 0 or Degree(R,u)*Degree(R,v) eq 0 then
                Genus2ConicAndCubicUVFct := Genus2ConicAndCubicUV1246;
                R, _, _ := Genus2ConicAndCubicUVFct([u, v], JI : models := false);
            end if;

        end if;

        /* Let us find a conic with small discriminant */
	if R ne 0 and Degree(R,u)*Degree(R,v) ne 0 then

	    vprintf Hyperelliptic, 2 :  "Let us minimize the discriminant of the conic to be used, i.e %o\n\n", R;

	    U, V := MinimizeLinearEquationOverRationals(R);

	    vprintf Hyperelliptic, 2 :  "We set :";
	    vprintf Hyperelliptic, 2 :  "  u = %o\n", U;
	    vprintf Hyperelliptic, 2 :  "  v = %o\n", V;

	    R, C, M := Genus2ConicAndCubicUVFct([FF | U, V], JI : models := models);

	    vprintf Hyperelliptic, 2 :  "So that :";
	    vprintf Hyperelliptic, 2 :  "  R = %o\n", R;

	    /* Let us first remove the content of C and M */
	    ct := LCM([Denominator(c) : c in Coefficients(C)]) /
		  GCD([Numerator(c) : c in Coefficients(C)]);
	    C *:= ct;
	    ct := LCM([Denominator(c) : c in Coefficients(M)]) /
		GCD([Numerator(c) : c in Coefficients(M)]);
	    M *:= ct;

            vprintf Hyperelliptic, 2 :
               "Factorization of conic discriminant before reduction: %o\n",
                Factorization(Integers() ! Discriminant(Conic(ProjectiveSpace(Parent(C)), C)));

            vprintf Hyperelliptic, 2 : "Minimal model step...\n";
	    Cphi, phi := MinimalModel(Conic(ProjectiveSpace(Parent(C)), C));
	    C := DefiningPolynomial(Cphi);
	    M := Evaluate(M, DefiningPolynomials(phi));
	    ct := GCD([Denominator(c) : c in Coefficients(M)]) /
		  GCD([Numerator(c) : c in Coefficients(M)]);
	    M *:= ct;
	    vprintf Hyperelliptic, 2 :  "Conic %o\n", C;
	    vprintf Hyperelliptic, 2 :  "Cubic %o\n", M;

	else
	    R := FF!0;
	    vprintf Hyperelliptic, 2 :  "None parametric conic works ! Let us do it as usual...\n\n", R;
	end if;
    end if;

    if R eq 0 then R, C, M := Genus2ConicAndCubic123(JI : models := models); end if;

    /* Hum, hum... No non-degenrate conic found, return immediatly */
    if R eq 0 then return false; end if;

    /* Computing conic and cubic */
    if models then

        phi := ConicParametrization(C :
            RationalPoint := RationalModel, RandomLine := not Deterministic);

	f := Evaluate(M, DefiningPolynomials(phi));

        g := UnivariatePolynomial(Evaluate(f, Parent(f).2, 1));

        vprintf Hyperelliptic, 1 :  "Hyperelliptic polynomial: %o\n", g;
	return g;

    end if;

    return true;

end function;
