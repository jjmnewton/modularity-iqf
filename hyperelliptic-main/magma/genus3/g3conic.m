//freeze;

/***
 *  Reconstructing genus 3 hyperelliptic curves with the conic and quartic method.
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
 *  Copyright 2011, R. Lercier & C. Ritzenthaler & J. Sijsling & J. Sijsling
 */

import "conic_123.m" : Genus3ConicAndQuartic123;
import "conic_124.m" : Genus3ConicAndQuartic124;
import "conic_157.m" : Genus3ConicAndQuartic157;
import "conic_136.m" : Genus3ConicAndQuartic136;
import "conic_148.m" : Genus3ConicAndQuartic148;
import "conic_129.m" : Genus3ConicAndQuartic129;

import "conic_125.m" : Genus3ConicAndQuartic125;
import "conic_126.m" : Genus3ConicAndQuartic126;
import "conic_128.m" : Genus3ConicAndQuartic128;
import "conic_146.m" : Genus3ConicAndQuartic146;
import "conic_137.m" : Genus3ConicAndQuartic137;
import "conic_247.m" : Genus3ConicAndQuartic247;
import "conic_1210.m" : Genus3ConicAndQuartic1210;
import "conic_1310.m" : Genus3ConicAndQuartic1310;
import "conic_1211.m" : Genus3ConicAndQuartic1211;
import "conic_1411.m" : Genus3ConicAndQuartic1411;
import "conic_1312.m" : Genus3ConicAndQuartic1312;
import "conic_1313.m" : Genus3ConicAndQuartic1313;
import "conic_1612.m" : Genus3ConicAndQuartic1612;

import "conic_uv.m" : Genus3ConicAndQuarticUV;

import "../toolbox/diophantine.m" : ConicParametrization, MinimizeLinearEquationOverRationals;

function Genus3ConicAndQuartic(JI : models := true, RationalModel := true, Deterministic := false, minimize := true)

    FF := Universe(JI);

    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    R := FF!0;

    if Type(FF) eq FldRat and RationalModel eq true then

	Puv := PolynomialRing(FF, 2); u := Puv.1; v := Puv.2;

	R, _, _ := Genus3ConicAndQuarticUV([u, v], JI : models := false);

	if R ne 0 and Degree(R,u)*Degree(R,v) ne 0 then

	    /* Let us find a conic with small discriminant */

	    vprintf Hyperelliptic, 2 :  "Let us minimize the discriminant of the conic to be used, i.e %o\n\n", R;

	    U, V := MinimizeLinearEquationOverRationals(R);

	    vprintf Hyperelliptic, 2 :  "We set :";
	    vprintf Hyperelliptic, 2 :  "  u = %o\n", U;
	    vprintf Hyperelliptic, 2 :  "  v = %o\n", V;

	    R, C, Q := Genus3ConicAndQuarticUV([FF | U, V], JI : models := models);

	    vprintf Hyperelliptic, 2 :  "So that :";
	    vprintf Hyperelliptic, 2 :  "  R = %o\n", R;

	    /* Let us first remove the content of C and Q */
	    ct := LCM([Denominator(c) : c in Coefficients(C)]) /
		  GCD([Numerator(c) : c in Coefficients(C)]);
	    C *:= ct;
	    ct := LCM([Denominator(c) : c in Coefficients(Q)]) /
		GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;

            //vprintf Hyperelliptic, 2 :
            //    "Factorization of conic discriminant before reduction: %o\n",
            //    Factorization(Integers() ! Discriminant(Conic(ProjectiveSpace(Parent(C)), C)));

            vprintf Hyperelliptic, 2 : "Minimal model step...\n";
	    Cphi, phi := MinimalModel(Conic(ProjectiveSpace(Parent(C)), C));
	    C := DefiningPolynomial(Cphi);
	    Q := Evaluate(Q, DefiningPolynomials(phi));
	    ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
		  GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;
	    vprintf Hyperelliptic, 2 :  "Conic %o\n", C;
	    vprintf Hyperelliptic, 2 :  "Quartic %o\n", Q;

	else
	    R := FF!0;
            vprintf Hyperelliptic, 2 :  "None parametric conic works ! Let us do it as usual...\n\n", R;
	end if;
    end if;

    /* Considering conics in turn */
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic123(JI : models := models); end if;

    if R eq 0 then R, C, Q := Genus3ConicAndQuartic124(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic157(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic136(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic148(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic129(JI : models := models); end if;

    if R eq 0 then R, C, Q := Genus3ConicAndQuartic125(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic126(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic128(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic146(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic137(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic247(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1210(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1310(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1211(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1411(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1312(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1313(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1612(JI : models := models); end if;

    /* No non-degenrate conic found, return immediatly */
    if R eq 0 then return false; end if;

    /* Computing conic and quartic */
    if models then

        phi := ConicParametrization(C :
            RationalPoint := RationalModel, RandomLine := not Deterministic);

        f := Evaluate(Q, DefiningPolynomials(phi));

        f := UnivariatePolynomial(Evaluate(f, Parent(f).2, 1));

        if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
            f := MinRedBinaryForm(f : degree := 8);
        end if;

        vprintf Hyperelliptic, 1 :  "Hyperelliptic polynomial: %o\n", f;
	return f;

    end if;

    return true;

end function;

function Genus3ConicAndQuarticForC4(JI : models := true, minimize := true)

    FF := Universe(JI);
    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    /* Considering conics in turn */
    R, C, Q := Genus3ConicAndQuartic123(JI : models := models);
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic157(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic129(JI : models := models); end if;

    if R eq 0 then
	R, C, Q := Genus3ConicAndQuartic136(JI : models := models);
	if R ne 0 then
	    PC := Parent(C);  x1 := PC.1; x2 := PC.2; x3 := PC.3;
	    C := Evaluate(C, [x1, x3, x2]); Q := Evaluate(Q, [x1, x3, x2]);
	end if;
    end if;

    /* Usefull for instance for [ 1, 0, 1, 0, 3, 0, 43, 0, 18 ] in GF(47^2) */
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic124(JI : models := models); end if;

    /* No non-degenrate conic found, return immediatly (should not happen) */
    if R eq 0 then
	vprintf Hyperelliptic, 1 : "ARGH, no non-degenerate conic found in a C4 case (this should not happen) \n";
	return false;
    end if;

    /* Computing conic and quartic */
    if models then

	PC := Parent(C);  x1 := PC.1; x2 := PC.2; x3 := PC.3;

	/* If no sparse conic or quartic found,
           return immediatly (this should not happen) */
	Cc, Cm := CoefficientsAndMonomials(C);
	if (Seqset(Cm) meet {x1^2, x2^2, x3^2, x1*x3}) ne Seqset(Cm) then
	    vprintf Hyperelliptic, 1 : "ARGH, no sparse conic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	Qc, Qm := CoefficientsAndMonomials(Q);
	if (Seqset(Qm) meet {x2*x1^3, x2*x3^3, x2^3*x1, x2*x1^2*x3, x2^3*x3, x2*x1*x3^2}) ne Seqset(Qm) then
	    vprintf Hyperelliptic, 1 : "ARGH, no sparse quartic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	if Index(Cm, x1^2) eq 0 then c11 := FF!0; else	c11 := Cc[Index(Cm, x1^2)]; end if;
	if Index(Cm, x2^2) eq 0 then c22 := FF!0; else c22 := Cc[Index(Cm, x2^2)];  end if; //c2 = 0 is excluded
	if Index(Cm, x3^2) eq 0 then c33 := FF!0; else c33 := Cc[Index(Cm, x3^2)];  end if;
	if Index(Cm, x1*x3) eq 0 then c13 := FF!0; else c13 := Cc[Index(Cm, x1*x3)]; end if;
	/* "c11 := ", c11, ";"; "c13 := ", c13, ";"; "c22 := ", c22, ";"; "c33 := ", c33, ";"; ""; */

	if c11 eq 0 then
	    /* "HUM, c11 = 0..."; */
	    xi := -c33/c13; eta := 0;
	    QF := FF;
	else
	    PCx := PolynomialRing(FF); X := PCx.1;
	    QF := quo<PCx | X^2+(c11*c33-1/4*c13^2)/c11/c22>; a := QF.1;
	    xi := -1/2*c13/c11; eta := a;
	end if;
	/* "pt is "; [xi, eta, 1]; */
	/* "Conic evaluated at this point is", Evaluate(C, [xi, eta, 1]); */

	P3 := PolynomialRing(QF, 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

	pol := Evaluate(C,[xi + x2*x1, eta + x1,1]);
	/* ""; "pol is", pol; */

	A := Coefficient(pol,x1,2);
	B := Coefficient(pol,x1,1);
	/* "param is", [xi*A-x2*B,A*eta-B,A]; */
	f := UnivariatePolynomial(Evaluate(Q,[xi*A-x2*B,A*eta-B,A]));

        if c11 eq 0 then
            if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
                f := MinRedBinaryForm(f : degree := 8);
            end if;
            return f;
        end if;

	F := [Eltseq(c) : c in Eltseq(Evaluate(f, a*Parent(f).1))];
	if Seqset([F[1+i, 1] : i in [0..Degree(f)] | #F[1+i] ne 0]) ne {0} then
	    vprintf Hyperelliptic, 1 : "ARGH, no rational model found in a C4 case (this should not happen)\n";
	end if;

	FFx := PolynomialRing(FF); x := FFx.1;
	fr :=  &+[(FF!F[1+i, 2])*x^(i) : i in [0..Degree(f)] | #F[1+i] ne 0];

        if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
            fr := MinRedBinaryForm(fr : degree := 8);
        end if;
	return fr;
    end if;

    return true;

end function;
