//freeze;

/***
 *  SL2-invariants of binary octics in characteristic 0 or > 7
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
 *  Copyright 2013, R. Basson & R. Lercier & C. Ritzenthaler & J. Sijsling
 */

import "../toolbox/sl2invtools.m"    : Transvectant, PowerRepresentativesInFiniteFields, ShiodaInvariantsAppend;

function ShiodaInvariantsCharp(f : scaled := true,
    PrimaryOnly := false, degmax := Infinity(), degmin := 1)

    JI := []; Wght := [];

    /* Degree 2 */
    if degmax lt 2 then	return JI, Wght; end if;

    f_cov := [* f, 1, 8 *];

    if degmin le 2 then

        /* J2 = (f,f)_8 : order 2*d-16, degree 2  */
        J2 := Transvectant(f_cov, f_cov, 8 : scaled := scaled);

        Append(~JI, Coefficient(J2[1], 0)); Append(~Wght, 2);
    end if;

    /* Degree 3 */
    if degmax lt 3 then	return JI, Wght; end if;

    /* g = (f,f)_4 : order 2*d-8, degree 2 => (8, 2) */
    g_cov := Transvectant(f_cov, f_cov, 4 : scaled := scaled);

    /* H = (f,f)_2 : order 2*d-4, degree 2 => (12, 2) */
    /* H_cov := Transvectant(f_cov, f_cov, 2 : scaled := scaled); */

    if degmin le 3 then

        /* J3 = (f,g)_8 : order 3*d-24, degree 3  */
        J3 := Transvectant(f_cov, g_cov, 8 : scaled := scaled);

        Append(~JI, Coefficient(J3[1], 0)); Append(~Wght, 3);
    end if;

    /* Degree 4 */
    if degmax lt 4 then	return JI, Wght; end if;

    /* k = (f,f)_6 : order 2*d-12, degree 2 => (4, 2) */
    k_cov := Transvectant(f_cov, f_cov, 6 : scaled := scaled);

    if degmin le 4 then

        /* J4 = (k,k)_4 : order 4*d-32, degree 4  */
        J4 := Transvectant(k_cov, k_cov, 4 : scaled := scaled);

        Append(~JI, Coefficient(J4[1], 0)); Append(~Wght, 4);
    end if;

    /* Degree 5 */
    if degmax lt 5 then	return JI, Wght; end if;

    /* m := (f, k)_4 : order 3*d-20, degree 3 => (4, 3) */
    m_cov := Transvectant(f_cov, k_cov, 4 : scaled := scaled);

    if degmin le 5 then

        /* J5 = (m,k)_4 : order 5*d-40, degree 5  */
        J5 := Transvectant(m_cov, k_cov, 4 : scaled := scaled);

        Append(~JI, Coefficient(J5[1], 0)); Append(~Wght, 5);
    end if;

    /* Degree 6 */
    if degmax lt 6 then	return JI, Wght; end if;

    /* h := (k, k)_2 : order 4*d-28, degree 4 => (4, 4) */
    h_cov := Transvectant(k_cov, k_cov, 2 : scaled := scaled);

    if degmin le 6 then

        /* J6 = (k,h)_4 : order 6*d-48, degree 6  */
        J6 := Transvectant(k_cov, h_cov, 4 : scaled := scaled);

        Append(~JI, Coefficient(J6[1], 0)); Append(~Wght, 6);
    end if;

    /* Degree 7 */
    if degmax lt 7 then	return JI, Wght; end if;

    if degmin le 7 then

        /* J7 = (m,h)_4 : order 7*d-56, degree 7  */
        J7 := Transvectant(m_cov, h_cov, 4 : scaled := scaled);

        Append(~JI, Coefficient(J7[1], 0)); Append(~Wght, 7);
    end if;

    /* Degree 8 */
    if degmax lt 8 then	return JI, Wght; end if;

    if not PrimaryOnly then

        if degmin le 8 then

            /* p := (g, k)_4 : order 4*d-28, degree 4 => (4, 4) */
            p_cov := Transvectant(g_cov, k_cov, 4 : scaled := scaled);

            /* J8 = (p,h)_4 : order 8*d-64, degree 8  */
            J8 := Transvectant(p_cov, h_cov, 4 : scaled := scaled);

            Append(~JI, Coefficient(J8[1], 0)); Append(~Wght, 8);
        end if;

        /* Degree 9 */
        if degmax lt 9 then	return JI, Wght; end if;

        if degmin le 9 then

            /* n := (f, h)_4 : order 5*d-36, degree 5 => (4, 5) */
            n_cov := Transvectant(f_cov, h_cov, 4 : scaled := scaled);

            /* J9 = (n,h)_4 : order 9*d-72, degree 9  */
            J9 := Transvectant(n_cov, h_cov, 4 : scaled := scaled);

            Append(~JI, Coefficient(J9[1], 0)); Append(~Wght, 9);
        end if;

        /* Degree 10 */
        if degmax lt 10 then return JI, Wght; end if;

        if degmin le 10 then

            /* q := (g, h)_4 : order 6*d-44, degree 6 => (4, 6) */
            q_cov := Transvectant(g_cov, h_cov, 4 : scaled := scaled);

            /* J10 = (q,h)_4 : order 10*d-80, degree 10  */
            J10 := Transvectant(q_cov, h_cov, 4 : scaled := scaled);

            Append(~JI, Coefficient(J10[1], 0)); Append(~Wght, 10);
        end if;

    end if;

    return JI, Wght;

end function;

/*
  Coefficients of 5 syzygies R1, R2, R3, R4 and R5 of degrees 16, 17, 18, 19,
  and 20 between J8, J9 nd J10. See [Shioda1967].
*/
function ShiodaSyzygyes(J2, J3, J4, J5, J6, J7)

    A6  := (-2/27*J3^2+64/45*J6-8/45*J2*J4+1/405*J2^3);
    A7  := (1/30*J2*J5-2/5*J7+1/15*J3*J4);
    A8  := (-52/105*J4^2+2/15*J2*J6);
    A16 := 1/90*J3*J4^2*J5+1/36450*J2^4*J4^2-26/42525*J2^3*J4*J6-2/15*J5^2*J6-1/810*J2^2*J4^3-1/1215*J2*J3^2*J4^2+76/2835*J2*J4^2*J6+52/2835*J3^2*J4*J6-12/1225*J4^4+1/5*J4*J5*J7-1/30*J2*J7^2-2/15*J3*J6*J7+352/4725*J4*J6^2;

    B7  := (1/12*J3*J4-1/2*J7+1/24*J2*J5);
    B8  := (-1/12*J3*J5-8/135*J2*J6+1/540*J2^2*J4-1/9720*J2^4+2/105*J4^2+1/324*J2*J3^2);
    B9  := (-1/12*J2*J7-1/6*J3*J6);
    B17 := -1/2430*J2^3*J5*J6-17/315*J4*J6*J7-1/54*J3^2*J4*J7+1/81*J3^2*J5*J6+31/3780*J2*J4*J5*J6+1/972*J3^3*J4^2-1/29160*J2^3*J3*J4^2+1/1620*J2^3*J4*J7-1/2160*J2^2*J4^2*J5+1/180*J2^2*J6*J7+4/135*J5*J6^2+1/648*J2*J3*J4^3-1/140*J2*J4^2*J7+1/1134*J3*J4^2*J6+1/12*J3*J7^2;

    G   := -4/5;
    C8  := (1/180*J2^2*J4-18/35*J4^2+1/12*J3*J5+2/15*J2*J6);
    C9  := (-1/180*J2^2*J5-1/4860*J2^3*J3+2/5*J4*J5-34/135*J3*J6+1/162*J3^3+1/270*J2*J3*J4);
    C10 := (-1/27*J3^2*J4+314/315*J4*J6-1/6*J3*J7-1/10*J2*J4^2+1/810*J2^3*J4-1/90*J2^2*J6);
    C18 := 3/35*J3*J4^2*J7+1/14580*J2^2*J3^2*J4^2+113/17010*J2^2*J4^2*J6-4/15*J5*J6*J7+17/42525*J2*J4*J6^2+1/90*J2*J3*J6*J7-4/32805*J2^3*J3^2*J6+26/3645*J2*J3^2*J4*J6-1/1080*J2*J3*J4^2*J5-1/437400*J2^5*J4^2+41/136080*J2^3*J4^3-11/437400*J2^3*J6^2-13/54675*J2^4*J4*J6-3/350*J2*J4^4+4/2187*J3^4*J6-1/168*J3^2*J4^3+1/180*J2^2*J7^2-8/245*J4^3*J6+40/243*J6^3-3/70*J3*J4*J5*J6+11/14580*J3^2*J6^2+1/492075*J2^6*J6;

    D9 := (-1/576*J2^2*J5-1/288*J2*J3*J4-1/6*J3*J6-1/16*J2*J7);
    D10 := (-3/32*J5^2+1/6480*J2^3*J4+11/210*J4*J6+13/1620*J2^2*J6+1/24*J3*J7+1/233280*J2^5-1/7776*J2^2*J3^2+1/288*J2*J3*J5+1/720*J2*J4^2-1/144*J3^2*J4);
    D11 := (1/18*J3*J4^2+1/144*J2*J3*J6+1/288*J2^2*J7+1/48*J2*J4*J5-1/48*J5*J6-5/16*J4*J7);
    D19 := 1/699840*J2^4*J3*J4^2+7/8640*J2*J5*J6^2-47
    /30240*J2^2*J4^2*J7-1/38880*J2^4*J4*J7+3/280*J4^2*J5*J6+1/81*J3^2*
    J6*J7-5/7776*J2^3*J6*J7-1/15552*J2^2*J3*J4^3-1/288*J2*J3*J7^2-29/
    30240*J2^2*J4*J5*J6+1/1296*J2*J3^2*J4*J7-1/648*J2*J3^2*J5*J6-85/
    27216*J2*J3*J4^2*J6+3/896*J2*J4^3*J5-1/23328*J2*J3^3*J4^2+1/19440*
    J2^4*J5*J6-1/51840*J2^3*J4^2*J5-1/486*J3^3*J4*J6+1/864*J3^2*J4^2*
    J5+83/90720*J3*J4*J6^2+1/72*J3*J5^2*J6+1/14580*J2^3*J3*J4*J6-1/2240
    *J3*J4^4+3/32*J5*J7^2-25/432*J6^2*J7-9/1120*J4^3*J7-67/15120*J2*J4*
    J6*J7-1/48*J3*J4*J5*J7;

    E := 1/30;
    E10 := (-3/32*J5^2-1/288*J2*J3*J5-1/8*J3*J7-19/432*J3^2*J4+1/810*J2^3*J4-11/144*J2*J4^2+661/630*J4*J6-1/90*J2^2*J6);
    E11 := (-1/6480*J2^2*J3*J4+13/810*J2*J3*J6+1/116640*J2^4*J3+1/4320*J2^3*J5+1/360*J2^2*J7+2/45*J3*J4^2-1/3888*J2*J3^3-1/4*J4*J7-1/60*J5*J6);
    E12 := (17/216*J2*J4*J6+1/24*J3*J4*J5+1/144*J2*J3*J7-27/80*J4^3-25/216*J6^2+25/648*J3^2*J6+1/270*J2^2*J4^2-1/1215*J2^3*J6+3/16*J5*J7);
    E20 := -1/19440*J2^3*J3*J4*J7+1/9720*J2^3*J3*J5*J6-1/7290*J2^2*J3^2*J4*J6+1/25920*J2^2*J3*J4^2*J5-1/2160*J2^2*J3*J6*J7-1/720*J2^2*J4*J5*J7-47/15120*J2*J3*J4^2*J7-1/720*
J2*J5*J6*J7-331/3780*J3*J4*J6*J7+1/218700*J2^5*J4*J6+1/116640*J2^4*J4^3-377/907200*J2^2*J4^4-1/11664*J3^4*J4^2-1/144*J3^2*J7^2+19849/396900*J4^2*J6^2+1/349920*
J2^3*J3^2*J4^2-83/127575*J2^3*J4^2*J6+83/1360800*J2^2*J4*J6^2+1/1080*J2^2*J5^2*J6-9/1400*J4^5-1/2592*J2*J3^2*J4^3+449/22680*J2*J4^3*J6+1/960*J2*J4^2*J5^2-1/48*J2*J4*J7^2+1/
648*J3^3*J4*J7-1/324*J3^3*J5*J6+43/3240*J3^2*J4^2*J6+3/448*J3*J4^3*J5-29/15120*J2*J3*J4*J5*J6+7/4320*J3*J5*J6^2+9/70*J4^2*J5*J7-143/1680*J4*J5^2*J6;

    return
	A6, A7, A8, A16,
	B7, B8, B9, B17,
	G, C8, C9, C10, C18,
	D9, D10, D11, D19,
	E, E10, E11, E12, E20;

end function;

function ShiodaAlgebraicInvariantsCharp(PrimaryInvariants, ratsolve)

    FF := Universe(PrimaryInvariants);

    P3 := PolynomialRing(FF, 3); J8 := P3.1; J9 := P3.2; J10 := P3.3;

    if ratsolve eq false or not IsFinite(FF) then
	g := 1; LG := [ FF!1 ];
    else
	Support := [i : i in [1..#PrimaryInvariants] | PrimaryInvariants[i] ne 0];
	if #Support eq 0 then
	    g := 1;
	else
	    g := Gcd([i+1 : i in Support]);
	end if;
	if g ne 1 then
	    LG := PowerRepresentativesInFiniteFields(FF, g);
	else
	    LG := [ FF!1 ];
	end if;
    end if;

    JIs := [];
    for L in LG do

	J2, J3, J4, J5, J6, J7 := Explode([L^((i+1) div g)*PrimaryInvariants[i] : i in [1..#PrimaryInvariants]]);

	A6, A7, A8, A16,
	    B7, B8, B9, B17,
	    G, C8, C9, C10, C18,
	    D9, D10, D11, D19,
	    E, E10, E11, E12, E20 := ShiodaSyzygyes(J2, J3, J4, J5, J6, J7);

	RES := [J8^5 +

	    (A8 + 2*B8 + C8) * J8^4 +

	    (-A6*C10 - A7*B9 + 2*A8*B8 + A8*C8 + A16 +
	    B7*B9*G + B7*G*D9 - B7*C9 + B8^2 + 2*B8*C8) * J8^3 +

	    (-A6*B7*G*D11 - 2*A6*B8*C10 - A6*B9^2*G + A6*B9*C9 - A6*C18 +
	    A7*B7*C10 - A7*B8*B9 - A7*B9*C8 - A7*B17 + A8*B7*B9*G +
	    A8*B7*G*D9 - A8*B7*C9 + A8*B8^2 + 2*A8*B8*C8 + 2*A16*B8 + A16*C8 -
	    B7^2*G*D10 + B7*B8*G*D9 - B7*B8*C9 + B7*B17*G +
	    B8^2*C8) * J8^2 +

	    (-A6*B7*B8*G*D11 + A6*B7*B9*G*D10 -
	    A6*B7*G*D19 - A6*B8^2*C10 + A6*B8*B9*C9 - 2*A6*B8*C18 -
	    2*A6*B9*B17*G + A6*B17*C9 + A7*B7^2*G*D11 + A7*B7*B8*C10 -
	    A7*B7*B9*G*D9 + A7*B7*C18 - A7*B8*B9*C8 - A7*B8*B17 - A7*B17*C8 -
	    A8*B7^2*G*D10 + A8*B7*B8*G*D9 - A8*B7*B8*C9 + A8*B7*B17*G +
	    A8*B8^2*C8 + A16*B7*B9*G + A16*B7*G*D9 - A16*B7*C9 + A16*B8^2 +
	    2*A16*B8*C8) * J8 +

	    (- A6*B7*B8*G*D19 + A6*B7*B17*G*D10 - A6*B8^2*C18
	    + A6*B8*B17*C9 - A6*B17^2*G + A7*B7^2*G*D19 + A7*B7*B8*C18 -
	    A7*B7*B17*G*D9 - A7*B8*B17*C8 - A16*B7^2*G*D10 +
	    A16*B7*B8*G*D9 - A16*B7*B8*C9 + A16*B7*B17*G + A16*B8^2*C8)];


	R1 := J8^2                 +  A6*J10 +  A7*J9 +  A8*J8 + A16;
	R2 := J8*J9               +  B7*J10 +  B8*J9 +  B9*J8 + B17;
	R3 := J8*J10 + G*J9^2    +  C8*J10 +  C9*J9 + C10*J8 + C18;
	R4 := J9*J10             +  D9*J10 + D10*J9 + D11*J8 + D19;
	R5:=  J10^2  + E*J2*J9^2 + E10*J10 + E11*J9 + E12*J8 + E20;

	RES cat:= [R1, R2, R3, R4, R5];

	if ratsolve eq false then return RES; end if;

	P2 := PolynomialRing(FF, 2); _J9 := P2.1; _J10 := P2.2;

	R8 := Roots(UnivariatePolynomial(RES[1]));
	for r8 in R8 do
	    j8 := r8[1];
	    dt  := A6*j8+A6*B8-B7*A7;
	    if dt ne 0 then
		j9  := (B7*j8^2-A6*B9*j8-A6*B17+B7*A8*j8+B7*A16)/dt;
		j10 := -(j8^3+j8^2*B8-A7*B9*j8-A7*B17+A8*j8^2+A8*j8*B8+A16*j8+A16*B8)/dt;
		NJI := [ J2, J3, J4, J5, J6, J7 ] cat [FF!j8, FF!j9, FF!j10 ];
		if g ne 1 then NJI := WPSNormalize([2..10], NJI); end if;
		JIs := ShiodaInvariantsAppend(JIs, NJI);
	    else

		R1 := j8^2                 +  A6*_J10 +  A7*_J9 +  A8*j8 + A16;
		R2 := j8*_J9               +  B7*_J10 +  B8*_J9 +  B9*j8 + B17;
		R3 := j8*_J10 + G*_J9^2    +  C8*_J10 +  C9*_J9 + C10*j8 + C18;
		R4 := _J9*_J10             +  D9*_J10 + D10*_J9 + D11*j8 + D19;
		R5:=  _J10^2  + E*J2*_J9^2 + E10*_J10 + E11*_J9 + E12*j8 + E20;

		SYS := [R1, R2, R3, R4, R5];
		V := Variety(ideal<P2 | SYS>);
		for v in V do
		    NJI := [ J2, J3, J4, J5, J6, J7 ] cat [ FF!j8, FF!v[1], FF!v[2] ];
		    if g ne 1 then NJI := WPSNormalize([2..10], NJI); end if;
		    JIs := ShiodaInvariantsAppend(JIs, NJI);
		end for;
	    end if;

	end for;
    end for;

    return JIs;

end function;
