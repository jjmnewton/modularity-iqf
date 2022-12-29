//freeze;

/***
 *  SL2-invariants of binary octics in characteristic 3
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

import "../toolbox/sl2invtools.m"    : PowerRepresentativesInFiniteFields, ShiodaInvariantsAppend;
import "g3twists_charp.m" : ShiodaInvariantsCharp;

function ShiodaInvariantsChar3(f :
    PrimaryOnly := false, degmax := Infinity(), degmin := 1)

    JI := []; Wght := [];

    /* Degree 2 */
    if degmax lt 2 then	return JI, Wght; end if;

    if Characteristic(CoefficientRing(f)) ne 3 then

        J2s, J3s, J4s, J5s, J6s, J7s, J8s, J9s, J10s :=
            Explode(ShiodaInvariantsCharp(f : scaled := false));

        /* Removing the content of these invariants */
        j2  := (1/288)                 * J2s;	/* [ <2, 5>,  <3, 2> ]          */
        j3  := (1/103680)              * J3s;	/* [ <2, 8>,  <3, 4>, <5, 1> ]  */
        j4  := (1/2073600)             * J4s;	/* [ <2, 10>, <3, 4>, <5, 2> ]  */
        j5  := (1/298598400)           * J5s;	/* [ <2, 14>, <3, 6>, <5, 2> ] */
        j6  := (1/17915904000)         * J6s;	/* [ <2, 16>, <3, 7>, <5, 3> ] */
        j7  := (1/2579890176000)       * J7s;	/* [ <2, 20>, <3, 9>, <5, 3> ] */
        j8  := (1/154793410560000)     * J8s;	/* [ <2, 22>, <3, 10>, <5, 4> ] */
        j9  := (1/22290251120640000)   * J9s;	/* [ <2, 26>, <3, 12>, <5, 4> ] */
        j10 := (1/1337415067238400000) * J10s;	/* [ <2, 28>, <3, 13>, <5, 5> ] */

        // J2
        if degmin le 2 then
            Kx := j2;
            Append(~JI, Kx); Append(~Wght, 2);
        end if;
        if degmax le 2 then return JI, Wght; end if;

        // J3
        if not PrimaryOnly and degmin le 3 then
            Kx := j3;
            Append(~JI, Kx); Append(~Wght, 3);
        end if;
        if degmax le 3 then return JI, Wght; end if;

        // J4
        if degmin le 4 then
            Kx := /* (1 / 2^10 / 7^4) * */ (j4 - 4*j2^2)/3;
            Append(~JI, Kx); Append(~Wght, 4);
        end if;
        if degmax le 4 then return JI, Wght; end if;

        // J5
        if degmin le 5 then
            Kx := /* (1 / 2^9 / 7^5 / 5) * */ (j5 - 2*j2*j3);
            Append(~JI, Kx); Append(~Wght, 5);
        end if;
        if degmax le 5 then return JI, Wght; end if;

        // J6
        if not PrimaryOnly and degmin le 6 then
            Kx := /* (1 / 2^14 / 7^6) * */ (j6 - 6*j4*j2 - 837*j3^2 - 130*j2^3)/3^4;
            Append(~JI, Kx); Append(~Wght, 6);
        end if;
        if degmax le 6 then return JI, Wght; end if;

        // J7
        if degmin le 7 then
            Kx := /* (1 / 2^15 / 5 / 7^7) * */ (j7 - 7*j2*j5)/3;
            Append(~JI, Kx); Append(~Wght, 7);
        end if;
        if degmax le 7 then return JI, Wght; end if;

        // J8
        if not PrimaryOnly and degmin le 8 then
            Kx := /* (1 / 2^17 / 5^2 / 7^9) */ 2 * (81*j8 - 4*j6*j2 - 2430*j5*j3
                - 381*j4*j2^2 - 216*j3^2*j2 + 763*j2^4)/3^6;
            Append(~JI, Kx); Append(~Wght, 8);
        end if;
        if degmax le 8 then return JI, Wght; end if;

        // J9
        if degmin le 9 then
            Kx := /* (1 / 2^19 / 5 / 7^9) / 8 * */ 2 * (2012*j2^3*j3+1152*j2^2*j5
            -276*j2*j3*j4+4671*j3^3-576*j2*j7-8*j3*j6+72*j9)/3^6;
            Append(~JI, Kx); Append(~Wght, 9);
        end if;
        if degmax le 9 then return JI, Wght; end if;

        // J10
        if not PrimaryOnly and degmin le 10 then
            Kx := /* (1 / 2^22 / 5^2 / 7^11) / 4 * */ (3446*j2^5+5400*j2^3*j4+3537*j2^2*j3^2+
            52*j2^2*j6+243*j2*j3*j5+144*j2*j4^2+5265*j3^2*j4+5913*j2*j8+5589*j3*j7+6537*j4*j6+
                324*j10)/3^7;
            Append(~JI, Kx); Append(~Wght, 10);
        end if;
        if degmax le 10 then return JI, Wght; end if;

        // J12
        if degmin le 12 then
            Kx := /* ( -1 / 2^22 / 5^2 / 7^11 ) / 2^6 / 7^2 */ 2 * (13699*j2^6+21069*j2^4*j4
            +40068*j2^3*j3^2+25825*j2^3*j6+24057*j2^2*j3*j5+17568*j2^2*j4^2+17010*j2*j3^2*j4
                +37908*j3^4+54432*j2^2*j8+25515*j2*j3*j7+477*j2*j4*j6+28431*j2*j5^2+32751*j3^2*j6
                +7290*j3*j4*j5+53460*j10*j2+486*j4*j8+17496*j5*j7+52663*j6^2)/3^9;
            Append(~JI, Kx); Append(~Wght, 12);
        end if;

        return JI, Wght;

    end if;

    a0:= Coefficient(f, 0); a1:= Coefficient(f, 1);
    a2:= Coefficient(f, 2); a3:= Coefficient(f, 3);
    a4:= Coefficient(f, 4); a5:= Coefficient(f, 5);
    a6:= Coefficient(f, 6); a7:= Coefficient(f, 7);
    a8:= Coefficient(f, 8);


    i1:= a4;
    i2:= a0*a8;
    j2:= a1*a7;
    k2:= a2*a6;
    l2:= a3*a5;
    i3:= a0*a5*a7 + a1*a3*a8;
    j3:= a0*a6^2  + a2^2*a8;
    k3:= a1*a5*a6 + a2*a3*a7;
    l3:= a2*a5^2  + a3^2*a6;
    i4:= a0*a6*a5^2  + a8*a2*a3^2;
    j4:= a0*a7*a6*a3 + a8*a1*a2*a5;
    k4:= a0*a7^2*a2  + a8*a1^2*a6;
    l4:= a1*a5^3     + a7*a3^3;
    m4:= a1*a6^2*a3  + a7*a2^2*a5;
    i5:= a0^2*a7^2*a6 + a8^2*a1^2*a2;
    j5:= a0*a5^4      + a8*a3^4;
    k5:= a0*a7^2*a3^2 + a8*a1^2*a5^2;
    l5:= a1^2*a6^3    + a7^2*a2^3;
    i6:= a0^2*a7^3*a3 + a8^2*a1^3*a5;
    i7:= a0^3*a7^4 + a8^3*a1^4;

    /* Degree 2 */
    if degmin le 2 then
        J2:= 2*i1^2 + i2 + j2 + k2 + l2;
        Append(~JI, J2); Append(~Wght, 2);
    end if;
    if degmax le 2 then	return JI, Wght; end if;

    /* Degree 3 */
    if not PrimaryOnly and degmin le 3 then
        J3:= 2*i1*i2 + i1*k2 + i3 + 2*k3;
        Append(~JI, J3); Append(~Wght, 3);
    end if;
    if degmax le 3 then	return JI, Wght; end if;

    /* Degree 4 */
    if degmin le 4 then
        J4:= i1^4 + 2*i1^2*i2 + i1^2*j2 + j2^2 + 2*i1^2*k2 + i2*k2 + i1^2*l2 + j2*l2 +
            l2^2 + 2*i1*i3 + 2*i1*k3 + 2*i4 + 2*k4;
        Append(~JI, J4); Append(~Wght, 4);
    end if;
    if degmax le 4 then	return JI, Wght; end if;

    /* Degree 5 */
    if degmin le 5 then
        J5:= i1^5 + 2*i1^3*i2 + i1^3*j2 + i1*j2^2 + i1*i2*k2 + 2*i1*j2*k2 + 2*i1*k2^2 +
            2*i1^3*l2 + 2*i1*i2*l2 + i1*k2*l2 + 2*i1^2*i3 + 2*k2*i3 + l2*i3 + i1^2*j3 +
            2*k2*j3 + 2*l2*j3 + i1^2*k3 + j2*k3 + k2*k3 + 2*l2*k3 + 2*i2*l3 + 2*j2*l3 +
            k2*l3 + l2*l3 + i1*j4 + 2*i1*k4 + i1*l4 + 2*i1*m4 + j5 + k5 + l5;
        Append(~JI, J5); Append(~Wght, 5);
    end if;
    if degmax le 5 then	return JI, Wght; end if;

    /* Degree 6 */
    if not PrimaryOnly and degmin le 6 then
        J6:= 2*i1^6 + 2*i1^4*i2 + i1^2*i2*j2 + j2^3 + i1^4*k2 + i1^2*i2*k2 +
            2*i1^2*j2*k2 + 2*i1^2*k2^2 + 2*k2^3 + i2^2*l2 + 2*k2^2*l2 + l2^3 + i1^3*i3 +
            i1*i2*i3 + 2*i1*j2*i3 + i1*k2*i3 + 2*i3^2 + i1^3*j3 + i1*i2*j3 + i1*j2*j3 +
            2*i1*k2*j3 + 2*i3*j3 + 2*i1^3*k3 + i1*j2*k3 + i1*k2*k3 + j3*k3 + 2*i1*i2*l3 +
            2*i1*j2*l3 + i1*k2*l3 + i3*l3 + 2*i2*i4 + j2*i4 + k2*i4 + i1^2*j4 + 2*j2*j4 +
            l2*k4 + 2*j2*l4 + 2*k2*l4 + 2*i1^2*m4 + 2*j2*m4 + 2*l2*m4 + i1*i5 + i1*k5 +
            i1*l5 + 2*i6;
        Append(~JI, J6); Append(~Wght, 6);
    end if;
    if degmax le 6 then	return JI, Wght; end if;

    /* Degree 7 */
    if degmin le 7 then
        J7:= i1^7 + i1^5*i2 + i1^3*i2^2 + 2*i1^3*i2*j2 + 2*i1*j2^3 + i1^5*k2 +
            i1^3*i2*k2 + 2*i1^3*j2*k2 + i1^3*k2^2 + i1^5*l2 + i1^3*i2*l2 + 2*i1^3*j2*l2 +
            i1^3*k2*l2 + i1^3*l2^2 + 2*i1^4*i3 + j2^2*i3 + j2*k2*i3 + i2^2*j3 + i1^2*k2*j3 +
            2*i2*k2*j3 + 2*j2*k2*j3 + 2*k2^2*j3 + k2*l2*j3 + 2*i1^4*k3 + i2*j2*k3 + j2^2*k3
            + 2*i1*j3*k3 + 2*i2*k2*l3 + k2^2*l3 + i1^2*l2*l3 + i2*l2*l3 + j2*l2*l3 +
            2*k2*l2*l3 + 2*l2^2*l3 + 2*i1*i3*l3 + 2*i1^3*i4 + j3*i4 + i1*k2*j4 + i1*l2*j4 +
            i1^3*k4 + 2*i1*j2*k4 + 2*i3*k4 + 2*k3*k4 + i1^3*l4 + 2*i1*i2*l4 + 2*i1*k2*l4 +
            2*i1*l2*l4 + k3*l4 + 2*i1*k2*m4 + i2*i5 + i1^2*j5 + 2*i2*j5 + 2*j2*j5 + k2*j5 +
            2*l2*j5 + l2*k5 + i2*l5 + j2*l5 + k2*l5 + l2*l5 + i7;
        Append(~JI, J7); Append(~Wght, 7);
    end if;
    if degmax le 7 then	return JI, Wght; end if;

    /* Degree 8 */
    if not PrimaryOnly and degmin le 8 then
        J8:= 2*i1^4*i2^2 + i2^4 + 2*i1^6*j2 + i1^4*i2*j2 + i2^3*j2 + i1^2*i2*j2^2 +
            2*i2^2*j2^2 + i2*j2^3 + j2^4 + i1^6*k2 + 2*i1^4*j2*k2 + i2^2*j2*k2 +
            2*i1^2*j2^2*k2 + i2*j2^2*k2 + j2^3*k2 + 2*i2^2*k2^2 + i1^2*j2*k2^2 + i2*j2*k2^2
            + 2*j2^2*k2^2 + i1^2*k2^3 + j2*k2^3 + k2^4 + 2*i1^4*i2*l2 + 2*i1^2*i2^2*l2 +
            2*i1^2*i2*j2*l2 + 2*i2^2*j2*l2 + 2*i2*j2^2*l2 + i1^4*k2*l2 + i2^2*k2*l2 +
            2*i1^2*j2*k2*l2 + 2*i2*j2*k2*l2 + 2*j2^2*k2*l2 + 2*i1^2*k2^2*l2 + i2*k2^2*l2 +
            2*j2*k2^2*l2 + 2*i2^2*l2^2 + 2*i2*j2*l2^2 + 2*j2^2*l2^2 + 2*j2*k2*l2^2 +
            2*k2^2*l2^2 + 2*i1^2*l2^3 + 2*i2*l2^3 + j2*l2^3 + 2*k2*l2^3 + l2^4 + 2*i1^5*i3 +
            2*i1^3*j2*i3 + i1*i2*j2*i3 + 2*i1*j2^2*i3 + 2*i1^3*k2*i3 + 2*i1*i2*k2*i3 +
            i1*j2*k2*i3 + i1*k2^2*i3 + i1^3*l2*i3 + i1*j2*l2*i3 + i1*k2*l2*i3 + i1^2*i3^2 +
            2*i2*i3^2 + 2*j2*i3^2 + k2*i3^2 + l2*i3^2 + i1^3*i2*j3 + 2*i1^3*k2*j3 +
            2*i1*i2*k2*j3 + i1*k2^2*j3 + 2*i1*i2*l2*j3 + i1*j2*l2*j3 + i1*k2*l2*j3 +
            2*i1^2*i3*j3 + k2*i3*j3 + l2*i3*j3 + 2*i2*j3^2 + i1^5*k3 + i1^3*i2*k3 +
            2*i1*i2^2*k3 + i1^3*j2*k3 + i1*i2*j2*k3 + i1*j2^2*k3 + 2*i1^3*k2*k3 +
            2*i1*j2*k2*k3 + i1*k2^2*k3 + 2*i1^3*l2*k3 + i1*i2*l2*k3 + i1*j2*l2*k3 +
            i1^2*j3*k3 + 2*j2*j3*k3 + 2*k2*j3*k3 + 2*l2*j3*k3 + i1^2*k3^2 + l2*k3^2 +
            2*i1*i2^2*l3 + i1*i2*j2*l3 + 2*i1*i2*k2*l3 + 2*i1*k2^2*l3 + i1^3*l2*l3 +
            i1*i2*l2*l3 + 2*i1*k2*l2*l3 + i2*i3*l3 + j2*i3*l3 + 2*k2*i3*l3 + 2*l2*i3*l3 +
            i2*l3^2 + 2*i1^2*i2*i4 + i2^2*i4 + i2*j2*i4 + j2^2*i4 + 2*i1^2*k2*i4 + i2*k2*i4
            + 2*j2*k2*i4 + k2^2*i4 + 2*i2*l2*i4 + 2*j2*l2*i4 + 2*k2*l2*i4 + 2*l2^2*i4 +
            i1*i3*i4 + i1*k3*i4 + i1^2*i2*j4 + 2*i2*j2*j4 + 2*i1^2*k2*j4 + j2*k2*j4 +
            i1^2*i2*k4 + i2^2*k4 + 2*i2*j2*k4 + 2*j2*k2*k4 + k2^2*k4 + i2*l2*k4 + 2*j2*l2*k4
            + 2*k2*l2*k4 + l2^2*k4 + 2*i1*i3*k4 + 2*k4^2 + i1^4*l4 + i1^2*i2*l4 + 2*i2*j2*l4
            + 2*i1^2*k2*l4 + 2*i2*k2*l4 + 2*j2*k2*l4 + k2^2*l4 + k2*l2*l4 + i1*k3*l4 +
            2*l4^2 + 2*i1^2*i2*m4 + i1^2*k2*m4 + 2*j2*k2*m4 + 2*i2*l2*m4 + 2*j2*l2*m4 +
            k2*l2*m4 + l2^2*m4 + i1*i3*m4 + 2*i1*l2*i5 + i3*i5 + j3*i5 + i1^3*j5 + i1*i2*j5
            + 2*i1*j2*j5 + 2*i1*k2*j5 + 2*i3*j5 + 2*j3*j5 + k3*j5 + l3*j5 + i1*i2*k5 +
            2*i1*l2*k5 + k3*k5 + i1*i2*l5 + i1*j2*l5 + 2*i1*k2*l5 + 2*i1*l2*l5 + 2*k3*l5 +
            i2*i6 + 2*l2*i6 + i1*i7;
        Append(~JI, J8); Append(~Wght, 8);
    end if;
    if degmax le 8 then	return JI, Wght; end if;

    /* Degree 9 */
    if degmin le 9 then
        J9:= i1^9 + 2*i1^7*i2 + i1^5*i2^2 + 2*i1*i2^4 + 2*i1*i2^2*j2^2 + 2*i1^3*j2^3 +
            i1*i2*j2^3 + 2*i1^7*k2 + i1^5*i2*k2 + 2*i1^5*j2*k2 + i1^3*i2*j2*k2 +
            2*i1*i2^2*j2*k2 + 2*i1^3*j2^2*k2 + 2*i1^5*k2^2 + i1*i2^2*k2^2 + i1^3*j2*k2^2 +
            2*i1*j2^2*k2^2 + i1^3*k2^3 + i1^5*j2*l2 + i1^3*j2^2*l2 + i1*i2*j2^2*l2 +
            i1*j2^3*l2 + i1*i2^2*k2*l2 + 2*i1^3*k2^2*l2 + i1*i2*k2^2*l2 + 2*i1*j2*k2^2*l2 +
            i1*k2^3*l2 + i1^3*i2*l2^2 + 2*i1*i2^2*l2^2 + 2*i1^3*j2*l2^2 + 2*i1*j2^2*l2^2 +
            i1^3*k2*l2^2 + i1*i2*k2*l2^2 + 2*i1*j2*k2*l2^2 + 2*i1*i2*l2^3 + i1*k2*l2^3 +
            i1^6*i3 + i1^4*i2*i3 + i2^3*i3 + 2*i1^4*j2*i3 + 2*i1^2*j2^2*i3 + i2*j2^2*i3 +
            j2^3*i3 + i1^2*i2*k2*i3 + i2^2*k2*i3 + 2*i2*j2*k2*i3 + j2^2*k2*i3 +
            2*i1^2*k2^2*i3 + j2*k2^2*i3 + 2*i1^4*l2*i3 + i1^2*i2*l2*i3 + i1^2*j2*l2*i3 +
            2*i2*k2*l2*i3 + 2*j2*k2*l2*i3 + k2^2*l2*i3 + i2*l2^2*i3 + j2*l2^2*i3 + l2^3*i3 +
            2*i1^3*i3^2 + 2*i1*k2*i3^2 + i1*l2*i3^2 + i3^3 + 2*i1^4*i2*j3 + 2*i1^2*i2^2*j3 +
            2*i2^3*j3 + i1^4*j2*j3 + 2*i1^2*i2*j2*j3 + 2*i2^2*j2*j3 + 2*i1^2*j2^2*j3 +
            2*i2^2*k2*j3 + i1^2*j2*k2*j3 + 2*j2^2*k2*j3 + 2*i2*k2^2*j3 + 2*i1^2*i2*l2*j3 +
            i2^2*l2*j3 + 2*i2*k2*l2*j3 + 2*k2^2*l2*j3 + 2*i2*l2^2*j3 + 2*l2^3*j3 +
            2*i1*k2*i3*j3 + 2*i1^3*j3^2 + 2*i1*i2*j3^2 + i1*j2*j3^2 + i1*k2*j3^2 + i3*j3^2 +
            2*j3^3 + i1^6*k3 + i1^4*i2*k3 + 2*i2^3*k3 + i1^2*i2*j2*k3 + i2*j2^2*k3 +
            2*j2^3*k3 + i1^4*k2*k3 + 2*i1^2*i2*k2*k3 + 2*i2^2*k2*k3 + j2^2*k2*k3 +
            i1^2*k2^2*k3 + j2*k2^2*k3 + 2*i1^4*l2*k3 + i1^2*j2*l2*k3 + i2*j2*l2*k3 +
            j2^2*l2*k3 + 2*i2*k2*l2*k3 + j2*k2*l2*k3 + 2*k2^2*l2*k3 + 2*i2*l2^2*k3 +
            j2*l2^2*k3 + 2*l2^3*k3 + 2*i1*k2*j3*k3 + 2*j3^2*k3 + i1^3*k3^2 + i1*i2*k3^2 +
            2*i1*j2*k3^2 + 2*i1*l2*k3^2 + j3*k3^2 + 2*i2^3*l3 + i1^2*j2^2*l3 + i2*j2^2*l3 +
            2*j2^3*l3 + 2*i1^2*i2*k2*l3 + i2^2*k2*l3 + i1^2*k2^2*l3 + i2*k2^2*l3 +
            2*j2*k2^2*l3 + 2*k2^3*l3 + 2*i2^2*l2*l3 + i2*j2*l2*l3 + j2^2*l2*l3 +
            i1^2*k2*l2*l3 + 2*i2*k2*l2*l3 + k2^2*l2*l3 + i2*l2^2*l3 + j2*l2^2*l3 +
            k2*l2^2*l3 + i1*i2*i3*l3 + i1*j2*i3*l3 + 2*i1*k2*i3*l3 + 2*i1*l2*i3*l3 +
            2*i1*i2*j3*l3 + i1*j2*j3*l3 + i1*k2*j3*l3 + 2*i1*i2*l3^2 + i1*j2*l3^2 +
            i1*k2*l3^2 + i3*l3^2 + l3^3 + i1^5*i4 + i1^3*i2*i4 + i1*j2^2*i4 + 2*i1^3*k2*i4 +
            2*i1^3*l2*i4 + 2*i1*i2*l2*i4 + i1*k2*l2*i4 + 2*i1^2*i3*i4 + k2*i3*i4 + l2*i3*i4
            + 2*k2*j3*i4 + 2*i1^2*k3*i4 + 2*j2*k3*i4 + 2*l2*k3*i4 + i1*i2^2*j4 +
            2*i1*i2*j2*j4 + i1^3*k2*j4 + 2*i1*k2^2*j4 + 2*i1*i2*l2*j4 + i1*j2*l2*j4 +
            2*i1*l2^2*j4 + i1^2*j3*j4 + 2*j2*j3*j4 + l2*j3*j4 + i1^5*k4 + i1*i2^2*k4 +
            i1^3*j2*k4 + i1*i2*j2*k4 + i1*j2^2*k4 + 2*i1^3*k2*k4 + i1*i2*k2*k4 + i1*j2*k2*k4
            + i1^3*l2*k4 + 2*i1*i2*l2*k4 + 2*i1*l2^2*k4 + i1^2*i3*k4 + 2*i2*i3*k4 +
            2*j2*i3*k4 + 2*i1^2*k3*k4 + 2*j2*k3*k4 + 2*k2*k3*k4 + 2*l2*k3*k4 + i1*k4^2 +
            i1*i2^2*l4 + i1*i2*j2*l4 + 2*i1*j2^2*l4 + i1^3*k2*l4 + 2*i1*i2*k2*l4 +
            2*i1*j2*k2*l4 + 2*i1*k2^2*l4 + i1*j2*l2*l4 + 2*i1^2*j3*l4 + 2*k2*j3*l4 +
            2*i1^2*k3*l4 + 2*i2*k3*l4 + j2*k3*l4 + k2*k3*l4 + l2*k3*l4 + j2*l3*l4 +
            2*k2*l3*l4 + 2*i1*i2^2*m4 + 2*i1^3*j2*m4 + i1*j2^2*m4 + 2*i1^3*k2*m4 +
            2*i1*j2*k2*m4 + i1*k2^2*m4 + i1*j2*l2*m4 + i1*k2*l2*m4 + 2*i1*l2^2*m4 +
            i1^2*i3*m4 + i2*i3*m4 + j2*i3*m4 + 2*k2*i3*m4 + l2*i3*m4 + 2*i1^2*j3*m4 +
            2*j2*j3*m4 + 2*l2*j3*m4 + i1^2*l3*m4 + i2*l3*m4 + j2*l3*m4 + 2*l2*l3*m4 +
            2*i1^4*i5 + i1^2*i2*i5 + 2*i2^2*i5 + i1^2*j2*i5 + 2*i2*j2*i5 + 2*i1^2*k2*i5 +
            2*i2*k2*i5 + k2^2*i5 + 2*i1^2*l2*i5 + 2*i2*l2*i5 + j2*l2*i5 + k2*l2*i5 +
            2*l2^2*i5 + i1*j3*i5 + i2^2*j5 + 2*i2*j2*j5 + j2^2*j5 + i1^2*k2*j5 + k2^2*j5 +
            2*k2*l2*j5 + i2^2*k5 + 2*i1^2*j2*k5 + j2^2*k5 + 2*i1^2*k2*k5 + i2*k2*k5 +
            2*k2^2*k5 + 2*i2*l2*k5 + k2*l2*k5 + 2*l2^2*k5 + i1*k3*k5 + 2*i1*l3*k5 + 2*l4*k5
            + i1^4*l5 + 2*i1^2*i2*l5 + j2^2*l5 + 2*i1^2*k2*l5 + 2*i2*k2*l5 + i1^2*l2*l5 +
            2*i2*l2*l5 + j2*l2*l5 + 2*k2*l2*l5 + l2^2*l5 + i1*i3*l5 + i1*j3*l5 + i1*k3*l5 +
            2*i1*l3*l5 + 2*k4*l5 + 2*m4*l5 + i1^3*i6 + 2*i1*i2*i6 + 2*i1*j2*i6 + 2*i1*l2*i6
            + k3*i6 + 2*i2*i7 + 2*j2*i7 + 2*k2*i7;
        Append(~JI, J9); Append(~Wght, 9);
    end if;
    if degmax le 9 then	return JI, Wght; end if;

    /* Degree 10 */
    if not PrimaryOnly and degmin le 10 then
        J10:= i1^8*i2 + 2*i1^6*i2^2 + 2*i1^2*i2^4 + i2^5 + i1^8*j2 + i1^4*i2^2*j2 +
            i1^2*i2^3*j2 + 2*i2^4*j2 + 2*i1^6*j2^2 + 2*i1^4*i2*j2^2 + i2^3*j2^2 +
            i1^2*i2*j2^3 + 2*i2^2*j2^3 + 2*i1^2*j2^4 + 2*i2*j2^4 + j2^5 + 2*i1^4*i2^2*k2 +
            i1^2*i2^3*k2 + 2*i2^4*k2 + 2*i2^3*j2*k2 + 2*i1^4*j2^2*k2 + 2*i2^2*j2^2*k2 +
            2*i1^2*j2^3*k2 + i2*j2^3*k2 + 2*j2^4*k2 + i1^6*k2^2 + i1^4*i2*k2^2 +
            i1^2*i2^2*k2^2 + 2*i1^4*j2*k2^2 + 2*i2^2*j2*k2^2 + 2*i2*j2^2*k2^2 + 2*j2^3*k2^2
            + i1^4*k2^3 + 2*i1^2*i2*k2^3 + 2*i2^2*k2^3 + i1^2*j2*k2^3 + i1^2*k2^4 +
            2*i1^6*i2*l2 + 2*i1^4*i2^2*l2 + i1^2*i2^3*l2 + i1^6*j2*l2 + 2*i1^4*i2*j2*l2 +
            2*i1^4*j2^2*l2 + i2^2*j2^2*l2 + 2*i1^2*j2^3*l2 + j2^4*l2 + i1^6*k2*l2 +
            2*i1^4*i2*k2*l2 + i2^3*k2*l2 + 2*i1^2*i2*j2*k2*l2 + 2*i2^2*j2*k2*l2 +
            i1^4*k2^2*l2 + 2*i1^2*i2*k2^2*l2 + i2^2*k2^2*l2 + i1^2*j2*k2^2*l2 +
            i2*j2*k2^2*l2 + 2*j2^2*k2^2*l2 + i2*k2^3*l2 + 2*k2^4*l2 + 2*i1^4*i2*l2^2 +
            i2^3*l2^2 + i1^2*i2*j2*l2^2 + 2*i2^2*j2*l2^2 + 2*i1^2*j2^2*l2^2 + 2*i2*j2^2*l2^2
            + i1^4*k2*l2^2 + 2*i2^2*k2*l2^2 + i2*k2^2*l2^2 + j2*k2^2*l2^2 + 2*k2^3*l2^2 +
            i1^4*l2^3 + i1^2*j2*l2^3 + 2*j2^2*l2^3 + i2*k2*l2^3 + j2*k2*l2^3 + k2^2*l2^3 +
            i1^2*l2^4 + 2*j2*l2^4 + l2^5 + 2*i1^5*i2*i3 + i1^3*i2^2*i3 + 2*i1*i2^3*i3 +
            2*i1^5*j2*i3 + 2*i1^3*i2*j2*i3 + i1*i2^2*j2*i3 + 2*i1^3*j2^2*i3 + 2*i1*j2^3*i3 +
            i1^5*k2*i3 + 2*i1^3*i2*k2*i3 + i1*i2^2*k2*i3 + 2*i1*i2*j2*k2*i3 + 2*i1^3*k2^2*i3
            + i1*i2*k2^2*i3 + 2*i1*j2*k2^2*i3 + i1*k2^3*i3 + i1^5*l2*i3 + i1^3*i2*l2*i3 +
            i1^3*j2*l2*i3 + 2*i1*j2^2*l2*i3 + i1*i2*k2*l2*i3 + i1*j2*k2*l2*i3 +
            2*i1*k2^2*l2*i3 + i1^3*l2^2*i3 + i1*j2*l2^2*i3 + i1*k2*l2^2*i3 + 2*i2^2*i3^2 +
            i2*j2*i3^2 + 2*j2^2*i3^2 + 2*i1^2*k2*i3^2 + 2*k2^2*i3^2 + i1^2*l2*i3^2 +
            2*i2*l2*i3^2 + j2*l2*i3^2 + k2*l2*i3^2 + l2^2*i3^2 + 2*i1*i3^3 + 2*i1^7*j3 +
            2*i1^5*i2*j3 + i1^3*i2^2*j3 + 2*i1*i2^3*j3 + i1*j2^3*j3 + i1^5*k2*j3 +
            i1^3*i2*k2*j3 + i1^3*j2*k2*j3 + 2*i1*i2*j2*k2*j3 + 2*i1*j2^2*k2*j3 +
            i1*i2*k2^2*j3 + 2*i1^5*l2*j3 + i1^3*i2*l2*j3 + i1^3*j2*l2*j3 + 2*i1^3*k2*l2*j3 +
            2*i1*i2*k2*l2*j3 + 2*i1*j2*k2*l2*j3 + i1*k2^2*l2*j3 + 2*i1^3*l2^2*j3 +
            i1*j2*l2^2*j3 + i2^2*i3*j3 + 2*i2*j2*i3*j3 + 2*j2^2*i3*j3 + i2*k2*i3*j3 +
            j2*k2*i3*j3 + k2*l2*i3*j3 + 2*i1^4*j3^2 + i1^2*i2*j3^2 + i2^2*j3^2 + i2*j2*j3^2
            + 2*i1^2*k2*j3^2 + i2*k2*j3^2 + 2*k2^2*j3^2 + 2*i1^2*l2*j3^2 + k2*l2*j3^2 +
            2*l2^2*j3^2 + i1*i3*j3^2 + i1^7*k3 + i1^5*i2*k3 + 2*i1^3*i2^2*k3 + i1*i2^3*k3 +
            2*i1^5*j2*k3 + 2*i1^3*i2*j2*k3 + i1*i2^2*j2*k3 + 2*i1^3*j2^2*k3 + i1*i2*j2^2*k3
            + i1*j2^3*k3 + i1^5*k2*k3 + 2*i1^3*i2*k2*k3 + i1*i2^2*k2*k3 + i1^3*j2*k2*k3 +
            i1*i2*j2*k2*k3 + 2*i1*j2^2*k2*k3 + 2*i1^3*k2^2*k3 + 2*i1*i2*k2^2*k3 +
            2*i1*j2*k2^2*k3 + 2*i1^5*l2*k3 + 2*i1*i2^2*l2*k3 + i1*i2*j2*l2*k3 +
            2*i1*j2^2*l2*k3 + 2*i1^3*k2*l2*k3 + 2*i1*i2*k2*l2*k3 + i1*j2*k2*l2*k3 +
            i1*k2^2*l2*k3 + 2*i1^3*l2^2*k3 + i1*i2*l2^2*k3 + 2*i1^2*i2*j3*k3 + 2*i2^2*j3*k3
            + 2*i1^2*j2*j3*k3 + 2*i2*j2*j3*k3 + i1^2*k2*j3*k3 + 2*i2*k2*j3*k3 +
            2*k2*l2*j3*k3 + 2*i1^4*k3^2 + 2*i1^2*i2*k3^2 + 2*i2^2*k3^2 + i2*j2*k3^2 +
            i1^2*k2*k3^2 + 2*i2*k2*k3^2 + 2*j2*k2*k3^2 + k2^2*k3^2 + i1^2*l2*k3^2 +
            2*i2*l2*k3^2 + 2*k2*l2*k3^2 + l2^2*k3^2 + 2*i1*j3*k3^2 + i1^5*i2*l3 +
            2*i1^3*i2^2*l3 + i1^5*j2*l3 + i1^3*i2*j2*l3 + i1^3*j2^2*l3 + i1*j2^3*l3 +
            2*i1^5*k2*l3 + i1^3*i2*k2*l3 + 2*i1*i2^2*k2*l3 + 2*i1*i2*j2*k2*l3 +
            i1*i2*k2^2*l3 + 2*i1^5*l2*l3 + 2*i1^3*i2*l2*l3 + 2*i1^3*j2*l2*l3 +
            2*i1*i2*j2*l2*l3 + 2*i1*j2^2*l2*l3 + i1^3*k2*l2*l3 + i1*i2*k2*l2*l3 +
            2*i1*j2*k2*l2*l3 + 2*i1*k2^2*l2*l3 + i1^3*l2^2*l3 + 2*i1*i2*l2^2*l3 +
            2*i1*j2*l2^2*l3 + i1*k2*l2^2*l3 + 2*i1^4*i3*l3 + 2*i1^2*i2*i3*l3 +
            2*i1^2*j2*i3*l3 + i2*k2*i3*l3 + i1^2*l2*i3*l3 + 2*k2*l2*i3*l3 + l2^2*i3*l3 +
            2*i1^2*i2*j3*l3 + 2*i2^2*j3*l3 + i1^2*j2*j3*l3 + j2^2*j3*l3 + i1^2*k2*j3*l3 +
            2*i2*k2*j3*l3 + j2*k2*j3*l3 + 2*k2^2*j3*l3 + i1^2*l2*j3*l3 + i2*l2*j3*l3 +
            k2*l2*j3*l3 + 2*l2^2*j3*l3 + i1^2*i2*l3^2 + i2^2*l3^2 + 2*i1^2*j2*l3^2 +
            i2*j2*l3^2 + 2*j2^2*l3^2 + i2*k2*l3^2 + 2*j2*k2*l3^2 + 2*k2^2*l3^2 + i2*l2*l3^2
            + 2*j2*l2*l3^2 + k2*l2*l3^2 + 2*i1*i3*l3^2 + 2*i1^6*i4 + 2*i2^2*j2*i4 +
            i1^2*j2^2*i4 + 2*i2*j2^2*i4 + j2^3*i4 + i1^4*k2*i4 + 2*i1^2*i2*k2*i4 +
            i2^2*k2*i4 + 2*i1^2*j2*k2*i4 + 2*j2^2*k2*i4 + 2*i1^2*k2^2*i4 + j2*k2^2*i4 +
            2*k2^3*i4 + 2*i1^2*i2*l2*i4 + i2^2*l2*i4 + 2*i2*j2*l2*i4 + 2*j2^2*l2*i4 +
            i1^2*k2*l2*i4 + i2*k2*l2*i4 + 2*j2*k2*l2*i4 + 2*k2^2*l2*i4 + i1^2*l2^2*i4 +
            i2*l2^2*i4 + 2*j2*l2^2*i4 + 2*l2^3*i4 + 2*i1^3*i3*i4 + i1*i2*i3*i4 + 2*i3^2*i4 +
            i1*i2*j3*i4 + i1*j2*j3*i4 + 2*i1*k2*j3*i4 + 2*i3*j3*i4 + 2*j3^2*i4 + i1*i2*k3*i4
            + 2*i1*j2*k3*i4 + 2*i1*l2*k3*i4 + j3*k3*i4 + 2*i1^6*j4 + i1^4*i2*j4 + i1^4*j2*j4
            + 2*i1^2*i2*j2*j4 + i2^2*j2*j4 + i1^2*j2^2*j4 + 2*j2^3*j4 + i1^2*i2*k2*j4 +
            i1^2*j2*k2*j4 + i2*j2*k2*j4 + 2*j2^2*k2*j4 + 2*i1^4*l2*j4 + i1^2*i2*l2*j4 +
            2*i2*j2*l2*j4 + j2^2*l2*j4 + i1^2*l2^2*j4 + 2*j2*l2^2*j4 + i1^3*j3*j4 +
            i1*i2*j3*j4 + 2*i1*k2*j3*j4 + 2*i1*l2*j3*j4 + 2*i1^6*k4 + 2*i1^2*i2^2*k4 +
            2*i1^4*j2*k4 + 2*i1^2*j2^2*k4 + i2*j2^2*k4 + 2*i1^4*k2*k4 + 2*i2^2*k2*k4 +
            i1^2*j2*k2*k4 + 2*i2*j2*k2*k4 + j2^2*k2*k4 + i1^2*k2^2*k4 + 2*i2*k2^2*k4 +
            i1^4*l2*k4 + i2^2*l2*k4 + 2*i1^2*j2*l2*k4 + 2*j2^2*l2*k4 + 2*i2*k2*l2*k4 +
            j2*k2*l2*k4 + 2*k2^2*l2*k4 + i2*l2^2*k4 + 2*j2*l2^2*k4 + 2*i1^3*i3*k4 +
            2*i1*i2*i3*k4 + 2*i1*j2*i3*k4 + i1*k2*i3*k4 + i1*j2*k3*k4 + i1*l2*k3*k4 +
            2*k3^2*k4 + i1^2*k4^2 + i2*k4^2 + j2*k4^2 + k2*k4^2 + 2*i1^6*l4 + i1^4*i2*l4 +
            i1^2*i2^2*l4 + 2*i1^4*j2*l4 + 2*i1^2*i2*j2*l4 + 2*i2*j2^2*l4 + 2*j2^3*l4 +
            i1^2*i2*k2*l4 + 2*i1^2*j2*k2*l4 + 2*i1^2*k2^2*l4 + 2*i2*k2^2*l4 + i1^4*l2*l4 +
            2*i1^2*j2*l2*l4 + 2*i2*j2*l2*l4 + j2^2*l2*l4 + 2*i1^2*k2*l2*l4 + 2*j2*k2*l2*l4 +
            k2^2*l2*l4 + 2*j2*l2^2*l4 + 2*k2*l2^2*l4 + i1^3*j3*l4 + 2*i1*i2*j3*l4 +
            i1*j2*j3*l4 + i1*l2*j3*l4 + 2*i1^3*k3*l4 + i1*i2*k3*l4 + i1*k2*k3*l4 + k3^2*l4 +
            2*i1*j2*l3*l4 + i1*k2*l3*l4 + i1^2*l4^2 + 2*i2*l4^2 + j2*l4^2 + k2*l4^2 +
            2*l2*l4^2 + i1^6*m4 + 2*i1^4*i2*m4 + i2^2*j2*m4 + i2*j2^2*m4 + 2*j2^3*m4 +
            2*i1^2*i2*k2*m4 + 2*i1^2*j2*k2*m4 + 2*j2*k2^2*m4 + 2*i1^4*l2*m4 + 2*i2*k2*l2*m4
            + i1^2*l2^2*m4 + k2*l2^2*m4 + 2*l2^3*m4 + 2*i1^3*i3*m4 + 2*i1*l2*i3*m4 +
            2*i1^3*j3*m4 + 2*i1*i2*j3*m4 + i1*j2*j3*m4 + i1*k2*j3*m4 + i1*l2*j3*m4 +
            i1*i2*l3*m4 + 2*i1*j2*l3*m4 + 2*i1*k2*l3*m4 + 2*i1*l2*l3*m4 + i3*l3*m4 + i1^5*i5
            + i1^3*i2*i5 + 2*i1*i2^2*i5 + i1^3*j2*i5 + i1*j2^2*i5 + i1*i2*k2*i5 +
            2*i1*j2*k2*i5 + 2*i1*k2^2*i5 + 2*i1^3*l2*i5 + i1*j2*l2*i5 + i1^2*i3*i5 +
            j2*i3*i5 + 2*l2*i3*i5 + i1^2*j3*i5 + 2*i2*j3*i5 + 2*j2*j3*i5 + 2*k2*j3*i5 +
            l2*j3*i5 + 2*i1^5*j5 + i1^3*i2*j5 + i1*i2^2*j5 + i1^3*j2*j5 + 2*i1*j2^2*j5 +
            2*i1^3*k2*j5 + i1*j2*k2*j5 + 2*i1*k2^2*j5 + i1^3*l2*j5 + 2*i2*i3*j5 + 2*j2*i3*j5
            + 2*k2*i3*j5 + i2*j3*j5 + i2*k3*j5 + j2*k3*j5 + k2*k3*j5 + 2*i1^2*l3*j5 +
            i2*l3*j5 + j2*l3*j5 + l2*l3*j5 + 2*i1^5*k5 + i1^3*i2*k5 + 2*i1^3*j2*k5 +
            i1*i2*j2*k5 + 2*i1*j2^2*k5 + 2*i1^3*k2*k5 + i1*k2^2*k5 + 2*i1^3*l2*k5 +
            i1*k2*l2*k5 + i1*l2^2*k5 + 2*k2*j3*k5 + 2*l2*j3*k5 + i1^2*k3*k5 + 2*i2*k3*k5 +
            l2*k3*k5 + i1^2*l3*k5 + 2*i2*l3*k5 + 2*j2*l3*k5 + k2*l3*k5 + l2*l3*k5 + i1*l4*k5
            + 2*i1^5*l5 + i1*i2^2*l5 + 2*i1*i2*j2*l5 + i1*j2^2*l5 + i1*i2*k2*l5 +
            i1*j2*k2*l5 + i1^3*l2*l5 + i1*i2*l2*l5 + i1*j2*l2*l5 + 2*i1*k2*l2*l5 +
            i1^2*j3*l5 + 2*k2*j3*l5 + 2*l2*j3*l5 + i2*k3*l5 + j2*k3*l5 + k2*k3*l5 + l2*k3*l5
            + 2*i1^2*l3*l5 + 2*i2*l3*l5 + 2*j2*l3*l5 + k2*l3*l5 + l2*l3*l5 + 2*i1*m4*l5 +
            2*l5^2 + 2*i1^4*i6 + 2*i2^2*i6 + 2*i1^2*j2*i6 + 2*i2*j2*i6 + 2*j2^2*i6 +
            i1^2*k2*i6 + j2*k2*i6 + 2*k2^2*i6 + i2*l2*i6 + 2*j2*l2*i6 + k2*l2*i6 +
            2*i1*k3*i6 + i1*l3*i6 + 2*l4*i6 + i1^3*i7 + i1*i2*i7 + 2*i1*j2*i7 + 2*i1*k2*i7 +
            2*i1*l2*i7 + i3*i7;
        Append(~JI, J10); Append(~Wght, 10);
    end if;
    if degmax le 10 then return JI, Wght; end if;

    /* Degree 12 */
    if degmin le 12 then
    J12:= i1^12 + i1^10*i2 + i1^8*i2^2 + i1^4*i2^4 + 2*i1^2*i2^5 + 2*i2^6 +
	i1^6*i2*j2^2 + 2*i2^4*j2^2 + i1^6*j2^3 + 2*i1^4*i2*j2^3 + i1^2*i2^2*j2^3 +
	i2^2*j2^4 + 2*i2*j2^5 + j2^6 + 2*i1^10*k2 + 2*i1^6*i2^2*k2 + i1^2*i2^4*k2 +
	2*i2^5*k2 + i1^4*i2^2*j2*k2 + i1^2*i2^3*j2*k2 + 2*i2^4*j2*k2 + i1^6*j2^2*k2 +
	2*i1^4*i2*j2^2*k2 + i2^3*j2^2*k2 + i1^4*j2^3*k2 + i2^2*j2^3*k2 + i2*j2^4*k2 +
	2*j2^5*k2 + i1^6*i2*k2^2 + i1^4*i2^2*k2^2 + i1^2*i2^3*k2^2 + i1^6*j2*k2^2 +
	2*i1^4*i2*j2*k2^2 + i1^2*i2^2*j2*k2^2 + 2*i2^3*j2*k2^2 + i1^4*j2^2*k2^2 +
	i2*j2^3*k2^2 + j2^4*k2^2 + 2*i2^3*k2^3 + i1^4*j2*k2^3 + 2*i2^2*j2*k2^3 +
	i1^2*j2^2*k2^3 + i2*j2^2*k2^3 + j2^3*k2^3 + i1^2*j2*k2^4 + 2*i2*j2*k2^4 +
	2*j2^2*k2^4 + 2*i2*k2^5 + 2*k2^6 + 2*i1^6*i2*j2*l2 + i1^4*i2^2*j2*l2 +
	i1^2*i2^3*j2*l2 + 2*i2^4*j2*l2 + i1^6*j2^2*l2 + i1^2*i2^2*j2^2*l2 +
	2*i2^3*j2^2*l2 + i1^2*i2*j2^3*l2 + 2*i2^2*j2^3*l2 + 2*j2^5*l2 + 2*i1^6*i2*k2*l2
	+ i1^4*i2^2*k2*l2 + i1^2*i2^3*k2*l2 + 2*i1^4*i2*j2*k2*l2 + i1^2*i2^2*j2*k2*l2 +
	2*i2^3*j2*k2*l2 + i1^4*j2^2*k2*l2 + 2*i1^2*i2*j2^2*k2*l2 + i2^2*j2^2*k2*l2 +
	2*i1^2*j2^3*k2*l2 + i1^2*i2^2*k2^2*l2 + 2*i1^2*i2*j2*k2^2*l2 + i2^2*j2*k2^2*l2 +
	i2*j2^2*k2^2*l2 + 2*j2^3*k2^2*l2 + i1^4*k2^3*l2 + 2*i1^2*i2*k2^3*l2 +
	2*i1^2*j2*k2^3*l2 + 2*i2*j2*k2^3*l2 + 2*j2^2*k2^3*l2 + i1^2*k2^4*l2 +
	2*j2*k2^4*l2 + k2^5*l2 + 2*i1^2*i2^3*l2^2 + i2^4*l2^2 + i1^4*i2*j2*l2^2 +
	i1^2*i2^2*j2*l2^2 + 2*i2^3*j2*l2^2 + 2*i1^4*j2^2*l2^2 + i2^2*j2^2*l2^2 +
	i1^2*j2^3*l2^2 + 2*i2*j2^3*l2^2 + i1^2*i2^2*k2*l2^2 + i2^3*k2*l2^2 +
	i1^4*j2*k2*l2^2 + 2*i2*j2^2*k2*l2^2 + 2*i1^4*k2^2*l2^2 + i1^2*i2*k2^2*l2^2 +
	i1^2*j2*k2^2*l2^2 + 2*i1^2*k2^3*l2^2 + i2*k2^3*l2^2 + 2*j2*k2^3*l2^2 + k2^4*l2^2
	+ i1^6*l2^3 + 2*i1^2*i2*j2*l2^3 + i1^2*j2^2*l2^3 + 2*i2*j2^2*l2^3 + 2*j2^3*l2^3
	+ 2*i1^2*i2*k2*l2^3 + 2*i2^2*k2*l2^3 + i1^2*j2*k2*l2^3 + 2*i2*j2*k2*l2^3 +
	2*j2^2*k2*l2^3 + 2*i1^2*k2^2*l2^3 + 2*i2*k2^2*l2^3 + 2*i1^2*i2*l2^4 + i2^2*l2^4
	+ 2*i1^2*j2*l2^4 + i2*j2*l2^4 + 2*j2^2*l2^4 + 2*i1^2*k2*l2^4 + i2*k2*l2^4 +
	j2*k2*l2^4 + k2^2*l2^4 + i2*l2^5 + j2*l2^5 + k2*l2^5 + l2^6 + 2*i1^9*i3 +
	i1^7*i2*i3 + 2*i1^3*i2^3*i3 + 2*i1*i2^4*i3 + i1^7*j2*i3 + i1^5*i2*j2*i3 +
	i1*i2^3*j2*i3 + 2*i1^3*i2*j2^2*i3 + i1^3*j2^3*i3 + 2*i1*i2*j2^3*i3 +
	2*i1*j2^4*i3 + i1^7*k2*i3 + i1^5*i2*k2*i3 + i1^3*i2^2*k2*i3 + i1*i2^3*k2*i3 +
	i1^5*j2*k2*i3 + i1*i2^2*j2*k2*i3 + 2*i1^3*j2^2*k2*i3 + 2*i1*i2*j2^2*k2*i3 +
	2*i1*j2^3*k2*i3 + i1^5*k2^2*i3 + 2*i1^3*i2*k2^2*i3 + i1^3*j2*k2^2*i3 +
	i1*j2^2*k2^2*i3 + 2*i1^3*k2^3*i3 + i1*i2*k2^3*i3 + 2*i1*k2^4*i3 +
	i1^3*i2^2*l2*i3 + 2*i1*i2^3*l2*i3 + i1^3*j2^2*l2*i3 + 2*i1*j2^3*l2*i3 +
	i1^5*k2*l2*i3 + i1*i2*j2*k2*l2*i3 + i1*j2^2*k2*l2*i3 + 2*i1*j2*k2^2*l2*i3 +
	2*i1*k2^3*l2*i3 + 2*i1*i2^2*l2^2*i3 + i1^3*j2*l2^2*i3 + i1*j2^2*l2^2*i3 +
	2*i1*i2*k2*l2^2*i3 + i1*j2*k2*l2^2*i3 + i1*k2^2*l2^2*i3 + 2*i1^3*l2^3*i3 +
	i1*i2*l2^3*i3 + i1*j2*l2^3*i3 + 2*i1*k2*l2^3*i3 + i1*l2^4*i3 + 2*i1^4*i2*i3^2 +
	i2^3*i3^2 + 2*i1^4*j2*i3^2 + i1^2*j2^2*i3^2 + i2*j2^2*i3^2 + 2*i1^2*i2*k2*i3^2 +
	2*i2^2*k2*i3^2 + 2*i2*j2*k2*i3^2 + i1^2*k2^2*i3^2 + j2*k2^2*i3^2 + k2^3*i3^2 +
	i1^4*l2*i3^2 + i1^2*i2*l2*i3^2 + 2*i1^2*j2*l2*i3^2 + 2*i2*j2*l2*i3^2 +
	i1^2*k2*l2*i3^2 + i2*k2*l2*i3^2 + j2*k2*l2*i3^2 + 2*k2^2*l2*i3^2 +
	2*i1^2*l2^2*i3^2 + 2*k2*l2^2*i3^2 + 2*l2^3*i3^2 + i1^3*i3^3 + i1*i2*i3^3 +
	i1*j2*i3^3 + 2*i1*k2*i3^3 + 2*i1*l2*i3^3 + 2*i3^4 + i1^9*j3 + 2*i1^5*i2^2*j3 +
	i1^3*i2^3*j3 + 2*i1*i2^4*j3 + i1^7*j2*j3 + 2*i1^5*i2*j2*j3 + 2*i1^3*i2^2*j2*j3 +
	2*i1*i2^3*j2*j3 + 2*i1^3*i2*j2^2*j3 + 2*i1^3*j2^3*j3 + 2*i1*i2*j2^3*j3 +
	2*i1*j2^4*j3 + 2*i1^7*k2*j3 + 2*i1^3*i2^2*k2*j3 + i1*i2^3*k2*j3 +
	2*i1^5*j2*k2*j3 + i1^3*i2*j2*k2*j3 + 2*i1*j2^3*k2*j3 + 2*i1*i2^2*k2^2*j3 +
	i1^3*j2*k2^2*j3 + i1*j2^2*k2^2*j3 + 2*i1^3*k2^3*j3 + 2*i1*j2*k2^3*j3 +
	i1*k2^4*j3 + i1*i2^3*l2*j3 + 2*i1^5*j2*l2*j3 + i1*i2^2*j2*l2*j3 +
	2*i1^3*j2^2*l2*j3 + i1*i2*j2^2*l2*j3 + 2*i1*j2^3*l2*j3 + 2*i1^5*k2*l2*j3 +
	2*i1^3*j2*k2*l2*j3 + 2*i1*i2*j2*k2*l2*j3 + i1^3*k2^2*l2*j3 + 2*i1*i2*k2^2*l2*j3
	+ i1*j2*k2^2*l2*j3 + 2*i1*i2^2*l2^2*j3 + i1^3*j2*l2^2*j3 + i1*j2^2*l2^2*j3 +
	2*i1^3*k2*l2^2*j3 + i1*i2*k2*l2^2*j3 + i1^3*l2^3*j3 + i1*i2*l2^3*j3 +
	i1*j2*l2^3*j3 + 2*i1*k2*l2^3*j3 + 2*i1^4*i2*i3*j3 + i1^2*i2^2*i3*j3 + i2^3*i3*j3
	+ i1^4*j2*i3*j3 + 2*i1^2*i2*j2*i3*j3 + i1^2*j2^2*i3*j3 + j2^3*i3*j3 +
	2*i1^4*k2*i3*j3 + 2*i1^2*i2*k2*i3*j3 + i1^2*j2*k2*i3*j3 + i2*k2^2*i3*j3 +
	j2*k2^2*i3*j3 + k2^3*i3*j3 + i1^2*i2*l2*i3*j3 + 2*i2^2*l2*i3*j3 + i2*j2*l2*i3*j3
	+ j2^2*l2*i3*j3 + 2*i1^2*k2*l2*i3*j3 + 2*i2*k2*l2*i3*j3 + i2*l2^2*i3*j3 +
	2*j2*l2^2*i3*j3 + l2^3*i3*j3 + i1^3*i3^2*j3 + i1*j2*i3^2*j3 + i1*k2*i3^2*j3 +
	i3^3*j3 + i1^6*j3^2 + 2*i1^4*j2*j3^2 + 2*i1^2*i2*j2*j3^2 + 2*i2*j2^2*j3^2 +
	2*i1^4*k2*j3^2 + i2^2*k2*j3^2 + 2*i1^2*k2^2*j3^2 + i2*k2^2*j3^2 + j2*k2^2*j3^2 +
	k2^3*j3^2 + 2*i1^2*i2*l2*j3^2 + i2^2*l2*j3^2 + i2*k2*l2*j3^2 + 2*j2*k2*l2*j3^2 +
	2*i2*l2^2*j3^2 + l2^3*j3^2 + 2*i1^3*i3*j3^2 + i1*i2*i3*j3^2 + 2*i1*k2*i3*j3^2 +
	i3^2*j3^2 + 2*i1^3*j3^3 + 2*i1*i2*j3^3 + i1*k2*j3^3 + i3*j3^3 + i1^9*k3 +
	i1^7*i2*k3 + i1^7*j2*k3 + 2*i1^5*i2*j2*k3 + i1^3*i2^2*j2*k3 + i1*i2^2*j2^2*k3 +
	2*i1^3*j2^3*k3 + 2*i1*j2^4*k3 + 2*i1^5*i2*k2*k3 + i1^3*i2^2*k2*k3 +
	i1*i2^3*k2*k3 + i1^5*j2*k2*k3 + i1*i2^2*j2*k2*k3 + 2*i1^3*j2^2*k2*k3 +
	i1*i2*j2^2*k2*k3 + i1^5*k2^2*k3 + 2*i1*i2^2*k2^2*k3 + i1*i2*j2*k2^2*k3 +
	2*i1*j2^2*k2^2*k3 + i1^3*k2^3*k3 + i1*i2*k2^3*k3 + 2*i1*j2*k2^3*k3 + i1*k2^4*k3
	+ i1^5*i2*l2*k3 + i1^3*i2^2*l2*k3 + 2*i1*i2^3*l2*k3 + 2*i1^5*j2*l2*k3 +
	i1^3*i2*j2*l2*k3 + i1*i2^2*j2*l2*k3 + i1*j2^3*l2*k3 + i1^5*k2*l2*k3 +
	2*i1^3*i2*k2*l2*k3 + i1*i2^2*k2*l2*k3 + i1^3*j2*k2*l2*k3 + i1*i2*j2*k2*l2*k3 +
	2*i1*j2^2*k2*l2*k3 + i1*i2*k2^2*l2*k3 + 2*i1*j2*k2^2*l2*k3 + 2*i1^3*i2*l2^2*k3 +
	2*i1*i2^2*l2^2*k3 + i1^3*j2*l2^2*k3 + 2*i1*i2*j2*l2^2*k3 + i1*j2^2*l2^2*k3 +
	i1^3*k2*l2^2*k3 + 2*i1*i2*k2*l2^2*k3 + i1*j2*k2*l2^2*k3 + 2*i1*k2^2*l2^2*k3 +
	2*i1^3*l2^3*k3 + 2*i1*j2*l2^3*k3 + i1*l2^4*k3 + i1^4*i2*j3*k3 + i1^2*i2^2*j3*k3
	+ 2*i2^3*j3*k3 + 2*i1^4*j2*j3*k3 + i1^2*i2*j2*j3*k3 + i2^2*j2*j3*k3 +
	i1^2*j2^2*j3*k3 + i1^4*k2*j3*k3 + 2*i1^2*i2*k2*j3*k3 + i1^2*j2*k2*j3*k3 +
	j2^2*k2*j3*k3 + 2*i2*k2^2*j3*k3 + 2*k2^3*j3*k3 + i2^2*l2*j3*k3 +
	i1^2*j2*l2*j3*k3 + i2*k2*l2*j3*k3 + 2*i2*l2^2*j3*k3 + l2^3*j3*k3 + i1^3*j3^2*k3
	+ 2*i1*i2*j3^2*k3 + 2*i1*k2*j3^2*k3 + 2*j3^3*k3 + 2*i1^6*k3^2 + i1^4*i2*k3^2 +
	2*i1^2*i2^2*k3^2 + i1^4*j2*k3^2 + 2*i2*j2^2*k3^2 + 2*i1^2*i2*k2*k3^2 +
	i1^2*j2*k2*k3^2 + i2*j2*k2*k3^2 + j2^2*k2*k3^2 + 2*i1^2*k2^2*k3^2 +
	2*i2*k2^2*k3^2 + j2*k2^2*k3^2 + k2^3*k3^2 + 2*i1^2*i2*l2*k3^2 +
	2*i1^2*j2*l2*k3^2 + i2*j2*l2*k3^2 + i1^2*k2*l2*k3^2 + i2*k2*l2*k3^2 +
	k2^2*l2*k3^2 + 2*i1^2*l2^2*k3^2 + l2^3*k3^2 + i1^3*j3*k3^2 + i1*l2*j3*k3^2 +
	2*j3^2*k3^2 + i1^3*k3^3 + 2*i1*i2*k3^3 + i1*l2*k3^3 + 2*i1^7*i2*l3 +
	i1^5*i2^2*l3 + 2*i1^7*j2*l3 + 2*i1^5*i2*j2*l3 + 2*i1^3*i2*j2^2*l3 + i1*j2^4*l3 +
	i1^7*k2*l3 + i1^5*i2*k2*l3 + 2*i1^3*i2^2*k2*l3 + 2*i1^3*i2*j2*k2*l3 +
	2*i1*j2^3*k2*l3 + i1^5*k2^2*l3 + 2*i1*i2^2*k2^2*l3 + i1^3*j2*k2^2*l3 +
	i1*j2^2*k2^2*l3 + i1^3*k2^3*l3 + i1*i2*k2^3*l3 + i1*i2^3*l2*l3 + i1^5*j2*l2*l3 +
	i1^3*i2*j2*l2*l3 + 2*i1^3*j2^2*l2*l3 + 2*i1*i2*j2^2*l2*l3 + 2*i1^5*k2*l2*l3 +
	2*i1^3*i2*k2*l2*l3 + i1*i2^2*k2*l2*l3 + i1*i2*j2*k2*l2*l3 + 2*i1^3*k2^2*l2*l3 +
	i1*i2*k2^2*l2*l3 + i1*j2*k2^2*l2*l3 + i1^3*i2*l2^2*l3 + i1*i2^2*l2^2*l3 +
	i1^3*j2*l2^2*l3 + i1*i2*j2*l2^2*l3 + 2*i1*j2^2*l2^2*l3 + i1^3*k2*l2^2*l3 +
	2*i1*i2*k2*l2^2*l3 + 2*i1*j2*k2*l2^2*l3 + 2*i1*i2*l2^3*l3 + i1*j2*l2^3*l3 +
	i1*k2*l2^3*l3 + i1^2*i2^2*i3*l3 + 2*i1^4*j2*i3*l3 + i1^2*i2*j2*i3*l3 +
	i2*j2^2*i3*l3 + 2*j2^3*i3*l3 + i1^2*i2*k2*i3*l3 + 2*i2*j2*k2*i3*l3 +
	i1^2*k2^2*i3*l3 + i2*k2^2*i3*l3 + j2*k2^2*i3*l3 + 2*i2^2*l2*i3*l3 +
	i2*j2*l2*i3*l3 + j2^2*l2*i3*l3 + 2*i1^2*k2*l2*i3*l3 + i2*k2*l2*i3*l3 +
	2*j2*k2*l2*i3*l3 + 2*i1^2*l2^2*i3*l3 + 2*i2*l2^2*i3*l3 + l2^3*i3*l3 +
	2*i1^3*i3^2*l3 + 2*i1*i2*i3^2*l3 + 2*i3^3*l3 + i1^4*i2*j3*l3 + i2^3*j3*l3 +
	2*i1^4*j2*j3*l3 + i2^2*j2*j3*l3 + 2*j2^3*j3*l3 + 2*i1^4*k2*j3*l3 +
	2*i2*j2*k2*j3*l3 + i2*k2^2*j3*l3 + k2^3*j3*l3 + i1^4*l2*j3*l3 + i1^2*i2*l2*j3*l3
	+ 2*i2^2*l2*j3*l3 + i1^2*j2*l2*j3*l3 + 2*j2^2*l2*j3*l3 + 2*i1^2*k2*l2*j3*l3 +
	2*j2*k2*l2*j3*l3 + i1^2*l2^2*j3*l3 + l2^3*j3*l3 + i1^4*i2*l3^2 + i2^3*l3^2 +
	2*i1^2*i2*j2*l3^2 + 2*j2^3*l3^2 + i1^4*k2*l3^2 + i2^2*k2*l3^2 + 2*i2*j2*k2*l3^2
	+ i1^2*k2^2*l3^2 + 2*i2*k2^2*l3^2 + 2*j2*k2^2*l3^2 + k2^3*l3^2 + i1^2*i2*l2*l3^2
	+ i2*j2*l2*l3^2 + i1^2*k2*l2*l3^2 + 2*i2*k2*l2*l3^2 + 2*j2*k2*l2*l3^2 +
	2*i1^2*l2^2*l3^2 + i2*l2^2*l3^2 + k2*l2^2*l3^2 + l2^3*l3^2 + 2*i1*k2*i3*l3^2 +
	i1^3*l3^3 + i1*i2*l3^3 + 2*i1*k2*l3^3 + 2*i3*l3^3 + i1^6*i2*i4 + i1^2*i2^3*i4 +
	i2^4*i4 + i1^6*j2*i4 + 2*i1^4*i2*j2*i4 + 2*i2^3*j2*i4 + i1^4*j2^2*i4 +
	2*i1^2*i2*j2^2*i4 + 2*i2^2*j2^2*i4 + 2*i1^2*j2^3*i4 + 2*i2*j2^3*i4 + 2*j2^4*i4 +
	2*i1^6*k2*i4 + i1^2*i2^2*k2*i4 + i2^3*k2*i4 + 2*i1^4*j2*k2*i4 + i1^2*i2*j2*k2*i4
	+ i2^2*j2*k2*i4 + i1^2*j2^2*k2*i4 + i1^4*k2^2*i4 + i1^2*i2*k2^2*i4 +
	i2^2*k2^2*i4 + 2*i1^2*j2*k2^2*i4 + i2*k2^3*i4 + j2*k2^3*i4 + 2*i1^4*i2*l2*i4 +
	i1^2*i2^2*l2*i4 + 2*i2^3*l2*i4 + 2*i1^4*j2*l2*i4 + 2*i1^2*j2^2*l2*i4 +
	j2^3*l2*i4 + 2*i1^4*k2*l2*i4 + i1^2*i2*k2*l2*i4 + i1^2*j2*k2*l2*i4 +
	j2^2*k2*l2*i4 + i1^2*k2^2*l2*i4 + 2*j2*k2^2*l2*i4 + 2*k2^3*l2*i4 + i1^4*l2^2*i4
	+ i2^2*l2^2*i4 + i1^2*j2*l2^2*i4 + 2*i2*j2*l2^2*i4 + 2*i1^2*k2*l2^2*i4 +
	i2*k2*l2^2*i4 + k2^2*l2^2*i4 + j2*l2^3*i4 + 2*l2^4*i4 + 2*i1^5*i3*i4 +
	i1^3*i2*i3*i4 + 2*i1^3*j2*i3*i4 + 2*i1^3*k2*i3*i4 + 2*i1*k2^2*i3*i4 +
	2*i1*i2*l2*i3*i4 + i1*j2*l2*i3*i4 + i1*k2*l2*i3*i4 + i1*l2^2*i3*i4 +
	i1^2*i3^2*i4 + j2*i3^2*i4 + 2*l2*i3^2*i4 + i1*i2^2*j3*i4 + i1^3*j2*j3*i4 +
	2*i1*i2*j2*j3*i4 + 2*i1*j2^2*j3*i4 + 2*i1*i2*k2*j3*i4 + 2*i1*i2*l2*j3*i4 +
	2*i1*j2*l2*j3*i4 + i1*k2*l2*j3*i4 + 2*i1^2*i3*j3*i4 + 2*i2*i3*j3*i4 +
	2*j2*i3*j3*i4 + l2*i3*j3*i4 + j2*j3^2*i4 + 2*k2*j3^2*i4 + 2*i1^3*i2*k3*i4 +
	2*i1*i2^2*k3*i4 + 2*i1^3*j2*k3*i4 + 2*i1*j2^2*k3*i4 + i1^3*k2*k3*i4 +
	2*i1^3*l2*k3*i4 + i1*i2*l2*k3*i4 + i1*j2*l2*k3*i4 + i1*k2*l2*k3*i4 +
	i1*l2^2*k3*i4 + i1^2*j3*k3*i4 + i2*j3*k3*i4 + 2*l2*j3*k3*i4 + i1^8*j4 +
	2*i1^6*i2*j4 + 2*i1^6*j2*j4 + 2*i1^4*i2*j2*j4 + i1^2*i2^2*j2*j4 +
	i1^2*i2*j2^2*j4 + 2*i2^2*j2^2*j4 + 2*i1^2*j2^3*j4 + i2*j2^3*j4 + j2^4*j4 +
	i1^6*k2*j4 + i1^4*i2*k2*j4 + i1^4*j2*k2*j4 + 2*i2^2*j2*k2*j4 + 2*i1^2*j2^2*k2*j4
	+ 2*j2^3*k2*j4 + i1^4*k2^2*j4 + i1^2*i2*k2^2*j4 + j2^2*k2^2*j4 + j2*k2^3*j4 +
	i1^6*l2*j4 + i1^4*i2*l2*j4 + 2*i1^2*i2^2*l2*j4 + i2^2*j2*l2*j4 + i2*j2^2*l2*j4 +
	2*i1^4*k2*l2*j4 + 2*i1^2*i2*k2*l2*j4 + i1^2*j2*k2*l2*j4 + 2*i2*j2*k2*l2*j4 +
	2*j2^2*k2*l2*j4 + 2*i1^2*k2^2*l2*j4 + 2*j2*k2^2*l2*j4 + 2*i1^2*i2*l2^2*j4 +
	i1^2*j2*l2^2*j4 + i1^2*k2*l2^2*j4 + 2*i1^2*l2^3*j4 + 2*i1^5*j3*j4 +
	2*i1*i2^2*j3*j4 + i1^3*j2*j3*j4 + 2*i1*i2*j2*j3*j4 + 2*i1*i2*k2*j3*j4 +
	i1*k2^2*j3*j4 + 2*i1^3*l2*j3*j4 + i1*l2^2*j3*j4 + 2*i1^8*k4 + i1^6*i2*k4 +
	2*i1^2*i2^3*k4 + i2^4*k4 + 2*i1^6*j2*k4 + i1^4*i2*j2*k4 + i2^3*j2*k4 +
	2*i1^2*i2*j2^2*k4 + i2^2*j2^2*k4 + i1^2*j2^3*k4 + 2*i2*j2^3*k4 + j2^4*k4 +
	2*i1^6*k2*k4 + i1^4*i2*k2*k4 + i1^2*i2^2*k2*k4 + 2*i2^3*k2*k4 + 2*i1^4*j2*k2*k4
	+ i1^2*i2*j2*k2*k4 + 2*i2^2*j2*k2*k4 + i2*j2^2*k2*k4 + 2*j2^3*k2*k4 +
	2*i1^4*k2^2*k4 + 2*i1^2*i2*k2^2*k4 + 2*i2^2*k2^2*k4 + i1^2*j2*k2^2*k4 +
	2*i2*j2*k2^2*k4 + j2^2*k2^2*k4 + 2*i1^2*k2^3*k4 + 2*i2*k2^3*k4 + j2*k2^3*k4 +
	k2^4*k4 + i1^6*l2*k4 + 2*i1^2*i2^2*l2*k4 + i2^3*l2*k4 + 2*i2^2*j2*l2*k4 +
	2*i1^2*j2^2*l2*k4 + 2*i2*j2^2*l2*k4 + i2^2*k2*l2*k4 + i1^2*j2*k2*l2*k4 +
	2*i2*j2*k2*l2*k4 + 2*j2^2*k2*l2*k4 + i1^4*l2^2*k4 + i1^2*i2*l2^2*k4 +
	j2^2*l2^2*k4 + i1^2*k2*l2^2*k4 + j2*k2*l2^2*k4 + 2*k2^2*l2^2*k4 + 2*i1^2*l2^3*k4
	+ i2*l2^3*k4 + 2*k2*l2^3*k4 + 2*l2^4*k4 + i1^5*i3*k4 + i1^3*i2*i3*k4 +
	2*i1^3*j2*i3*k4 + i1^3*k2*i3*k4 + 2*i1*j2*k2*i3*k4 + 2*i1*k2^2*i3*k4 +
	2*i1^3*l2*i3*k4 + i1*j2*l2*i3*k4 + i1*l2^2*i3*k4 + 2*i1^2*i3^2*k4 + 2*i2*i3^2*k4
	+ i1^3*j2*k3*k4 + 2*i1*i2*j2*k3*k4 + 2*i1*j2^2*k3*k4 + i1*i2*k2*k3*k4 +
	2*i1*j2*k2*k3*k4 + 2*i1*k2^2*k3*k4 + 2*i1*i2*l2*k3*k4 + 2*i1^2*k3^2*k4 +
	i2*k3^2*k4 + j2*k3^2*k4 + k2*k3^2*k4 + 2*l2*k3^2*k4 + 2*i1^2*i2*k4^2 + i2^2*k4^2
	+ 2*i1^2*j2*k4^2 + 2*i2*j2*k4^2 + j2^2*k4^2 + 2*i1^2*k2*k4^2 + i2*k2*k4^2 +
	2*j2*k2*k4^2 + k2^2*k4^2 + i1^2*l2*k4^2 + 2*i2*l2*k4^2 + 2*j2*l2*k4^2 +
	2*k2*l2*k4^2 + 2*i1*i3*k4^2 + i1^6*i2*l4 + i1^4*i2^2*l4 + 2*i1^6*j2*l4 +
	2*i1^2*i2^2*j2*l4 + 2*i1^4*j2^2*l4 + i1^2*i2*j2^2*l4 + 2*i1^2*j2^3*l4 +
	i2*j2^3*l4 + i1^6*k2*l4 + 2*i2^2*j2*k2*l4 + 2*i1^2*j2^2*k2*l4 + i2*j2^2*k2*l4 +
	2*j2^3*k2*l4 + 2*i1^2*j2*k2^2*l4 + 2*j2^2*k2^2*l4 + 2*i2*k2^3*l4 +
	i1^2*i2^2*l2*l4 + 2*i1^4*j2*l2*l4 + 2*i1^2*i2*j2*l2*l4 + i2^2*j2*l2*l4 +
	2*i1^2*j2^2*l2*l4 + i1^4*k2*l2*l4 + i2^2*k2*l2*l4 + 2*j2^2*k2*l2*l4 +
	2*i2*k2^2*l2*l4 + i1^2*i2*l2^2*l4 + 2*j2*k2*l2^2*l4 + j2*l2^3*l4 + 2*k2*l2^3*l4
	+ i1*i2^2*j3*l4 + i1*j2^2*j3*l4 + 2*i1^3*k2*j3*l4 + 2*i1*i2*k2*j3*l4 +
	2*i1*k2^2*j3*l4 + 2*i1*k2*l2*j3*l4 + i1^5*k3*l4 + 2*i1*i2^2*k3*l4 +
	2*i1^3*j2*k3*l4 + 2*i1*i2*j2*k3*l4 + i1*i2*k2*k3*l4 + 2*i1*j2*k2*k3*l4 +
	2*i1*k2^2*k3*l4 + i1*i2*l2*k3*l4 + 2*i1*j2*l2*k3*l4 + i1*k2*l2*k3*l4 +
	i1*l2^2*k3*l4 + 2*i1^2*j3*k3*l4 + i2*j3*k3*l4 + l2*j3*k3*l4 + i1^2*k3^2*l4 +
	2*i2*k3^2*l4 + 2*j2*k3^2*l4 + 2*k2*k3^2*l4 + 2*i1*j2^2*l3*l4 + i1*k2^2*l3*l4 +
	i1^3*l2*l3*l4 + 2*i1*l2^2*l3*l4 + 2*i2*l3^2*l4 + k2*l3^2*l4 + 2*i1^2*i2*l4^2 +
	2*i2^2*l4^2 + 2*i1^2*j2*l4^2 + 2*i2*j2*l4^2 + 2*i1^2*k2*l4^2 + i2*k2*l4^2 +
	j2*k2*l4^2 + 2*k2^2*l4^2 + 2*i1^2*l2*l4^2 + i2*l2*l4^2 + j2*l2*l4^2 + k2*l2*l4^2
	+ l2^2*l4^2 + 2*l4^3 + 2*i1^8*m4 + i1^6*i2*m4 + 2*i1^6*j2*m4 + i1^4*i2*j2*m4 +
	2*i1^2*i2^2*j2*m4 + i2^3*j2*m4 + i1^2*i2*j2^2*m4 + i1^2*j2^3*m4 + j2^4*m4 +
	2*i1^6*k2*m4 + 2*i1^4*i2*k2*m4 + 2*i1^4*j2*k2*m4 + 2*i2^2*j2*k2*m4 +
	i1^2*j2^2*k2*m4 + 2*i2*j2^2*k2*m4 + j2^3*k2*m4 + 2*i1^4*k2^2*m4 +
	2*i1^2*i2*k2^2*m4 + i2*j2*k2^2*m4 + j2*k2^3*m4 + 2*i1^6*l2*m4 + 2*i1^4*i2*l2*m4
	+ i1^4*j2*l2*m4 + i1^2*j2^2*l2*m4 + 2*i2*j2^2*l2*m4 + 2*j2^3*l2*m4 +
	i1^4*k2*l2*m4 + 2*i2*k2^2*l2*m4 + i1^2*i2*l2^2*m4 + i2^2*l2^2*m4 +
	2*i1^2*j2*l2^2*m4 + i2*j2*l2^2*m4 + 2*j2^2*l2^2*m4 + 2*i2*k2*l2^2*m4 +
	2*i1^2*l2^3*m4 + 2*j2*l2^3*m4 + 2*l2^4*m4 + 2*i1^5*i3*m4 + i1^3*i2*i3*m4 +
	2*i1*i2^2*i3*m4 + 2*i1^3*j2*i3*m4 + 2*i1*j2^2*i3*m4 + i1^3*k2*i3*m4 +
	2*i1*k2^2*i3*m4 + i1*i2*l2*i3*m4 + i1*j2*l2*i3*m4 + i1*k2*l2*i3*m4 +
	i1^2*i3^2*m4 + j2*i3^2*m4 + 2*k2*i3^2*m4 + 2*l2*i3^2*m4 + i1^5*j3*m4 +
	i1*i2^2*j3*m4 + i1^3*j2*j3*m4 + 2*i1*j2^2*j3*m4 + i1*i2*k2*j3*m4 +
	2*i1*j2*k2*j3*m4 + 2*i1*k2^2*j3*m4 + i1^3*l2*j3*m4 + 2*i1*j2*l2*j3*m4 +
	2*i1*l2^2*j3*m4 + i1^5*l3*m4 + i1*i2^2*l3*m4 + i1*j2^2*l3*m4 + i1^3*k2*l3*m4 +
	i1*i2*k2*l3*m4 + i1*k2^2*l3*m4 + i1^3*l2*l3*m4 + i1*i2*l2*l3*m4 + i1*k2*l2*l3*m4
	+ i1*l2^2*l3*m4 + i2*i3*l3*m4 + j2*i3*l3*m4 + 2*k2*i3*l3*m4 + l2*i3*l3*m4 +
	l2*l3^2*m4 + i1^7*i5 + 2*i1^5*i2*i5 + i1^3*i2^2*i5 + 2*i1*i2^3*i5 +
	i1^3*i2*j2*i5 + 2*i1*i2^2*j2*i5 + 2*i1*j2^3*i5 + i1^3*i2*k2*i5 + i1*i2*j2*k2*i5
	+ i1^3*k2^2*i5 + i1*i2*k2^2*i5 + 2*i1*j2*k2^2*i5 + i1*k2^3*i5 + i1^5*l2*i5 +
	i1*i2^2*l2*i5 + i1^3*j2*l2*i5 + i1*i2*j2*l2*i5 + i1*j2^2*l2*i5 + i1^3*k2*l2*i5 +
	2*i1*i2*k2*l2*i5 + 2*i1*j2*k2*l2*i5 + i1*k2^2*l2*i5 + 2*i1^3*l2^2*i5 +
	2*i1*k2*l2^2*i5 + i1*l2^3*i5 + i2^2*i3*i5 + i1^2*j2*i3*i5 + 2*j2^2*i3*i5 +
	2*k2^2*i3*i5 + i1^2*l2*i3*i5 + 2*i2*l2*i3*i5 + 2*l2^2*i3*i5 + 2*i1*i3^2*i5 +
	i1^2*i2*j3*i5 + i1^2*j2*j3*i5 + 2*j2^2*j3*i5 + i1^2*k2*j3*i5 + i2*k2*j3*i5 +
	i1^2*l2*j3*i5 + i2*l2*j3*i5 + j2*l2*j3*i5 + k2*l2*j3*i5 + l2^2*j3*i5 +
	i1*i3*j3*i5 + i1^5*i2*j5 + i1^3*i2^2*j5 + i1^3*i2*j2*j5 + i1^3*j2^2*j5 +
	i1*i2*j2^2*j5 + i1*j2^3*j5 + i1^5*k2*j5 + i1*i2^2*k2*j5 + i1^3*j2*k2*j5 +
	2*i1*i2*j2*k2*j5 + i1*i2*k2^2*j5 + i1*k2^3*j5 + i1*i2^2*l2*j5 + 2*i1^3*j2*l2*j5
	+ 2*i1*i2*j2*l2*j5 + 2*i1*j2^2*l2*j5 + i1^3*k2*l2*j5 + 2*i1*k2^2*l2*j5 +
	i1*i2*l2^2*j5 + 2*i1*j2*l2^2*j5 + 2*i1*k2*l2^2*j5 + i1^4*i3*j5 + i1^2*i2*i3*j5 +
	i1^2*j2*i3*j5 + j2^2*i3*j5 + i1^2*k2*i3*j5 + 2*i2*k2*i3*j5 + 2*j2*k2*i3*j5 +
	k2^2*i3*j5 + 2*i1^2*l2*i3*j5 + 2*i2*l2*i3*j5 + 2*l2^2*i3*j5 + 2*i1*i3^2*j5 +
	2*i1^4*j3*j5 + i1^2*j2*j3*j5 + 2*i1^2*k2*j3*j5 + 2*i2*k2*j3*j5 + 2*j2*k2*j3*j5 +
	k2^2*j3*j5 + 2*i1^2*l2*j3*j5 + 2*j2*l2*j3*j5 + k2*l2*j3*j5 + 2*l2^2*j3*j5 +
	2*i1^4*k3*j5 + 2*i1^2*i2*k3*j5 + 2*i1^2*j2*k3*j5 + i2*j2*k3*j5 + 2*j2^2*k3*j5 +
	2*i1^2*k2*k3*j5 + i2*k2*k3*j5 + j2*k2*k3*j5 + 2*k2^2*k3*j5 + i1^2*l2*k3*j5 +
	i2*l2*k3*j5 + 2*j2*l2*k3*j5 + k2*l2*k3*j5 + l2^2*k3*j5 + 2*i1*k3^2*j5 +
	2*i1^4*l3*j5 + i1^2*i2*l3*j5 + i2^2*l3*j5 + i1^2*j2*l3*j5 + 2*i2*j2*l3*j5 +
	j2^2*l3*j5 + i1^2*k2*l3*j5 + 2*i2*k2*l3*j5 + 2*j2*k2*l3*j5 + 2*k2^2*l3*j5 +
	2*i2*l2*l3*j5 + 2*j2*l2*l3*j5 + 2*k2*l2*l3*j5 + l2^2*l3*j5 + 2*i1^3*i4*j5 +
	i1*i2*i4*j5 + 2*i1*j2*i4*j5 + 2*i1*k2*i4*j5 + 2*i3*i4*j5 + i1^3*l4*j5 +
	2*i1*l2*l4*j5 + j3*l4*j5 + 2*i1^2*j5^2 + l2*j5^2 + i1^7*k5 + 2*i1^5*i2*k5 +
	2*i1^3*i2*j2*k5 + 2*i1*i2^2*j2*k5 + 2*i1*i2*j2^2*k5 + 2*i1*j2^3*k5 +
	2*i1^3*i2*k2*k5 + i1*i2^2*k2*k5 + i1*i2*j2*k2*k5 + 2*i1^3*k2^2*k5 +
	2*i1*i2*k2^2*k5 + 2*i1*k2^3*k5 + 2*i1^5*l2*k5 + 2*i1^3*i2*l2*k5 +
	2*i1*i2^2*l2*k5 + 2*i1^3*j2*l2*k5 + 2*i1*i2*j2*l2*k5 + i1*j2^2*l2*k5 +
	i1^3*l2^2*k5 + 2*i1*i2*l2^2*k5 + 2*i1*k2*l2^2*k5 + i1*l2^3*k5 + 2*i2*j2*j3*k5 +
	i2*k2*j3*k5 + k2^2*j3*k5 + i2*l2*j3*k5 + 2*j2*l2*j3*k5 + k2*l2*j3*k5 +
	2*i1^4*k3*k5 + 2*i1^2*i2*k3*k5 + 2*i2^2*k3*k5 + i1^2*j2*k3*k5 + 2*i2*j2*k3*k5 +
	j2^2*k3*k5 + i1^2*k2*k3*k5 + i2*k2*k3*k5 + 2*j2*k2*k3*k5 + k2^2*k3*k5 +
	i1^2*l2*k3*k5 + 2*i2*l2*k3*k5 + i2^2*l3*k5 + 2*i1^2*j2*l3*k5 + i2*j2*l3*k5 +
	2*j2^2*l3*k5 + i1^2*k2*l3*k5 + 2*i2*k2*l3*k5 + k2^2*l3*k5 + 2*k2*l2*l3*k5 +
	2*i1*i2*l4*k5 + i1*j2*l4*k5 + i1*k2*l4*k5 + 2*k3*l4*k5 + 2*i1^7*l5 + i1^5*i2*l5
	+ 2*i1^3*i2^2*l5 + 2*i1*i2^3*l5 + 2*i1^5*j2*l5 + 2*i1^3*i2*j2*l5 +
	2*i1*i2^2*j2*l5 + 2*i1^3*j2^2*l5 + i1^5*k2*l5 + 2*i1^3*i2*k2*l5 +
	2*i1*i2^2*k2*l5 + 2*i1^3*j2*k2*l5 + i1*i2*j2*k2*l5 + 2*i1*j2^2*k2*l5 +
	i1^3*k2^2*l5 + i1*i2*k2^2*l5 + 2*i1*k2^3*l5 + 2*i1^5*l2*l5 + 2*i1*i2^2*l2*l5 +
	2*i1*j2^2*l2*l5 + i1^3*k2*l2*l5 + 2*i1*i2*k2*l2*l5 + 2*i1^3*l2^2*l5 +
	i1*i2*l2^2*l5 + i1*l2^3*l5 + i1^4*i3*l5 + i1^2*i2*i3*l5 + 2*i2^2*i3*l5 +
	i2*j2*i3*l5 + j2^2*i3*l5 + 2*i1^2*k2*i3*l5 + i2*k2*i3*l5 + j2*k2*i3*l5 +
	2*i1^2*l2*i3*l5 + 2*i2*l2*i3*l5 + 2*j2*l2*i3*l5 + 2*l2^2*i3*l5 + i1*i3^2*l5 +
	2*i1^4*j3*l5 + 2*i2^2*j3*l5 + 2*i1^2*j2*j3*l5 + i2*k2*j3*l5 + j2*k2*j3*l5 +
	k2^2*j3*l5 + 2*k2*l2*j3*l5 + i1^4*k3*l5 + 2*i1^2*i2*k3*l5 + i2^2*k3*l5 +
	2*j2^2*k3*l5 + i2*l2*k3*l5 + l2^2*k3*l5 + i1*j3*k3*l5 + i1^4*l3*l5 +
	2*i2^2*l3*l5 + j2^2*l3*l5 + 2*j2*k2*l3*l5 + 2*k2^2*l3*l5 + 2*i2*l2*l3*l5 +
	j2*l2*l3*l5 + k2*l2*l3*l5 + l2^2*l3*l5 + i1*i3*l3*l5 + 2*i1^3*k4*l5 +
	i1*i2*k4*l5 + 2*i1*j2*k4*l5 + i1*k2*k4*l5 + i1*l2*k4*l5 + i3*k4*l5 + k3*k4*l5 +
	i1^3*m4*l5 + 2*i1*i2*m4*l5 + i1*j2*m4*l5 + 2*i1*k2*m4*l5 + i3*m4*l5 +
	2*i1^2*l5^2 + i2*l5^2 + j2*l5^2 + k2*l5^2 + 2*i1^6*i6 + i1^2*i2*j2*i6 +
	2*i2*j2^2*i6 + j2^3*i6 + i2^2*k2*i6 + i2*j2*k2*i6 + 2*i2*k2^2*i6 + k2^3*i6 +
	i1^4*l2*i6 + 2*i1^2*i2*l2*i6 + 2*i2^2*l2*i6 + i1^2*j2*l2*i6 + 2*i2*j2*l2*i6 +
	j2^2*l2*i6 + i1^2*k2*l2*i6 + i2*k2*l2*i6 + 2*j2*k2*l2*i6 + k2^2*l2*i6 +
	2*i1^2*l2^2*i6 + i2*l2^2*i6 + 2*k2*l2^2*i6 + i1*i2*j3*i6 + 2*i1*j2*j3*i6 +
	2*i1*i2*k3*i6 + 2*i1*l2*k3*i6 + 2*i1^3*l3*i6 + i1*j2*l3*i6 + i1*k2*l3*i6 +
	j3*l3*i6 + i1^2*l4*i6 + i2*l4*i6 + 2*j2*l4*i6 + 2*k2*l4*i6 + l2*l4*i6 + i6^2 +
	2*i1^5*i7 + i1^3*i2*i7 + 2*i1*i2^2*i7 + 2*i1^3*j2*i7 + 2*i1*i2*j2*i7 +
	2*i1*j2^2*i7 + i1^3*k2*i7 + 2*i1*i2*k2*i7 + i1*j2*k2*i7 + i1*k2^2*i7 +
	i1^3*l2*i7 + 2*i1*i2*l2*i7 + 2*i1*k2*l2*i7 + i1*l2^2*i7 + i1^2*i3*i7 + i2*i3*i7
	+ j2*i3*i7 + 2*k2*i3*i7 + i1^2*j3*i7 + k2*j3*i7 + 2*l2*j3*i7 + i1^2*k3*i7 +
	2*j2*k3*i7 + 2*k2*k3*i7 + 2*j2*l3*i7 + k2*l3*i7 + 2*l2*l3*i7 + i1*j4*i7 +
	i1*k4*i7 + 2*i1*l4*i7;
        Append(~JI, J12); Append(~Wght, 12);
    end if;

    return JI, Wght;

end function;

function ShiodaAlgebraicInvariantsChar3(PrimaryInvariants, ratsolve)

    FF := Universe(PrimaryInvariants);

    P4 := PolynomialRing(FF, 4);
    J3 := P4.1; J6 := P4.2; J8 := P4.3; J10 := P4.4;

    if ratsolve eq false or not IsFinite(FF) then
	g := 1; LG := [ FF!1 ];
    else
	Support := [i : i in [1..#PrimaryInvariants] | PrimaryInvariants[i] ne 0];
	if #Support eq 0 then
	    g := 1;
	else
	    g := Gcd([[2, 4, 5, 7, 9, 12][i] : i in Support]);
	end if;
	if g ne 1 then
	    LG := PowerRepresentativesInFiniteFields(FF, g);
	else
	    LG := [ FF!1 ];
	end if;
    end if;

    JIs := [];
    for L in LG do

	J2, J4, J5, J7, J9, J12 := Explode([L^([2, 4, 5, 7, 9, 12][i] div g)*PrimaryInvariants[i] : i in [1..#PrimaryInvariants]]);

	RES := [];

	// deg. 12
	Append(~RES,
	    J2^6 + 2*J2^3*J3^2 + J3^4 + J2^2*J4^2 + J2^2*J3*J5 + J3*J4*J5 + 2*J2*J5^2 + J3^2*J6 + J6^2 + 2*J2*J3*J7 + 2*J5*J7 + J2^2*J8 + J4*J8 + J2*J10);


	// deg. 16
	Append(~RES,
	    J2^2*J3^4 + 2*J2^3*J3^2*J4 + 2*J3^4*J4 + 2*J2^4*J4^2 + J2*J3^2*J4^2 + 2*J2^2*J4^3 + J4^4 + J2*J3^3*J5 +     J2^3*J5^2 + 2*J2*J4*J5^2 + J2^5*J6 + 2*J2^3*J4*J6 + J3^2*J4*J6 + J2*J3*J5*J6 + J5^2*J6 + J4*J6^2 +     2*J2^3*J3*J7 + J3^3*J7 + 2*J2*J3*J4*J7 + J2^2*J5*J7 + 2*J3*J6*J7 + J2^4*J8 + 2*J2*J3^2*J8 + J2^2*J4*J8    + J4^2*J8 + 2*J3*J5*J8 + J2*J6*J8 + 2*J2^2*J3*J9 + J2^3*J10 + 2*J3^2*J10 + J6*J10 + 2*J2^2*J12 +     J4*J12);

	// deg. 17
	Append(~RES,
	    2*J2^4*J3^3 + 2*J2^2*J3^3*J4 + J2^3*J3*J4^2 + 2*J3^4*J5 + 2*J2^4*J4*J5 + 2*J2*J3^2*J4*J5 + J2^2*J3*J5^2 +     2*J3*J4*J5^2 + J2*J5^3 + J2^4*J3*J6 + J2^3*J5*J6 + J3^2*J5*J6 + J2*J4*J5*J6 + 2*J2*J3*J6^2 + J2^5*J7 +    2*J2^2*J3^2*J7 + 2*J2^3*J4*J7 + 2*J3^2*J4*J7 + 2*J2*J4^2*J7 + 2*J2*J3*J5*J7 + J5^2*J7 + 2*J4*J6*J7 +     2*J3*J7^2 + J2^3*J3*J8 + J3^3*J8 + J2*J3*J4*J8 + 2*J2^2*J5*J8 + 2*J4*J5*J8 + 2*J3*J6*J8 + J2*J7*J8 +     J2^2*J4*J9 + 2*J4^2*J9 + J2^2*J3*J10 + J3*J4*J10 + J2*J5*J10 + J7*J10 + 2*J2*J3*J12);

	// deg. 18
	Append(~RES,
	    J2^9 + J2^3*J3^4 + 2*J3^6 + J2^4*J3^2*J4 + J2*J3^4*J4 + 2*J3^2*J4^3 + J2^2*J3^3*J5 + J2^3*J3*J4*J5 +     J3^3*J4*J5 + J2*J3*J4^2*J5 + 2*J2^4*J5^2 + J2*J3^2*J5^2 + 2*J2^3*J3^2*J6 + J3^4*J6 + J2^4*J4*J6 +     2*J2*J3^2*J4*J6 + 2*J2^2*J4^2*J6 + J4^3*J6 + 2*J2^2*J3*J5*J6 + 2*J3*J4*J5*J6 + 2*J2*J5^2*J6 +     J2*J4*J6^2 + 2*J2^2*J3*J4*J7 + J3^2*J5*J7 + J2*J4*J5*J7 + J2*J3*J6*J7 + 2*J5*J6*J7 + 2*J2^2*J7^2 +     2*J2^5*J8 + 2*J2^2*J3^2*J8 + J2^3*J4*J8 + J2^2*J6*J8 + J3*J7*J8 + J2*J8^2 + J2^3*J3*J9 + 2*J2*J3*J4*J9    + J2^2*J5*J9 + J4*J5*J9 + 2*J2*J7*J9 + J2^4*J10 + J2*J3^2*J10 + J2^2*J4*J10 + J3*J5*J10 + 2*J8*J10 +     J2^3*J12 + 2*J3^2*J12 + J2*J4*J12 + J6*J12);

	// deg. 19
	Append(~RES,
	    J2^8*J3 + 2*J2^2*J3^5 + J2^3*J3^3*J4 + J3*J4^4 + 2*J2*J3^4*J5 + J2^5*J4*J5 + 2*J2^3*J4^2*J5 + J3^2*J4^2*J5    + 2*J2*J4^3*J5 + J2*J3*J4*J5^2 + J2^2*J5^3 + J2^3*J3*J4*J6 + 2*J3^3*J4*J6 + J2*J3*J4^2*J6 + J2^4*J5*J6    + 2*J2*J3^2*J5*J6 + 2*J2^2*J4*J5*J6 + J2^2*J3*J6^2 + 2*J3*J4*J6^2 + 2*J2*J5*J6^2 + J2^3*J3^2*J7 +     2*J3^4*J7 + 2*J2^4*J4*J7 + 2*J2*J3^2*J4*J7 + 2*J4^3*J7 + J2^2*J3*J5*J7 + J3*J4*J5*J7 + 2*J2*J5^2*J7 +     J5*J7^2 + J2*J3^3*J8 + J2^2*J3*J4*J8 + 2*J3*J4^2*J8 + J2^3*J5*J8 + 2*J2*J4*J5*J8 + J2*J3*J6*J8 +     2*J5*J6*J8 + J2^2*J7*J8 + J4*J7*J8 + J3*J8^2 + J2^2*J3^2*J9 + J3^2*J4*J9 + J2*J4^2*J9 + J2*J3*J5*J9 +     2*J4*J6*J9 + 2*J2^3*J3*J10 + J3^3*J10 + J2^2*J5*J10 + 2*J3*J6*J10 + J2*J7*J10 + J2^2*J3*J12 +     J3*J4*J12 + 2*J2*J5*J12 + 2*J7*J12);

	// deg. 20
	Append(~RES,
	    2*J2^4*J3^4 + J2*J3^6 + J2^8*J4 + 2*J2^3*J3^2*J4^2 + 2*J2*J3^2*J4^3 + J4^5 + J2^3*J3^3*J5 + J3^5*J5 +     J2^2*J3*J4^2*J5 + J2*J4^2*J5^2 + 2*J2*J3*J5^3 + 2*J2^3*J4^2*J6 + J3^2*J4^2*J6 + J2*J4^3*J6 +     J2^3*J3*J5*J6 + 2*J2*J3*J4*J5*J6 + J2^2*J5^2*J6 + J4*J5^2*J6 + 2*J2^4*J6^2 + J2*J3^2*J6^2 + J4^2*J6^2     + J3*J5*J6^2 + J2*J6^3 + 2*J2^2*J3^3*J7 + J3^3*J4*J7 + J2*J3*J4^2*J7 + 2*J2*J3^2*J5*J7 + J4^2*J5*J7 +     2*J3*J5^2*J7 + J2^2*J3*J6*J7 + J2*J5*J6*J7 + J3^2*J7^2 + 2*J2*J4*J7^2 + J2^3*J3^2*J8 + 2*J2^4*J4*J8 +     J2*J3^2*J4*J8 + J2^2*J4^2*J8 + J3*J4*J5*J8 + 2*J2*J5^2*J8 + 2*J2^3*J6*J8 + J2*J3*J7*J8 + J2^2*J8^2 +     2*J4*J8^2 + J2^4*J3*J9 + 2*J2*J3^3*J9 + 2*J3*J4^2*J9 + 2*J2*J4*J5*J9 + J2*J3*J6*J9 + 2*J4*J7*J9 +     J2^2*J3^2*J10 + 2*J2^3*J4*J10 + 2*J3^2*J4*J10 + J2*J4^2*J10 + 2*J2*J3*J5*J10 + J5^2*J10 +     2*J2^2*J6*J10 + 2*J4*J6*J10 + J3*J7*J10 + 2*J2*J8*J10 + J10^2 + J2^4*J12 + 2*J2*J3^2*J12 +     2*J2^2*J4*J12 + 2*J4^2*J12 + 2*J3*J5*J12 + J2*J6*J12);

	// deg. 22
	Append(~RES,
	    J2^11 + J2^2*J3^6 + 2*J3^6*J4 + 2*J2^4*J3^2*J4^2 + J2*J3^4*J4^2 + 2*J2^2*J3^2*J4^3 + 2*J3^2*J4^4 +     J3^3*J4^2*J5 + J2*J3*J4^3*J5 + J3^4*J5^2 + J2^2*J4^2*J5^2 + J3*J4*J5^3 + 2*J2*J5^4 + J2^2*J3^4*J6 +     2*J3^4*J4*J6 + J2^4*J4^2*J6 + J2*J3^2*J4^2*J6 + J2^2*J4^3*J6 + J4^4*J6 + J2^4*J3*J5*J6 + J3*J4^2*J5*J6    + 2*J3^2*J5^2*J6 + J2*J4*J5^2*J6 + 2*J2^2*J3^2*J6^2 + 2*J3^2*J4*J6^2 + 2*J2*J4^2*J6^2 + J2*J3*J5*J6^2     + 2*J5^2*J6^2 + J2^3*J3^3*J7 + 2*J3^5*J7 + 2*J2^4*J3*J4*J7 + J2*J3^3*J4*J7 + J2^2*J3*J4^2*J7 +     2*J3*J4^3*J7 + 2*J2^3*J4*J5*J7 + 2*J2*J4^2*J5*J7 + J2*J3*J5^2*J7 + 2*J5^3*J7 + J3^3*J6*J7 +     J2*J3*J4*J6*J7 + 2*J2^2*J5*J6*J7 + 2*J3*J6^2*J7 + 2*J2^4*J7^2 + J2*J3^2*J7^2 + 2*J2^2*J4*J7^2 +     J3*J5*J7^2 + J2*J6*J7^2 + 2*J2^3*J4^2*J8 + J3^2*J4^2*J8 + 2*J2^3*J3*J5*J8 + J3^3*J5*J8 +     2*J2*J3*J4*J5*J8 + J2^2*J5^2*J8 + J4*J5^2*J8 + 2*J2^4*J6*J8 + J2*J3^2*J6*J8 + J2^2*J4*J6*J8 +     J4^2*J6*J8 + J3*J5*J6*J8 + 2*J2*J6^2*J8 + J3*J4*J7*J8 + 2*J3^2*J8^2 + J2*J4*J8^2 + J6*J8^2 +     J2^2*J3^3*J9 + 2*J2^3*J3*J4*J9 + 2*J3^3*J4*J9 + J2*J3*J4^2*J9 + J2^4*J5*J9 + 2*J2^2*J4*J5*J9 +     2*J3*J5^2*J9 + 2*J2^2*J3*J6*J9 + J3*J4*J6*J9 + 2*J2*J5*J6*J9 + 2*J2^3*J7*J9 + 2*J3^2*J7*J9 +     2*J2*J4*J7*J9 + J6*J7*J9 + J2*J3*J8*J9 + J4^3*J10 + 2*J2^2*J3*J5*J10 + J2*J5^2*J10 + 2*J2*J4*J6*J10 +     J6^2*J10 + 2*J2^2*J8*J10 + J4*J8*J10 + J2*J10^2 + J2^5*J12 + J2^2*J3^2*J12 + J2^3*J4*J12 + J2*J4^2*J12    + 2*J3*J7*J12 + 2*J2*J8*J12 + J10*J12);

	// deg. 23
	Append(~RES,
	    J2*J3^7 + J2^2*J3^5*J4 + J2^3*J3^3*J4^2 + 2*J2*J3^3*J4^3 + 2*J2^2*J3*J4^4 + J2^9*J5 + 2*J2^3*J3^4*J5 +     J2^3*J4^3*J5 + J3^2*J4^3*J5 + J2*J4^4*J5 + J2^2*J3^3*J5^2 + 2*J2^3*J3*J4*J5^2 + J3^3*J4*J5^2 +     2*J2^4*J5^3 + 2*J2^2*J4*J5^3 + J2*J3^5*J6 + J2^2*J3^3*J4*J6 + J2^3*J3*J4^2*J6 + J2*J3*J4^3*J6 +     2*J2^3*J3^2*J5*J6 + J3^4*J5*J6 + J2^4*J4*J5*J6 + 2*J2*J3^2*J4*J5*J6 + 2*J2^2*J4^2*J5*J6 +     J3*J4*J5^2*J6 + J2^4*J3*J6^2 + 2*J2*J3^3*J6^2 + J2^2*J3*J4*J6^2 + 2*J2^3*J5*J6^2 + 2*J3^2*J5*J6^2 +     J5*J6^3 + 2*J2^2*J3^4*J7 + J2^3*J3^2*J4*J7 + J3^4*J4*J7 + J2^4*J4^2*J7 + J2*J3^2*J4^2*J7 + J4^4*J7 +     J2^4*J3*J5*J7 + 2*J2*J3^3*J5*J7 + J2^2*J3*J4*J5*J7 + J3*J4^2*J5*J7 + J2^3*J5^2*J7 + 2*J2*J4*J5^2*J7 +     J2^2*J3^2*J6*J7 + 2*J2^3*J4*J6*J7 + J3^2*J4*J6*J7 + 2*J2*J4^2*J6*J7 + J2*J3*J4*J7^2 + 2*J3*J6*J7^2 +     J2*J7^3 + J3^5*J8 + J2^4*J3*J4*J8 + J2*J3^3*J4*J8 + J2^2*J3*J4^2*J8 + J3*J4^3*J8 + J2^2*J3^2*J5*J8 +     J2^3*J4*J5*J8 + 2*J3^2*J4*J5*J8 + J2*J3*J5^2*J8 + 2*J3^3*J6*J8 + J2^2*J5*J6*J8 + J4*J5*J6*J8 +     J3*J6^2*J8 + 2*J2*J3^2*J7*J8 + J2^2*J4*J7*J8 + J4^2*J7*J8 + J2*J6*J7*J8 + J3*J4*J8^2 + 2*J2*J5*J8^2 +     J7*J8^2 + 2*J2^4*J3^2*J9 + 2*J2*J3^4*J9 + J2^2*J3^2*J4*J9 + J3^2*J4^2*J9 + 2*J2*J4^3*J9 + J3^3*J5*J9 +    2*J2^2*J5^2*J9 + J2*J3^2*J6*J9 + J2^2*J4*J6*J9 + 2*J3*J5*J6*J9 + 2*J3*J4*J7*J9 + J7^2*J9 + J2*J4*J8*J9    + 2*J2^3*J3*J4*J10 + 2*J3^3*J4*J10 + 2*J2*J3*J4^2*J10 + J2^4*J5*J10 + J2*J3^2*J5*J10 +     2*J2^2*J4*J5*J10 + 2*J3*J5^2*J10 + 2*J2*J5*J6*J10 + 2*J2^3*J7*J10 + 2*J3^2*J7*J10 + J2*J4*J7*J10 +     2*J6*J7*J10 + J2*J3*J8*J10 + 2*J5*J8*J10 + 2*J4*J9*J10 + J3*J10^2 + J2^4*J3*J12 + J2*J3^3*J12 +     2*J2^2*J3*J4*J12 + J3^2*J5*J12 + J3*J8*J12);

	// deg. 24
	Append(~RES,
	    J2^12 + 2*J2^3*J3^6 + J3^8 + J2*J3^6*J4 + 2*J2^3*J3^2*J4^3 + J3^4*J4^3 + 2*J2^4*J4^4 + 2*J4^6 +     2*J2*J3^3*J4^2*J5 + J2^2*J3*J4^3*J5 + J2*J3^4*J5^2 + J2^2*J3^2*J4*J5^2 + J2^3*J4^2*J5^2 +     2*J3^2*J4^2*J5^2 + J2^3*J3*J5^3 + J2*J3*J4*J5^3 + 2*J2^2*J5^4 + 2*J2^3*J3^4*J6 + 2*J2*J3^4*J4*J6 +     J2^2*J3^2*J4^2*J6 + 2*J2^3*J4^3*J6 + J3^2*J4^3*J6 + 2*J2^3*J3*J4*J5*J6 + J3^3*J4*J5*J6 +     J2*J3*J4^2*J5*J6 + 2*J2*J3^2*J5^2*J6 + 2*J2^2*J4*J5^2*J6 + J4^2*J5^2*J6 + J2^3*J3^2*J6^2 +     J2^4*J4*J6^2 + J2*J3^2*J4*J6^2 + J2^2*J3*J5*J6^2 + 2*J3*J4*J5*J6^2 + J2*J5^2*J6^2 + 2*J3^2*J6^3 + J6^4    + J2^3*J3*J4^2*J7 + 2*J3^3*J4^2*J7 + 2*J2*J3*J4^3*J7 + J2^3*J3^2*J5*J7 + 2*J2^4*J4*J5*J7 +     J2*J3^2*J4*J5*J7 + 2*J2^2*J4^2*J5*J7 + J2^2*J3*J5^2*J7 + 2*J2*J5^3*J7 + 2*J2^4*J3*J6*J7 +     J2*J3^3*J6*J7 + J2^2*J3*J4*J6*J7 + 2*J3*J4^2*J6*J7 + 2*J2^3*J5*J6*J7 + 2*J2*J4*J5*J6*J7 +     2*J2*J3*J6^2*J7 + 2*J5*J6^2*J7 + 2*J2^2*J3^2*J7^2 + J2^3*J4*J7^2 + J3^2*J4*J7^2 + 2*J2*J4^2*J7^2 +     J5^2*J7^2 + 2*J2^2*J6*J7^2 + J4*J6*J7^2 + J3*J7^3 + 2*J2^2*J3^4*J8 + 2*J2^3*J3^2*J4*J8 + 2*J3^4*J4*J8     + J2*J3^2*J4^2*J8 + 2*J2^2*J4^3*J8 + 2*J4^4*J8 + 2*J2*J3^3*J5*J8 + 2*J3*J4^2*J5*J8 + J2^3*J5^2*J8 +     2*J3^2*J5^2*J8 + J2*J4*J5^2*J8 + J2^2*J3^2*J6*J8 + J3^2*J4*J6*J8 + J2*J4^2*J6*J8 + J2*J3*J5*J6*J8 +     J5^2*J6*J8 + 2*J2^2*J6^2*J8 + 2*J2^3*J3*J7*J8 + J3^3*J7*J8 + 2*J2*J3*J4*J7*J8 + J2^2*J5*J7*J8 +     2*J4*J5*J7*J8 + 2*J3*J6*J7*J8 + 2*J2^4*J8^2 + 2*J2*J3^2*J8^2 + 2*J2^2*J4*J8^2 + J4^2*J8^2 + J2*J6*J8^2    + J8^3 + J2^3*J3^3*J9 + J3^5*J9 + 2*J2*J3^3*J4*J9 + 2*J2^2*J3*J4^2*J9 + 2*J3*J4^3*J9 +     2*J2^2*J3^2*J5*J9 + 2*J5^3*J9 + J2^3*J3*J6*J9 + J3^3*J6*J9 + 2*J2^2*J5*J6*J9 + J3*J6^2*J9 + J2^4*J7*J9    + 2*J2*J3^2*J7*J9 + 2*J4^2*J7*J9 + 2*J3*J5*J7*J9 + 2*J2*J6*J7*J9 + 2*J2^2*J3*J8*J9 + 2*J3*J4*J8*J9 +     2*J2*J5*J8*J9 + J7*J8*J9 + J2*J4*J9^2 + 2*J2*J3^4*J10 + J2^2*J3^2*J4*J10 + J2^3*J4^2*J10 +     J3^2*J4^2*J10 + J2*J4^3*J10 + 2*J3^3*J5*J10 + J2*J3*J4*J5*J10 + 2*J4*J5^2*J10 + J2^4*J6*J10 +     J3*J5*J6*J10 + J2*J6^2*J10 + 2*J7^2*J10 + J3^2*J8*J10 + 2*J2*J4*J8*J10 + J2*J3*J9*J10 + 2*J5*J9*J10 +     2*J4*J10^2 + J2^3*J3^2*J12 + J3^4*J12 + 2*J2^4*J4*J12 + 2*J2*J3^2*J4*J12 + 2*J4^3*J12 + J2*J5^2*J12 +     2*J2^3*J6*J12 + J3^2*J6*J12 + 2*J2*J4*J6*J12 + 2*J2*J3*J7*J12 + 2*J2*J10*J12 + J12^2);

	if ratsolve eq false then return RES; end if;

	V := Variety(ideal<P4 | RES>);
	for v in V do
	    NJI := [J2, FF!v[1], J4, J5, FF!v[2], J7, FF!v[3], J9, FF!v[4], J12];
	    NJI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10, 12], NJI);;
	    JIs := ShiodaInvariantsAppend(JIs, NJI);
	end for;
    end for;

    return JIs;

end function;
