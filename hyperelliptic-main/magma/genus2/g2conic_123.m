//freeze;

/***
 *  Equations in genus 2 of the conic and the cubic for the covariants [1, 2, 3].
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

function Genus2ConicAndCubic123(JI : models := true)

    FF := Parent((Universe(JI)!1)/1); /* We want a field */

    J2,J4,J6,_,J10 := Explode(JI);

    P3 := PolynomialRing(FF, 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

    /* Conic [1, 2, 3] */
    R :=
        J2^6*J6^3 - 2*J2^5*J4^2*J6^2 + J2^4*J4^4*J6 - 72*J10*J2^5*J4*J6 + 8*J10*J2^4*J4^3
        - 72*J2^4*J4*J6^3 + 136*J2^3*J4^3*J6^2 - 64*J2^2*J4^5*J6 - 432*J10^2*J2^5
        - 48*J10*J2^4*J6^2 + 4816*J10*J2^3*J4^2*J6 - 512*J10*J2^2*J4^4 + 216*J2^3*J6^4
        + 1080*J2^2*J4^2*J6^3 - 2304*J2*J4^4*J6^2 + 1024*J4^6*J6 + 28800*J10^2*J2^3*J4
        - 12960*J10*J2^2*J4*J6^2 - 84480*J10*J2*J4^3*J6 + 8192*J10*J4^5 - 7776*J2*J4*J6^4
        + 6912*J4^3*J6^3 - 96000*J10^2*J2^2*J6 - 512000*J10^2*J2*J4^2 - 129600*J10*J2*J6^3
        + 691200*J10*J4^2*J6^2 + 11664*J6^5 + 11520000*J10^2*J4*J6 + 51200000*J10^3;
    if R eq 0 then
        return R, R, R;
    end if;

    if not models then return R, R, R; end if;

    C :=
        (-3600*J6-160*J4*J2+3*J2^3)*x1^2+
        (6000*J6*J2+6400*J4^2-360*J4*J2^2+6*J2^4)*x1*x2+
        (-1600000*J10+(-96000*J4-800*J2^2)*J6-400*J4*J2^3+6400*J4^2*J2+6*J2^5)*x1*x3+
        (-800000*J10+(-48000*J4-400*J2^2)*J6-200*J4*J2^3+3200*J4^2*J2+3*J2^5)*x2^2+
        (360000*J6^2+(-8000*J4*J2+2400*J2^3)*J6+10000*J4^2*J2^2-
        440*J4*J2^4+6*J2^6-64000*J4^3)*x2*x3+
        ((-600000*J2^2+8000000*J4)*J10-150000*J6^2*J2+(300*J2^4-38000*J4*J2^2+320000*J4^2)*J6+
        3*J2^7-240*J4*J2^5+6100*J4^2*J2^3-48000*J4^3*J2)*x3^2;

    M :=
        (-3200000*J10+(-288000*J4+600*J2^2)*J6-100*J4*J2^3+3200*J4^2*J2+J2^5)*x1^3+
        (4000000*J10*J2+2160000*J6^2+(-1600*J2^3+432000*J4*J2)*J6-128000*J4^3-
        320*J4*J2^4+3*J2^6+10400*J4^2*J2^2)*x1^2*x2+
        ((32000000*J4-2400000*J2^2)*J10-160000*J4^3*J2+13000*J4^2*J2^3-2700000*J6^2*J2-
        180000*J6*J4*J2^2-340*J4*J2^5+3*J2^7)*x1^2*x3+
        ((32000000*J4-2400000*J2^2)*J10-160000*J4^3*J2+13000*J4^2*J2^3-2700000*J6^2*J2-
        180000*J6*J4*J2^2-340*J4*J2^5+3*J2^7)*x1*x2^2+
        ((16000000*J4*J2+1200000*J2^3+960000000*J6)*J10+(43200000*J4+3060000*J2^2)*J6^2+
        (-1800*J2^5+260000*J4*J2^3-960000*J4^2*J2)*J6+2560000*J4^4-496000*J4^3*J2^2+
        29800*J4^2*J2^4+6*J2^8-720*J4*J2^6)*x1*x2*x3+
        ((-800000*J2^4-200000000*J6*J2-320000000*J4^2+28000000*J4*J2^2)*J10-108000000*J6^3+
        (-5400000*J4*J2-1405000*J2^3)*J6^2+(-880000*J4^2*J2^2-3000*J4*J2^4-550*J2^6+
        6400000*J4^3)*J6+17350*J4^2*J2^5-380*J4*J2^7+3*J2^9+
        2240000*J4^4*J2-334000*J4^3*J2^3)*x1*x3^2+
        ((-8000000*J4*J2+400000*J2^3-80000000*J6)*J10+(-7200000*J4+1140000*J2^2)*J6^2+
        (2200*J2^5-100000*J4*J2^3+1760000*J4^2*J2)*J6+1280000*J4^4-136000*J4^3*J2^2+
        5800*J4^2*J2^4+J2^8-120*J4*J2^6)*x2^3+
        ((-1400000*J2^4-800000000*J6*J2-960000000*J4^2+64000000*J4*J2^2)*J10+54000000*J6^3+
        (-37800000*J4*J2-760000*J2^3)*J6^2+(7700000*J4^2*J2^2-318000*J4*J2^4+3200*J2^6-
        60800000*J4^3)*J6+18600*J4^2*J2^5-380*J4*J2^7+3*J2^9+3520000*J4^4*J2-
        414000*J4^3*J2^3)*x3*x2^2+
        (160000000000*J10^2+((20000000000*J4+100000000*J2^2)*J6+70000000*J4*J2^3-
        1200000000*J4^2*J2-900000*J2^5)*J10+(648000000*J4^2-7200000*J4*J2^2+
        895000*J2^4)*J6^2+(6480000*J4^2*J2^3-129000*J4*J2^5+1050*J2^7-94400000*J4^3*J2)*J6-
        12800000*J4^5+4880000*J4^4*J2^2-480000*J4^3*J2^4+20350*J4^2*J2^6-
        400*J4*J2^8+3*J2^10)*x3^2*x2+
        ((3200000000*J4^3-20000000000*J6^2+24000000*J4*J2^4-350000*J2^6-100000000*J6*J2^3-
        520000000*J4^2*J2^2)*J10+(19500000*J2^2-1260000000*J4)*J6^3+(-80000*J2^5-
        10250000*J4*J2^3+122000000*J4^2*J2)*J6^2+(-29000000*J4^3*J2^2+1325000*J4^2*J2^4+
        50*J2^8+224000000*J4^4-23500*J4*J2^6)*J6+J2^11+2300000*J4^4*J2^3-
        193500*J4^3*J2^5+7550*J4^2*J2^7-9600000*J4^5*J2-140*J4*J2^9)*x3^3;

    return R, C, M;

end function;
