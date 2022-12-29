//freeze;

/***
 *  Mini Toolboox for descending a hyperelliptic curve onto twists defined
 *  over its field of moduli (finite fields)
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
 *  Copyright 2011, R. Lercier & C. Ritzenthaler & J. Sijsling
 */

function MConj(M, sigma)
    return Matrix([[sigma(M[1,1]), sigma(M[1,2])],
	[sigma(M[2,1]), sigma(M[2,2])]]);
end function;

function MNorm(M, sigma, ord_sigma)
    Mr := M;
    for i:=1 to ord_sigma-1 do
	Mr := MConj(Mr, sigma) * M;
    end for;
    return Mr;
end function;

function MActOnC(f, degf, A)
    _X := Parent(f).1;
    fd  := Parent(f)!(Evaluate(f, (A[1,1]*_X + A[1,2]) / (A[2,1]*_X + A[2,2])) * (A[2,1]*_X + A[2,2])^degf);
    return fd;
end function;


function Glasby(_M, sigma, Fq)

   Fqe := CoefficientRing(_M); w := Fqe.1;
   e := Degree(Fqe, Fq);

   /* Computing M s.t the cocycle relation is true,
      that is Norm(M) eq 1 */
   R := MNorm(_M, sigma, e);
   if not IsScalar(R) or
      not ((R[1, 1] in Fq) and (R[2, 2] in Fq) and (R[1, 1] eq R[2, 2])) then
       "HUM, non scalar endomorphism found after conjugation, I give up...";
       return Parent(_M)!0;
   end if;

   ret, t := NormEquation(Fqe, Fq!R[1,1]);

   if ret ne true then
       "HUM, no solution to the norm equation, I give up...";
       return Parent(_M)!0;
   end if;

   M := (_M/t);

   /* Finding X */
   notinvertible:=true;
   while notinvertible do
       X := Matrix([[Random(Fqe), Random(Fqe)],[Random(Fqe), Random(Fqe)]]);
       Xb:=X;
       for i := 2 to e do
	   Xb := MConj(Xb, sigma) * M;
	   X := X + Xb;
       end for;
       if IsInvertible(X) then
	   notinvertible:=false;
       end if;
   end while;

//   M - MConj(X, sigma)^(-1) * X;

   return X;
end function;
