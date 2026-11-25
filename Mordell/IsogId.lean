import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Defs

set_option linter.unusedVariables false

namespace Mordell.IsogId

lemma idSlopeChord {x1 x2 x3 l n u c d A B D : ℚ} (hc : c = l^2 - x1 - x2 - x3) (hd : d = x1*x2 + x1*x3 + x2*x3 + 2*l*n) (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (hR : n^2 = x1*x2*x3) (hu : u ≠ 0) (hn : n ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx3 : x3 ≠ 0) (hDdef : D = 2*l*x1*x2+n*x1+n*x2) (hD : D ≠ 0) :
    (-(2*l^2*n*x1*x2 + 2*l*x1^2*x2^2 + 3*l*x1^2*x2*x3 + 3*l*x1*x2^2*x3 + n*x1^2*x2 + n*x1^2*x3 + n*x1*x2^2 + 2*n*x1*x2*x3 + n*x2^2*x3))/(-n*u*D) * ((l*x1+n)^2/(u^2*x1^2) - (l*x2+n)^2/(u^2*x2^2)) = (l*x1+n)*(d-x1^2)/(u^3*x1^2) - (l*x2+n)*(d-x2^2)/(u^3*x2^2) := by
  subst hc hd hA hB
  field_simp
  linear_combination (4*l^2*n*x1^3*x2 - 4*l^2*n*x1*x2^3 + 2*l*n^2*x1^3 + 2*l*n^2*x1^2*x2 - 2*l*n^2*x1*x2^2 - 2*l*n^2*x2^3) * hR + (2*l^2*n^2*x1^2*x2 - 2*l^2*n^2*x1*x2^2 + 2*l*n^3*x1^2 - 2*l*n^3*x2^2 + 2*l*n*x1^3*x2^2 + l*n*x1^3*x2*x3 - 2*l*n*x1^2*x2^3 - l*n*x1*x2^3*x3 + n^2*x1^3*x2 + n^2*x1^3*x3 + n^2*x1^2*x2*x3 - n^2*x1*x2^3 - n^2*x1*x2^2*x3 - n^2*x2^3*x3) * hDdef

lemma idAddX {x1 x2 x3 l n u c d A B D : ℚ} (hc : c = l^2 - x1 - x2 - x3) (hd : d = x1*x2 + x1*x3 + x2*x3 + 2*l*n) (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (hR : n^2 = x1*x2*x3) (hu : u ≠ 0) (hn : n ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx3 : x3 ≠ 0) (hDdef : D = 2*l*x1*x2+n*x1+n*x2) (hD : D ≠ 0) :
    (l*x3+n)^2/(u^2*x3^2) = ((-(2*l^2*n*x1*x2 + 2*l*x1^2*x2^2 + 3*l*x1^2*x2*x3 + 3*l*x1*x2^2*x3 + n*x1^2*x2 + n*x1^2*x3 + n*x1*x2^2 + 2*n*x1*x2*x3 + n*x2^2*x3))/(-n*u*D))^2 - A - (l*x1+n)^2/(u^2*x1^2) - (l*x2+n)^2/(u^2*x2^2) := by
  subst hc hd hA hB
  field_simp
  linear_combination (8*l^3*n*x1^4*x2^4*x3 + 12*l^3*n*x1^4*x2^3*x3^2 + 12*l^3*n*x1^3*x2^4*x3^2 + 4*l^2*n^2*x1^4*x2^4 + 8*l^2*n^2*x1^4*x2^3*x3 + 13*l^2*n^2*x1^4*x2^2*x3^2 + 8*l^2*n^2*x1^3*x2^4*x3 + 18*l^2*n^2*x1^3*x2^3*x3^2 + 13*l^2*n^2*x1^2*x2^4*x3^2 + 4*l^2*x1^5*x2^5*x3 + 12*l^2*x1^5*x2^4*x3^2 + 9*l^2*x1^5*x2^3*x3^3 + 12*l^2*x1^4*x2^5*x3^2 + 18*l^2*x1^4*x2^4*x3^3 + 9*l^2*x1^3*x2^5*x3^3 + 4*l*n^3*x1^4*x2^3 + 2*l*n^3*x1^4*x2^2*x3 + 6*l*n^3*x1^4*x2*x3^2 + 4*l*n^3*x1^3*x2^4 + 4*l*n^3*x1^3*x2^3*x3 + 10*l*n^3*x1^3*x2^2*x3^2 + 2*l*n^3*x1^2*x2^4*x3 + 10*l*n^3*x1^2*x2^3*x3^2 + 6*l*n^3*x1*x2^4*x3^2 + 4*l*n*x1^5*x2^4*x3 + 10*l*n*x1^5*x2^3*x3^2 + 6*l*n*x1^5*x2^2*x3^3 + 4*l*n*x1^4*x2^5*x3 + 20*l*n*x1^4*x2^4*x3^2 + 18*l*n*x1^4*x2^3*x3^3 + 10*l*n*x1^3*x2^5*x3^2 + 18*l*n*x1^3*x2^4*x3^3 + 6*l*n*x1^2*x2^5*x3^3 + n^4*x1^4*x2^2 + n^4*x1^4*x3^2 + 2*n^4*x1^3*x2^3 + 2*n^4*x1^3*x2*x3^2 + n^4*x1^2*x2^4 + 2*n^4*x1^2*x2^2*x3^2 + 2*n^4*x1*x2^3*x3^2 + n^4*x2^4*x3^2 + n^2*x1^5*x2^3*x3 + 2*n^2*x1^5*x2^2*x3^2 + n^2*x1^5*x2*x3^3 + 2*n^2*x1^4*x2^4*x3 + 6*n^2*x1^4*x2^3*x3^2 + 4*n^2*x1^4*x2^2*x3^3 + n^2*x1^3*x2^5*x3 + 6*n^2*x1^3*x2^4*x3^2 + 6*n^2*x1^3*x2^3*x3^3 + 2*n^2*x1^2*x2^5*x3^2 + 4*n^2*x1^2*x2^4*x3^3 + n^2*x1*x2^5*x3^3) * hR + (D*l^2*n^2*x1^2*x2^2*x3^2 + 2*D*l*n^3*x1^2*x2^2*x3 + 2*D*l*n^3*x1^2*x2*x3^2 + 2*D*l*n^3*x1*x2^2*x3^2 + D*n^4*x1^2*x2^2 + D*n^4*x1^2*x3^2 + D*n^4*x2^2*x3^2 + 2*D*n^2*x1^3*x2^2*x3^2 + 2*D*n^2*x1^2*x2^3*x3^2 + 2*D*n^2*x1^2*x2^2*x3^3 + 2*l^3*n^2*x1^3*x2^3*x3^2 + 4*l^2*n^3*x1^3*x2^3*x3 + 5*l^2*n^3*x1^3*x2^2*x3^2 + 5*l^2*n^3*x1^2*x2^3*x3^2 + 2*l*n^4*x1^3*x2^3 + 2*l*n^4*x1^3*x2^2*x3 + 4*l*n^4*x1^3*x2*x3^2 + 2*l*n^4*x1^2*x2^3*x3 + 4*l*n^4*x1^2*x2^2*x3^2 + 4*l*n^4*x1*x2^3*x3^2 + 4*l*n^2*x1^4*x2^3*x3^2 + 4*l*n^2*x1^3*x2^4*x3^2 + 4*l*n^2*x1^3*x2^3*x3^3 + n^5*x1^3*x2^2 + n^5*x1^3*x3^2 + n^5*x1^2*x2^3 + n^5*x1^2*x2*x3^2 + n^5*x1*x2^2*x3^2 + n^5*x2^3*x3^2 + 2*n^3*x1^4*x2^2*x3^2 + 4*n^3*x1^3*x2^3*x3^2 + 2*n^3*x1^3*x2^2*x3^3 + 2*n^3*x1^2*x2^4*x3^2 + 2*n^3*x1^2*x2^3*x3^3) * hDdef

lemma idAddY {x1 x2 x3 l n u c d A B D : ℚ} (hc : c = l^2 - x1 - x2 - x3) (hd : d = x1*x2 + x1*x3 + x2*x3 + 2*l*n) (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (hR : n^2 = x1*x2*x3) (hu : u ≠ 0) (hn : n ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx3 : x3 ≠ 0) (hDdef : D = 2*l*x1*x2+n*x1+n*x2) (hD : D ≠ 0) :
    (-(l*x3+n))*(d-x3^2)/(u^3*x3^2) = -(((-(2*l^2*n*x1*x2 + 2*l*x1^2*x2^2 + 3*l*x1^2*x2*x3 + 3*l*x1*x2^2*x3 + n*x1^2*x2 + n*x1^2*x3 + n*x1*x2^2 + 2*n*x1*x2*x3 + n*x2^2*x3))/(-n*u*D)) * ((l*x3+n)^2/(u^2*x3^2) - (l*x1+n)^2/(u^2*x1^2)) + (l*x1+n)*(d-x1^2)/(u^3*x1^2)) := by
  subst hc hd hA hB
  field_simp
  linear_combination (-2*l^2*n*x1^3*x2 - 2*l^2*n*x1^3*x3 - 2*l^2*n*x1^2*x2*x3 + 2*l^2*n*x1^2*x3^2 + 4*l^2*n*x1*x2*x3^2 - 2*l*n^2*x1^3 - 2*l*n^2*x1^2*x2 + 2*l*n^2*x1*x3^2 + 2*l*n^2*x2*x3^2) * hR + (-2*l^2*n^2*x1^2*x3 + 2*l^2*n^2*x1*x3^2 - 2*l*n^3*x1^2 + 2*l*n^3*x3^2 - l*n*x1^3*x2*x3 - 2*l*n*x1^3*x3^2 + 2*l*n*x1^2*x3^3 + l*n*x1*x2*x3^3 - n^2*x1^3*x2 - n^2*x1^3*x3 - n^2*x1^2*x2*x3 + n^2*x1*x2*x3^2 + n^2*x1*x3^3 + n^2*x2*x3^3) * hDdef

lemma idSlopeTan {x1 x2 x3 l n u c d A B D : ℚ} (hc : c = l^2 - x1 - x1 - x3) (hd : d = x1*x1 + x1*x3 + x1*x3 + 2*l*n) (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (hR : n^2 = x1*x1*x3) (hu : u ≠ 0) (hn : n ≠ 0) (hx1 : x1 ≠ 0) (hx3 : x3 ≠ 0) (hDdef : D = 2*l*x1*x1+n*x1+n*x1) (hD : D ≠ 0) :
    2 * ((l*x1+n)*(d-x1^2)/(u^3*x1^2)) * ((-(2*l^2*n*x1*x1 + 2*l*x1^2*x1^2 + 3*l*x1^2*x1*x3 + 3*l*x1*x1^2*x3 + n*x1^2*x1 + n*x1^2*x3 + n*x1*x1^2 + 2*n*x1*x1*x3 + n*x1^2*x3))/(-n*u*D)) = 3*((l*x1+n)^2/(u^2*x1^2))^2 + 2*A*((l*x1+n)^2/(u^2*x1^2)) + B := by
  subst hc hd hA hB
  field_simp
  linear_combination (-28*l^3*n*x1^4 - 52*l^2*n^2*x1^3 - 8*l^2*x1^6 - 24*l^2*x1^5*x3 - 30*l*n^3*x1^2 - 24*l*n*x1^5 - 38*l*n*x1^4*x3 - 6*n^4*x1 - 16*n^2*x1^4 - 14*n^2*x1^3*x3) * hR + (-4*l^3*n^2*x1^3 - 14*l^2*n^3*x1^2 - 4*l^2*n*x1^5 - 2*l^2*n*x1^4*x3 - 12*l*n^4*x1 - 8*l*n^2*x1^4 - 8*l*n^2*x1^3*x3 - 3*n^5 - 8*n^3*x1^3 - 4*n^3*x1^2*x3 + 4*n*x1^5*x3 - n*x1^4*x3^2) * hDdef

end Mordell.IsogId