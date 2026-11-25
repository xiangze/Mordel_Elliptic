import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Defs

set_option linter.unusedVariables false

namespace Mordell.IsogId

lemma jImageEq {x y u c d A B : ℚ} (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (h : y^2 = x^3 + c*x^2 + d*x) (hu : u ≠ 0) (hx : x ≠ 0) :
    (y*(d-x^2)/(u^3*x^2))^2 = (y^2/(u^2*x^2))^3 + A*(y^2/(u^2*x^2))^2 + B*(y^2/(u^2*x^2)) := by
  subst hA hB
  field_simp
  linear_combination (c*x^2*y^2 - d*x*y^2 - x^3*y^2 - y^4) * h

lemma jTwoX {x y a b a' b' X Y l x3 : ℚ} (ha' : a' = -2*a) (hb' : b' = a^2-4*b) (h : y^2 = x^3 + a*x^2 + b*x) (hx : x ≠ 0) (hy : y ≠ 0) (hX : X = y^2/x^2) (hY : Y = y*(b-x^2)/x^2) (hl : l = (3*x^2+2*a*x+b)/(2*y)) (hx3 : x3 = l^2 - a - 2*x) :
    Y^2/(4*X^2) = x3 := by
  subst ha' hb' hX hY hl hx3
  field_simp
  linear_combination (16*a + 32*x) * h

lemma jTwoY {x y a b a' b' X Y l x3 : ℚ} (ha' : a' = -2*a) (hb' : b' = a^2-4*b) (h : y^2 = x^3 + a*x^2 + b*x) (hx : x ≠ 0) (hy : y ≠ 0) (hX : X = y^2/x^2) (hY : Y = y*(b-x^2)/x^2) (hl : l = (3*x^2+2*a*x+b)/(2*y)) (hx3 : x3 = l^2 - a - 2*x) :
    Y*(b'-X^2)/(8*X^2) = -(l*(x3-x)+y) := by
  subst ha' hb' hX hY hl hx3
  field_simp
  linear_combination (-64*a^2*x^3 - 40*a*b*x^2 - 216*a*x^4 - 8*b^2*x - 32*b*x^3 - 8*b*y^2 - 216*x^5 + 72*x^2*y^2) * h

lemma jKerEq {w y u c d A B X : ℚ} (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (h : y^2 = (w^2)^3 + A*(w^2)^2 + B*w^2) (hu : u ≠ 0) (hw : w ≠ 0) (hX : X = (u^2*w^2 - c + u^2*y/w)/2) :
    (-u*w*X)^2 = X^3 + c*X^2 + d*X := by
  subst hA hB hX
  have h' : u^4*y^2 = u^4*(w^2)^3 - 2*c*u^2*(w^2)^2 + (c^2-4*d)*w^2 := by rw [h]; field_simp; ring
  field_simp
  linear_combination (c*w - u^2*w^3 - u^2*y) * h'

lemma jKerProd {w y u c d A B X : ℚ} (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4) (h : y^2 = (w^2)^3 + A*(w^2)^2 + B*w^2) (hu : u ≠ 0) (hw : w ≠ 0) (hX : X = (u^2*w^2 - c + u^2*y/w)/2) :
    X * ((u^2*w^2 - c - u^2*y/w)/2) = d := by
  subst hA hB hX
  have h' : u^4*y^2 = u^4*(w^2)^3 - 2*c*u^2*(w^2)^2 + (c^2-4*d)*w^2 := by rw [h]; field_simp; ring
  field_simp
  linear_combination (-1) * h'

lemma jKerY {w y u c d A B X : ℚ} (hA : A = -2*c/u^2) (hB : B = (c^2-4*d)/u^4)
    (h : y^2 = (w^2)^3 + A*(w^2)^2 + B*w^2) (hu : u ≠ 0) (hw : w ≠ 0)
    (hX : X = (u^2*w^2 - c + u^2*y/w)/2) (hX0 : X ≠ 0) :
    (-u*w*X)*(d-X^2)/(u^3*X^2) = y := by
  have hprod := jKerProd hA hB h hu hw hX
  have hdX : d - X^2 = X * (-(u^2*y/w)) := by rw [← hprod, hX]; ring
  rw [hdX]
  field_simp

end Mordell.IsogId