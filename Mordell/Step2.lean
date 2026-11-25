import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Mordell の定理 Step 2（弱 Mordell–Weil）の前半

位数 2 の有理点 `T = (0,0)` を持つ曲線
  `E : y² = x³ + a x² + b x`   （`b ≠ 0`）
を考える。平方類の群 `F^× / (F^×)²` を `SqClass F` と書き、写像

  `α(O) = 1`,  `α(T) = b`,  `α(x, y) = x`  （`x ≠ 0`）

を定める（Silverman–Tate, *Rational Points on Elliptic Curves*, §III.5）。

1. `alpha_add`      : `α` は準同型（任意の体 `F`、群構造は Mathlib の `W.Point` のもの）
2. `alpha_eq_cls_dvd` : `F = ℚ`、`a b ∈ ℤ` のとき `α(P)` は `b` のある約数 `d` の平方類
3. `finite_range_alpha` : 特に `α` の像は有限

## 証明の要点
* **Vieta**（`vieta`）：直線 `y = ℓx + ν` が曲線と `x₁, x₂` で交わるとき、
  第 3 交点 `x₃ = ℓ² - a - x₁ - x₂` について
  `x₁x₂ + x₁x₃ + x₂x₃ = b - 2ℓν`、`x₁x₂x₃ = ν²`。
  （`x³+ax²+bx-(ℓx+ν)² - (x-x₁)(x-x₂)(x-x₃)` は 1 次式で、`x₁, x₂`（接線なら重根）で消える）
* **像**：`x = m/n`（既約）なら `(mn)·(m² + amn + bn²)` は整数の平方。
  2 因子の公約数は `b` を割る（`b n⁴ = n²S - mn(mn + an²)`、`m⁴ = m²S - mn(am² + bmn)`）
  ので、`mn = ± g u²`（`g ∣ b`）。
-/

namespace Mordell.Step2

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## 平方類 -/

/-- 平方類の群 `F^× / (F^×)²`。 -/
def SqClass (F : Type*) [Field F] : Type _ := Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range

noncomputable instance (F : Type*) [Field F] : CommGroup (SqClass F) :=
  QuotientGroup.Quotient.commGroup _

section SqClass

variable {F : Type*} [Field F]

/-- 単数の平方類。 -/
def mkSq (u : Fˣ) : SqClass F := (QuotientGroup.mk u : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)

lemma mkSq_mul (u v : Fˣ) : (mkSq (u * v) : SqClass F) = mkSq u * mkSq v :=
  QuotientGroup.mk_mul _ _ _

lemma mkSq_sq (w : Fˣ) : (mkSq (w ^ 2) : SqClass F) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩

lemma mkSq_one : (mkSq 1 : SqClass F) = 1 := rfl

open Classical in
/-- `x ≠ 0` の平方類（`x = 0` には便宜上 `1` を割り当てる）。 -/
noncomputable def cls (x : F) : SqClass F :=
  if hx : x = 0 then 1 else mkSq (Units.mk0 x hx)

lemma cls_of_ne {x : F} (hx : x ≠ 0) : cls x = mkSq (Units.mk0 x hx) := by
  simp [cls, hx]

@[simp] lemma cls_zero : cls (0 : F) = 1 := by simp [cls]

@[simp] lemma cls_one : cls (1 : F) = 1 := by
  rw [cls_of_ne one_ne_zero, ← mkSq_one]
  congr 1
  ext
  simp

lemma cls_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : cls (x * y) = cls x * cls y := by
  rw [cls_of_ne hx, cls_of_ne hy, cls_of_ne (mul_ne_zero hx hy), ← mkSq_mul]
  congr 1
  ext
  simp

lemma cls_sq {z : F} (hz : z ≠ 0) : cls (z ^ 2) = 1 := by
  rw [cls_of_ne (pow_ne_zero 2 hz), ← mkSq_sq (Units.mk0 z hz)]
  congr 1
  ext
  simp

lemma cls_mul_self (z : F) : cls z * cls z = 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [← cls_mul hz hz, ← sq, cls_sq hz]

/-- `v = u z²` なら `v` と `u` は同じ平方類。 -/
lemma cls_eq_of_eq_mul_sq {u v z : F} (hu : u ≠ 0) (hz : z ≠ 0) (h : v = u * z ^ 2) :
    cls v = cls u := by
  rw [h, cls_mul hu (pow_ne_zero 2 hz), cls_sq hz, mul_one]

end SqClass

/-! ## 曲線 `y² = x³ + a x² + b x` -/

section Curve

variable {F : Type*} [Field F]

/-- `y² = x³ + a x² + b x`。 -/
def curve (a b : F) : Affine F := (⟨0, a, 0, b, 0⟩ : WeierstrassCurve F).toAffine

variable {a b : F}

@[simp] lemma curve_a₁ : (curve a b).a₁ = 0 := rfl
@[simp] lemma curve_a₂ : (curve a b).a₂ = a := rfl
@[simp] lemma curve_a₃ : (curve a b).a₃ = 0 := rfl
@[simp] lemma curve_a₄ : (curve a b).a₄ = b := rfl
@[simp] lemma curve_a₆ : (curve a b).a₆ = 0 := rfl

lemma curve_equation {x y : F} (h : (curve a b).Nonsingular x y) :
    y ^ 2 = x ^ 3 + a * x ^ 2 + b * x := by
  have := (equation_iff x y).mp h.1
  simpa [curve] using this

@[simp] lemma curve_negY (x y : F) : (curve a b).negY x y = -y := by
  simp [curve, negY]

@[simp] lemma curve_addX (x₁ x₂ ℓ : F) : (curve a b).addX x₁ x₂ ℓ = ℓ ^ 2 - a - x₁ - x₂ := by
  simp [curve, addX]

/-- 曲線上で `x = 0` なら `y = 0`（つまりその点は `T`）。 -/
lemma y_eq_zero_of_x_eq_zero {x y : F} (h : (curve a b).Nonsingular x y) (hx : x = 0) : y = 0 := by
  have := curve_equation h
  rw [hx] at this
  simpa using this

/-! ### Vieta：直線と曲線の 3 交点 -/

/-- 直線 `y = ℓx + ν` 上の 2 点（または接点）`x₁, x₂` に対し、
第 3 交点 `x₃ = ℓ² - a - x₁ - x₂` について基本対称式の関係が成り立つ。 -/
lemma vieta {x₁ x₂ ℓ ν : F}
    (h₁ : (ℓ * x₁ + ν) ^ 2 = x₁ ^ 3 + a * x₁ ^ 2 + b * x₁)
    (h₂ : (ℓ * x₂ + ν) ^ 2 = x₂ ^ 3 + a * x₂ ^ 2 + b * x₂)
    (hdeg : x₁ ≠ x₂ ∨ (x₁ = x₂ ∧ 2 * ℓ * (ℓ * x₁ + ν) = 3 * x₁ ^ 2 + 2 * a * x₁ + b)) :
    x₁ * x₂ + x₁ * (ℓ ^ 2 - a - x₁ - x₂) + x₂ * (ℓ ^ 2 - a - x₁ - x₂) = b - 2 * ℓ * ν ∧
      x₁ * x₂ * (ℓ ^ 2 - a - x₁ - x₂) = ν ^ 2 := by
  -- r(t) := t³+at²+bt-(ℓt+ν)² - (t-x₁)(t-x₂)(t-x₃) = p t + q
  set x₃ := ℓ ^ 2 - a - x₁ - x₂ with hx₃
  set p := (b - 2 * ℓ * ν) - (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) with hp
  set q := x₁ * x₂ * x₃ - ν ^ 2 with hq
  have r₁ : p * x₁ + q = 0 := by rw [hp, hq, hx₃]; linear_combination (-1 : F) * h₁
  have r₂ : p * x₂ + q = 0 := by rw [hp, hq, hx₃]; linear_combination (-1 : F) * h₂
  have hp0 : p = 0 := by
    rcases hdeg with hne | ⟨heq, htan⟩
    · have : p * (x₁ - x₂) = 0 := by linear_combination r₁ - r₂
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    · -- 接線の場合：r'(x₁) = p
      subst heq
      rw [hp, hx₃]
      linear_combination (-1 : F) * htan
  have hq0 : q = 0 := by rw [hp0, zero_mul, zero_add] at r₁; exact r₁
  refine ⟨?_, ?_⟩
  · linear_combination -hp0
  · linear_combination hq0

variable [DecidableEq F]

/-- Mathlib の `slope` で与えられる直線について Vieta の関係をまとめたもの。 -/
lemma vieta_slope {x₁ x₂ y₁ y₂ : F} (h₁ : (curve a b).Nonsingular x₁ y₁)
    (h₂ : (curve a b).Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = -y₂)) :
    let ℓ := (curve a b).slope x₁ x₂ y₁ y₂
    let ν := y₁ - ℓ * x₁
    y₂ = ℓ * x₂ + ν ∧
      x₁ * x₂ + x₁ * (ℓ ^ 2 - a - x₁ - x₂) + x₂ * (ℓ ^ 2 - a - x₁ - x₂) = b - 2 * ℓ * ν ∧
      x₁ * x₂ * (ℓ ^ 2 - a - x₁ - x₂) = ν ^ 2 := by
  intro ℓ ν
  have e₁ := curve_equation h₁
  have e₂ := curve_equation h₂
  have hy₁ : y₁ = ℓ * x₁ + ν := by simp only [ν]; ring
  by_cases hx : x₁ = x₂
  · -- 接線：y₁ = y₂ ≠ 0
    have hy : y₁ ≠ -y₂ := fun h => hxy ⟨hx, h⟩
    have hyy : y₁ = y₂ := by
      subst hx
      have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (eq_neg_of_add_eq_zero_left h) hy
    have h2y : y₁ - -y₁ ≠ 0 := by
      intro h; apply hy; rw [← hyy]; linear_combination h
    have hy10 : y₁ ≠ 0 := by intro h; apply h2y; rw [h]; ring
    have hℓ : ℓ = (3 * x₁ ^ 2 + 2 * a * x₁ + b) / (y₁ - -y₁) := by
      simp only [ℓ]
      rw [slope_of_Y_ne (W := curve a b) hx (by simpa using hy)]
      simp [curve]
    have htan : 2 * ℓ * (ℓ * x₁ + ν) = 3 * x₁ ^ 2 + 2 * a * x₁ + b := by
      have hc := div_mul_cancel₀ (3 * x₁ ^ 2 + 2 * a * x₁ + b) h2y
      rw [← hℓ] at hc
      rw [← hy₁]
      linear_combination hc
    have hy₂ : y₂ = ℓ * x₂ + ν := by rw [← hyy, ← hx]; exact hy₁
    refine ⟨hy₂, vieta (hy₁ ▸ e₁) (hy₂ ▸ e₂) (Or.inr ⟨hx, htan⟩)⟩
  · -- 割線
    have hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne (W := curve a b) hx
    have hsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hy₂ : y₂ = ℓ * x₂ + ν := by
      simp only [ν]; rw [hℓ]; field_simp; ring
    exact ⟨hy₂, vieta (hy₁ ▸ e₁) (hy₂ ▸ e₂) (Or.inl hx)⟩

end Curve

/-! ## 写像 `α` と準同型性 -/

section Alpha

variable {F : Type*} [Field F] [DecidableEq F]

/-- `α : E(F) → F^×/(F^×)²`。`α(O) = 1`、`α(T) = b`、`α(x,y) = x`。 -/
noncomputable def alpha (a b : F) : (curve a b).Point → SqClass F
  | .zero => 1
  | .some x _ _ => if x = 0 then cls b else cls x

variable {a b : F}

@[simp] lemma alpha_zero : alpha a b 0 = 1 := rfl

lemma alpha_some {x y : F} (h : (curve a b).Nonsingular x y) :
    alpha a b (.some x y h) = if x = 0 then cls b else cls x := rfl

/-- 同じ `x` 座標を持つ 2 点の `α` の積は `1`。 -/
lemma alpha_mul_alpha_of_x_eq {x₁ x₂ y₁ y₂ : F} (h₁ : (curve a b).Nonsingular x₁ y₁)
    (h₂ : (curve a b).Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    alpha a b (.some x₁ y₁ h₁) * alpha a b (.some x₂ y₂ h₂) = 1 := by
  subst hx
  rw [alpha_some, alpha_some]
  split_ifs <;> exact cls_mul_self _

/-- **α は準同型**：`α(P + Q) = α(P) α(Q)`。 -/
theorem alpha_add (hb : b ≠ 0) (P Q : (curve a b).Point) :
    alpha a b (P + Q) = alpha a b P * alpha a b Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, alpha_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, alpha_zero, mul_one]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve a b).negY x₂ y₂
  · -- P + Q = O
    rw [Point.add_of_Y_eq hxy.1 hxy.2, alpha_zero, alpha_mul_alpha_of_x_eq h₁ h₂ hxy.1]
  rw [Point.add_some hxy, alpha_some, alpha_some, alpha_some, curve_addX]
  have hxy' : ¬(x₁ = x₂ ∧ y₁ = -y₂) := by simpa using hxy
  obtain ⟨hy₂, e1, e0⟩ := vieta_slope h₁ h₂ hxy'
  set ℓ := (curve a b).slope x₁ x₂ y₁ y₂
  set ν := y₁ - ℓ * x₁ with hν
  set x₃ := ℓ ^ 2 - a - x₁ - x₂ with hx₃
  by_cases hx₁ : x₁ = 0
  · -- P = T：ν = 0、x₂ x₃ = b
    have hy₁ : y₁ = 0 := y_eq_zero_of_x_eq_zero h₁ hx₁
    have hν0 : ν = 0 := by rw [hν, hy₁, hx₁]; ring
    have hb' : x₂ * x₃ = b := by rw [hν0, hx₁] at e1; linear_combination e1
    have hx₂ : x₂ ≠ 0 := by rintro rfl; apply hb; rw [← hb']; ring
    have hx₃0 : x₃ ≠ 0 := by intro h; apply hb; rw [← hb', h]; ring
    rw [ite_eq_right hx₃0, ite_eq_left hx₁, ite_eq_right hx₂, ← cls_mul hb hx₂]
    exact cls_eq_of_eq_mul_sq (mul_ne_zero hb hx₂) (inv_ne_zero hx₂)
      (by rw [← hb']; field_simp)
  by_cases hx₂ : x₂ = 0
  · -- Q = T：ν = 0、x₁ x₃ = b
    have hy₂0 : y₂ = 0 := y_eq_zero_of_x_eq_zero h₂ hx₂
    have hν0 : ν = 0 := by rw [hx₂, hy₂0] at hy₂; linear_combination -hy₂
    have hb' : x₁ * x₃ = b := by rw [hν0, hx₂] at e1; linear_combination e1
    have hx₃0 : x₃ ≠ 0 := by intro h; apply hb; rw [← hb', h]; ring
    rw [ite_eq_right hx₃0, ite_eq_right hx₁, ite_eq_left hx₂, ← cls_mul hx₁ hb]
    exact cls_eq_of_eq_mul_sq (mul_ne_zero hx₁ hb) (inv_ne_zero hx₁)
      (by rw [← hb']; field_simp)
  by_cases hx₃0 : x₃ = 0
  · -- P + Q = T：ν = 0、x₁ x₂ = b
    have hν0 : ν = 0 := by
      rw [hx₃0, mul_zero] at e0; exact pow_eq_zero_iff (two_ne_zero) |>.mp e0.symm
    have hb' : x₁ * x₂ = b := by rw [hν0, hx₃0] at e1; linear_combination e1
    rw [ite_eq_left hx₃0, ite_eq_right hx₁, ite_eq_right hx₂, ← cls_mul hx₁ hx₂, hb']
  · -- 一般の場合：x₁ x₂ x₃ = ν² ≠ 0 より x₃ ≡ x₁ x₂
    have hν0 : ν ≠ 0 := by
      intro h; rw [h] at e0
      exact mul_ne_zero (mul_ne_zero hx₁ hx₂) hx₃0 (by rw [e0]; ring)
    rw [ite_eq_right hx₃0, ite_eq_right hx₁, ite_eq_right hx₂, ← cls_mul hx₁ hx₂]
    exact cls_eq_of_eq_mul_sq (mul_ne_zero hx₁ hx₂) (div_ne_zero hν0 (mul_ne_zero hx₁ hx₂))
      (by field_simp; linear_combination e0)

/-- `α` を加法群の準同型 `E(F) →+ Additive (F^×/(F^×)²)` として束ねたもの。 -/
noncomputable def alphaHom (hb : b ≠ 0) : (curve a b).Point →+ Additive (SqClass F) where
  toFun P := Additive.ofMul (alpha a b P)
  map_zero' := rfl
  map_add' P Q := by rw [alpha_add hb]; rfl

end Alpha

/-! ## 像は `b` の約数で抑えられる（`F = ℚ`, `a b ∈ ℤ`） -/

section Image

/-- `mn` と `S = m² + amn + bn²` の公約数は `b` を割る（`m, n` 互いに素）。 -/
lemma dvd_b_of_dvd {a b m n t : ℤ} (hmn : IsCoprime m n) (h₁ : t ∣ m * n)
    (h₂ : t ∣ m ^ 2 + a * m * n + b * n ^ 2) : t ∣ b := by
  -- b n⁴ = n² S - mn (mn + a n²),  m⁴ = m² S - mn (a m² + b m n)
  have hn : t ∣ b * n ^ 4 := by
    have : b * n ^ 4 = n ^ 2 * (m ^ 2 + a * m * n + b * n ^ 2) - (m * n) * (m * n + a * n ^ 2) := by
      ring
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_right h₂ _) (dvd_mul_of_dvd_left h₁ _)
  have hm : t ∣ b * m ^ 4 := by
    have : m ^ 4 = m ^ 2 * (m ^ 2 + a * m * n + b * n ^ 2) - (m * n) * (a * m ^ 2 + b * m * n) := by
      ring
    exact dvd_mul_of_dvd_right
      (this ▸ dvd_sub (dvd_mul_of_dvd_right h₂ _) (dvd_mul_of_dvd_left h₁ _)) b
  obtain ⟨u, v, huv⟩ := hmn.pow (m := 4) (n := 4)
  have : b = u * (b * m ^ 4) + v * (b * n ^ 4) := by linear_combination (-b) * huv
  rw [this]; exact dvd_add (dvd_mul_of_dvd_right hm _) (dvd_mul_of_dvd_right hn _)

/-- 整数論的な核心：`y² = x³ + a x² + b x`、`x = m/n ≠ 0`（既約）なら
`m n = d u²`（`d ∣ b`, `u ≠ 0`）。 -/
lemma num_mul_den_eq {a b : ℤ} {x y : ℚ} (hx : x ≠ 0)
    (h : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x) :
    ∃ d u : ℤ, d ∣ b ∧ u ≠ 0 ∧ x.num * x.den = d * u ^ 2 := by
  set m : ℤ := x.num with hm
  set n : ℤ := (x.den : ℤ) with hn
  have hm0 : m ≠ 0 := Rat.num_ne_zero.mpr hx
  have hn0 : n ≠ 0 := by simp [hn]
  have hcop : IsCoprime m n := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [hm, hn, Int.gcd] using x.reduced
  have hxmn : x = m / n := (Rat.num_div_den x).symm
  set S : ℤ := m ^ 2 + a * m * n + b * n ^ 2 with hS
  -- (y n²)² = (mn) S
  have hsq : IsSquare (((m * n * S : ℤ)) : ℚ) := by
    refine ⟨y * n ^ 2, ?_⟩
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    rw [hxmn] at h
    push_cast [hS]
    field_simp at h
    linear_combination (-(n : ℚ)) * h
  obtain ⟨k, hk⟩ := Rat.isSquare_intCast_iff.mp hsq
  -- g = gcd(mn, S)
  have hg0 : 0 < Int.gcd (m * n) S := Int.gcd_pos_of_ne_zero_left _ (mul_ne_zero hm0 hn0)
  obtain ⟨A, B, hAB, hA, hB⟩ := Int.exists_gcd_one hg0
  set g : ℤ := (Int.gcd (m * n) S : ℤ) with hg
  have hgb : g ∣ b := dvd_b_of_dvd hcop (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
  have hgne : g ≠ 0 := by simp [hg]; omega
  -- A B は平方数
  have hABsq : IsSquare (A * B) := by
    apply Rat.isSquare_intCast_iff.mp
    refine ⟨(k : ℚ) / g, ?_⟩
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hgne
    have : (m * n * S : ℤ) = g ^ 2 * (A * B) := by rw [hA, hB]; ring
    rw [this] at hk
    have hk' : ((g : ℚ) ^ 2 * (A * B)) = k * k := by exact_mod_cast hk
    push_cast
    field_simp
    linear_combination hk'
  obtain ⟨c, hc⟩ := hABsq
  obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' (Int.isCoprime_iff_gcd_eq_one.mpr hAB)
    (show A * B = c ^ 2 by rw [hc]; ring)
  have hA0 : A ≠ 0 := by rintro rfl; apply mul_ne_zero hm0 hn0; rw [hA]; ring
  rcases Int.associated_iff.mp hu with h1 | h1
  · refine ⟨g, u, hgb, ?_, ?_⟩
    · rintro rfl; apply hA0; rw [← h1]; ring
    · rw [hA, ← h1]; ring
  · refine ⟨-g, u, neg_dvd.mpr hgb, ?_, ?_⟩
    · rintro rfl; apply hA0; linear_combination h1
    · rw [hA]; linear_combination g * h1

/-- **像の評価**：`α(P)` は `b` のある約数 `d` の平方類。 -/
theorem alpha_eq_cls_dvd {a b : ℤ} (P : (curve (a : ℚ) b).Point) :
    ∃ d : ℤ, d ∣ b ∧ alpha (a : ℚ) b P = cls (d : ℚ) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨1, one_dvd _, by simp [← Point.zero_def]⟩
  rw [alpha_some]
  by_cases hx : x = 0
  · exact ⟨b, dvd_rfl, by rw [ite_eq_left hx]⟩
  rw [ite_eq_right hx]
  obtain ⟨d, u, hd, hu, hdu⟩ := num_mul_den_eq hx (curve_equation h)
  refine ⟨d, hd, ?_⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : (x.num * x.den : ℤ) ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hx) (by simp)
    exact this (by rw [hdu]; ring)
  have hden : (x.den : ℚ) ≠ 0 := by simp
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  -- x · den² = num · den = d u²
  have hx' : x = d * ((u : ℚ) / x.den) ^ 2 := by
    have h1 : ((x.num * x.den : ℤ) : ℚ) = d * u ^ 2 := by exact_mod_cast hdu
    have h2 : (x.num : ℚ) = x * x.den := by
      exact (Rat.mul_den_eq_num x).symm
    push_cast at h1
    rw [h2] at h1
    field_simp
    linear_combination h1
  exact cls_eq_of_eq_mul_sq hdq (div_ne_zero huq hden) hx'

/-- `α` の像は有限集合（`b` の約数の平方類に含まれる）。 -/
theorem finite_range_alpha {a b : ℤ} (hb : b ≠ 0) : (Set.range (alpha (a : ℚ) b)).Finite := by
  have hdiv : {d : ℤ | d ∣ b}.Finite := by
    refine (Set.finite_Icc (-|b|) |b|).subset fun d hd => ?_
    have := Int.le_of_dvd (abs_pos.mpr hb) ((abs_dvd_abs d b).mpr hd)
    exact abs_le.mp this
  refine (hdiv.image fun d : ℤ => cls (d : ℚ)).subset ?_
  rintro _ ⟨P, rfl⟩
  obtain ⟨d, hd, h⟩ := alpha_eq_cls_dvd P
  exact ⟨d, hd, h.symm⟩

end Image

end Mordell.Step2
