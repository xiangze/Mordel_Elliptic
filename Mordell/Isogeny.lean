import Mw.Step2
import Mw.IsogId
import Mw.IsogId2

/-!
# 2-同種写像（Mordell の定理 Step 2 の残り）

`E : y² = x³ + c x² + d x` から `E_u : y² = x³ + A x² + B x`
（`A = -2c/u²`, `B = (c² - 4d)/u⁴`）への写像

  `φ_u(O) = O`,  `φ_u(T) = O`,  `φ_u(x, y) = (y²/(u²x²), y(d - x²)/(u³x²))`

を Mathlib の点の群 `W.Point` の間の写像として定義し、

* `Data.phi_add`  : `φ_u` は**準同型**
* `psi_phi`       : `ψ ∘ φ = [2]`（`φ = φ₁ : E → E'`, `ψ = φ₂ : E' → E`）
* `Data.exists_phi_eq_of_alpha_eq_one` : `ker α ⊆ φ_u(E(ℚ))`

を示す。`u = 1` が `φ : E → E'`、`u = 2` が `ψ : E' → E`
（`E' : y² = x³ - 2a x² + (a² - 4b) x`）にあたる。

加法性の証明の核心は、`E'` 上の弦（接線）の傾きが閉じた式
`L = N / (-ν u (2ℓx₁x₂ + ν(x₁+x₂)))` で与えられること（`Mw.IsogId`）。
この 1 つの式が割線・接線の両方で正しい。
-/

namespace Mordell.Isogeny

open WeierstrassCurve WeierstrassCurve.Affine Mordell.Step2 Mordell.IsogId

/-! ## 曲線の基本事実（ℚ 上） -/

lemma curve_Δ (a b : ℚ) : (curve a b).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

lemma isElliptic_curve {a b : ℚ} (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) :
    (curve a b).IsElliptic :=
  ⟨by
    rw [curve_Δ]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)) hab)⟩

lemma nonsingular_of_eq {a b x y : ℚ} (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0)
    (h : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x) : (curve a b).Nonsingular x y := by
  have := isElliptic_curve hb hab
  refine (equation_iff_nonsingular (W := curve a b)).mp ?_
  rw [equation_iff]
  simp only [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  linear_combination h

lemma curve_addY (a b x₁ x₂ y₁ ℓ : ℚ) :
    (curve a b).addY x₁ x₂ y₁ ℓ = -(ℓ * (ℓ ^ 2 - a - x₁ - x₂ - x₁) + y₁) := by
  simp [addY, negAddY]

lemma some_eq {a b x y x' y' : ℚ} {h : (curve a b).Nonsingular x y}
    {h' : (curve a b).Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

/-- 平方類が自明なら平方数。 -/
lemma eq_sq_of_cls_eq_one {z : ℚ} (hz : z ≠ 0) (h : cls z = 1) : ∃ w : ℚ, w ≠ 0 ∧ z = w ^ 2 := by
  rw [cls_of_ne hz] at h
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff (Units.mk0 z hz)).mp h
  refine ⟨w, w.ne_zero, ?_⟩
  have := congrArg Units.val hw
  simpa [eq_comm] using this

/-! ## 同種写像のデータ -/

/-- `φ_u : y² = x³ + cx² + dx  →  y² = x³ + Ax² + Bx` のデータ。 -/
structure Data where
  c : ℚ
  d : ℚ
  A : ℚ
  B : ℚ
  u : ℚ
  hu : u ≠ 0
  hd : d ≠ 0
  hcd : c ^ 2 - 4 * d ≠ 0
  hA : A = -2 * c / u ^ 2
  hB : B = (c ^ 2 - 4 * d) / u ^ 4

namespace Data

variable (I : Data)

lemma hB0 : I.B ≠ 0 := by rw [I.hB]; exact div_ne_zero I.hcd (pow_ne_zero 4 I.hu)

lemma hAB : I.A ^ 2 - 4 * I.B ≠ 0 := by
  have hu := I.hu
  have : I.A ^ 2 - 4 * I.B = 16 * I.d / I.u ^ 4 := by
    rw [I.hA, I.hB]; field_simp; ring
  rw [this]; exact div_ne_zero (mul_ne_zero (by norm_num) I.hd) (pow_ne_zero 4 I.hu)

/-- 像の `x` 座標。 -/
def imX (x y : ℚ) : ℚ := y ^ 2 / (I.u ^ 2 * x ^ 2)
/-- 像の `y` 座標。 -/
def imY (x y : ℚ) : ℚ := y * (I.d - x ^ 2) / (I.u ^ 3 * x ^ 2)

lemma im_nonsingular {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x ≠ 0) :
    (curve I.A I.B).Nonsingular (I.imX x y) (I.imY x y) :=
  nonsingular_of_eq I.hB0 I.hAB (jImageEq I.hA I.hB (curve_equation h) I.hu hx)

/-- 2-同種写像 `φ_u`。 -/
noncomputable def phi : (curve I.c I.d).Point → (curve I.A I.B).Point
  | .zero => .zero
  | .some x _ h => if hx : x = 0 then .zero else .some _ _ (I.im_nonsingular h hx)

@[simp] lemma phi_zero : I.phi 0 = 0 := rfl

lemma phi_some_of_ne {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x ≠ 0) :
    I.phi (.some x y h) = .some _ _ (I.im_nonsingular h hx) := dite_eq_right hx

lemma phi_some_of_eq {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x = 0) :
    I.phi (.some x y h) = 0 := dite_eq_left hx

/-- 位数 2 の点 `T = (0, 0)`。 -/
noncomputable def T : (curve I.c I.d).Point := .some 0 0 (nonsingular_of_eq I.hd I.hcd (by ring))

@[simp] lemma phi_T : I.phi I.T = 0 := I.phi_some_of_eq _ rfl

lemma eq_T {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x = 0) : Point.some x y h = I.T :=
  some_eq hx (y_eq_zero_of_x_eq_zero h hx)

/-! ### `φ(-P) = -φ(P)` -/

lemma phi_neg (P : (curve I.c I.d).Point) : I.phi (-P) = -I.phi P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero, phi_zero, neg_zero]
  rw [Point.neg_some]
  by_cases hx : x = 0
  · rw [I.phi_some_of_eq _ hx, I.phi_some_of_eq _ hx, neg_zero]
  rw [I.phi_some_of_ne _ hx, I.phi_some_of_ne _ hx, Point.neg_some]
  refine some_eq ?_ ?_ <;> simp only [imX, imY, curve_negY] <;> ring

/-! ### `P + T` と `φ(P + T) = φ(P)` -/

lemma add_T_nonsingular {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x ≠ 0) :
    (curve I.c I.d).Nonsingular (I.d / x) (-(I.d * y / x ^ 2)) := by
  refine nonsingular_of_eq I.hd I.hcd ?_
  have e := curve_equation h
  rw [neg_sq, div_pow, mul_pow, e]
  field_simp
  ring

lemma add_T {x y : ℚ} (h : (curve I.c I.d).Nonsingular x y) (hx : x ≠ 0) :
    Point.some x y h + I.T = Point.some _ _ (I.add_T_nonsingular h hx) := by
  have e := curve_equation h
  have hxy : ¬(x = 0 ∧ y = (curve I.c I.d).negY 0 0) := fun h' => hx h'.1
  rw [T, Point.add_some hxy]
  have hℓ : (curve I.c I.d).slope x 0 y 0 = y / x := by
    rw [slope_of_X_ne (W := curve I.c I.d) hx]; simp
  have hx3 : (curve I.c I.d).addX x 0 ((curve I.c I.d).slope x 0 y 0) = I.d / x := by
    rw [curve_addX, hℓ, div_pow, e]; field_simp; ring
  refine some_eq hx3 ?_
  rw [curve_addY, hℓ, div_pow, e]
  field_simp
  ring

lemma phi_add_T (P : (curve I.c I.d).Point) : I.phi (P + I.T) = I.phi P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, zero_add, phi_T, phi_zero]
  by_cases hx : x = 0
  · have hy := y_eq_zero_of_x_eq_zero h hx
    rw [I.eq_T h hx, T, Point.add_of_Y_eq rfl (by simp), I.phi_some_of_eq _ rfl, phi_zero]
  rw [I.add_T h hx, I.phi_some_of_ne _ hx,
    I.phi_some_of_ne _ (div_ne_zero I.hd hx)]
  have hu := I.hu; have hd := I.hd
  refine some_eq ?_ ?_
  · simp only [imX]; field_simp
  · simp only [imY]; field_simp; ring

/-! ### 分類：`φ(P)` と `φ(Q)` の `x` 座標が等しければ `Q ∈ {±P, ±(P+T)}` -/

lemma classify {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve I.c I.d).Nonsingular x₁ y₁)
    (h₂ : (curve I.c I.d).Nonsingular x₂ y₂) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : I.imX x₁ y₁ = I.imX x₂ y₂) :
    Point.some x₂ y₂ h₂ = .some x₁ y₁ h₁ ∨ Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ ∨
      Point.some x₂ y₂ h₂ = Point.some x₁ y₁ h₁ + I.T ∨
      Point.some x₂ y₂ h₂ = -(Point.some x₁ y₁ h₁ + I.T) := by
  have e₁ := curve_equation h₁
  have e₂ := curve_equation h₂
  have hu := I.hu
  simp only [imX] at hX
  rw [div_eq_div_iff (by positivity) (by positivity)] at hX
  have key : I.u ^ 2 * x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - I.d)) = 0 := by
    linear_combination hX - (I.u ^ 2 * x₂ ^ 2) * e₁ + (I.u ^ 2 * x₁ ^ 2) * e₂
  have hne : I.u ^ 2 * x₁ * x₂ ≠ 0 := by positivity
  rcases mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne) with h | h
  · -- x₁ = x₂
    have hx : x₁ = x₂ := sub_eq_zero.mp h
    have : (y₂ - y₁) * (y₂ + y₁) = 0 := by rw [← hx] at e₂; linear_combination e₂ - e₁
    rcases mul_eq_zero.mp this with h' | h'
    · left; exact some_eq hx.symm (sub_eq_zero.mp h')
    · right; left; rw [Point.neg_some]; exact some_eq hx.symm (by simp; linear_combination h')
  · -- x₁ x₂ = d：Q = ±(P + T)
    have hx : x₂ = I.d / x₁ := by field_simp; linear_combination h
    have : (y₂ + I.d * y₁ / x₁ ^ 2) * (y₂ - I.d * y₁ / x₁ ^ 2) = 0 := by
      rw [hx] at e₂
      rw [show (y₂ + I.d * y₁ / x₁ ^ 2) * (y₂ - I.d * y₁ / x₁ ^ 2)
          = y₂ ^ 2 - I.d ^ 2 * y₁ ^ 2 / x₁ ^ 4 by ring, e₂, e₁]
      field_simp
      ring
    right; right
    rw [I.add_T h₁ hx₁]
    rcases mul_eq_zero.mp this with h' | h'
    · left; exact some_eq hx (by linear_combination h')
    · right; rw [Point.neg_some]; exact some_eq hx (by simp; linear_combination h')

/-! ### 倍点：`φ(2P) = 2φ(P)` -/

lemma phi_double (P : (curve I.c I.d).Point) : I.phi (P + P) = I.phi P + I.phi P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero, phi_zero, add_zero]
  by_cases hx : x = 0
  · have hy := y_eq_zero_of_x_eq_zero h hx
    rw [Point.add_of_Y_eq rfl (by simp [hy]), I.phi_some_of_eq _ hx, add_zero, phi_zero]
  by_cases hy : y = 0
  · rw [Point.add_of_Y_eq rfl (by simp [hy]), I.phi_some_of_ne _ hx, phi_zero,
      Point.add_of_Y_eq rfl (by simp [imY, hy])]
  have e := curve_equation h
  have hu := I.hu
  have hyy : y ≠ -y := fun h' => hy (by linear_combination h' / 2)
  have hxy : ¬(x = x ∧ y = (curve I.c I.d).negY x y) := by simpa using hyy
  rw [Point.add_some hxy]
  obtain ⟨-, e1, e0⟩ := vieta_slope h h (by simpa using hyy)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (curve I.c I.d).slope x x y y = ℓ := ⟨_, rfl⟩
  simp only [hℓ] at e1 e0
  obtain ⟨ν, hν⟩ : ∃ ν, y - ℓ * x = ν := ⟨_, rfl⟩
  simp only [hν] at e1 e0
  have hy₁ : y = ℓ * x + ν := by linear_combination hν
  obtain ⟨x₃, hx₃⟩ : ∃ x₃, ℓ ^ 2 - I.c - x - x = x₃ := ⟨_, rfl⟩
  simp only [hx₃] at e1 e0
  have hX₃ : (curve I.c I.d).addX x x ((curve I.c I.d).slope x x y y) = x₃ := by
    rw [curve_addX, hℓ, hx₃]
  rw [I.phi_some_of_ne _ hx]
  by_cases hY : I.imY x y = 0
  · -- Y = 0：d = x²、2P = T
    have hdx : I.d = x ^ 2 := by
      simp only [imY] at hY
      rcases div_eq_zero_iff.mp hY with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hy
        · linear_combination h''
      · exact absurd h' (by positivity)
    have hν0 : ν = 0 := by
      -- e1 : x² + 2x x₃ = d - 2ℓν, e0 : x² x₃ = ν²
      have h1 : x * (2 * x₃) = -(2 * ℓ * ν) := by linear_combination e1 + hdx
      have h2 : ν * (ν + ℓ * x) = 0 := by
        have : x * (x * (2 * x₃)) = x * (-(2 * ℓ * ν)) := by rw [h1]
        linear_combination (1/2 : ℚ) * this - e0
      rcases mul_eq_zero.mp h2 with h' | h'
      · exact h'
      · exact absurd (by rw [hy₁]; linear_combination h') hy
    have hx30 : x₃ = 0 := by
      have : x * x * x₃ = 0 := by rw [e0, hν0]; ring
      simpa [hx] using this
    have hT : (curve I.c I.d).addX x x ((curve I.c I.d).slope x x y y) = 0 := by rw [hX₃, hx30]
    rw [I.phi_some_of_eq _ hT, Point.add_of_Y_eq rfl (by simp [hY])]
  -- Y ≠ 0：E' 上も接線
  have hx30 : x₃ ≠ 0 := by
    intro hx30
    apply hY
    have hν0 : ν = 0 := by
      have : ν ^ 2 = 0 := by rw [← e0, hx30]; ring
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hdx : I.d = x ^ 2 := by linear_combination -e1 + 2 * x * hx30 + 2 * ℓ * hν0
    simp [imY, hdx]
  have hn : ν ≠ 0 := by
    intro hn; apply hx30
    have : x * x * x₃ = 0 := by rw [e0, hn]; ring
    simpa [hx] using this
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * ℓ * x * x + ν * x + ν * x := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    have : D = 2 * x * y := by rw [hD, hy₁]; ring
    rw [this]; positivity
  have hX₃0 : (curve I.c I.d).addX x x ((curve I.c I.d).slope x x y y) ≠ 0 := by
    rw [hX₃]; exact hx30
  rw [I.phi_some_of_ne _ hX₃0]
  have hYY : ¬(I.imX x y = I.imX x y ∧ I.imY x y = (curve I.A I.B).negY (I.imX x y) (I.imY x y)) := by
    simp only [curve_negY, true_and]
    intro h'; apply hY; linear_combination h' / 2
  rw [Point.add_some hYY]
  -- E' 上の接線の傾き = L
  have hc : I.c = ℓ ^ 2 - x - x - x₃ := by linear_combination -hx₃
  have hd : I.d = x * x + x * x₃ + x * x₃ + 2 * ℓ * ν := by linear_combination -e1
  have hR : ν ^ 2 = x * x * x₃ := e0.symm
  have hslope : (curve I.A I.B).slope (I.imX x y) (I.imX x y) (I.imY x y) (I.imY x y) =
      (-(2*ℓ^2*ν*x*x + 2*ℓ*x^2*x^2 + 3*ℓ*x^2*x*x₃ + 3*ℓ*x*x^2*x₃ + ν*x^2*x + ν*x^2*x₃
        + ν*x*x^2 + 2*ν*x*x*x₃ + ν*x^2*x₃))/(-ν*I.u*D) := by
    rw [slope_of_Y_ne (W := curve I.A I.B) rfl (by simpa using hYY)]
    simp only [curve_a₁, curve_a₂, curve_a₄, curve_negY, zero_mul, sub_zero]
    have hYne : I.imY x y - -I.imY x y ≠ 0 := by
      intro h'; apply hY; linear_combination h' / 2
    rw [div_eq_iff hYne]
    have := idSlopeTan (x2 := x) hc hd I.hA I.hB hR I.hu hn hx hx30 hD hD0
    simp only [imX, imY]
    rw [hy₁]
    linear_combination -this
  have hy₃ : (curve I.c I.d).addY x x y ((curve I.c I.d).slope x x y y) = -(ℓ * x₃ + ν) := by
    rw [curve_addY, hℓ, ← hx₃, hy₁]; ring
  have hx' := idAddX (x2 := x) hc hd I.hA I.hB hR I.hu hn hx hx hx30 hD hD0
  have hy' := idAddY (x2 := x) hc hd I.hA I.hB hR I.hu hn hx hx hx30 hD hD0
  refine some_eq ?_ ?_
  · rw [hX₃, hy₃, curve_addX, hslope]
    simp only [imX]
    rw [hy₁]
    linear_combination hx'
  · rw [hX₃, hy₃, curve_addY, hslope]
    simp only [imX, imY]
    rw [hy₁]
    generalize hLg : (-(2*ℓ^2*ν*x*x + 2*ℓ*x^2*x^2 + 3*ℓ*x^2*x*x₃ + 3*ℓ*x*x^2*x₃ + ν*x^2*x + ν*x^2*x₃
        + ν*x*x^2 + 2*ν*x*x*x₃ + ν*x^2*x₃))/(-ν*I.u*D) = L at hx' hy' ⊢
    linear_combination hy' - L * hx'

/-! ### 割線：`φ(P)` と `φ(Q)` の `x` 座標が異なる場合 -/

lemma phi_add_chord {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve I.c I.d).Nonsingular x₁ y₁)
    (h₂ : (curve I.c I.d).Nonsingular x₂ y₂) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : I.imX x₁ y₁ ≠ I.imX x₂ y₂) :
    I.phi (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = I.phi (.some x₁ y₁ h₁) + I.phi (.some x₂ y₂ h₂) := by
  have e₁ := curve_equation h₁
  have e₂ := curve_equation h₂
  have hu := I.hu
  have hx : x₁ ≠ x₂ := by
    rintro rfl; apply hX
    simp only [imX]; rw [e₁, e₂]
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (curve I.c I.d).negY x₂ y₂) := fun h' => hx h'.1
  rw [Point.add_some hxy]
  obtain ⟨hy₂, e1, e0⟩ := vieta_slope h₁ h₂ (fun h' => hx h'.1)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (curve I.c I.d).slope x₁ x₂ y₁ y₂ = ℓ := ⟨_, rfl⟩
  simp only [hℓ] at hy₂ e1 e0
  obtain ⟨ν, hν⟩ : ∃ ν, y₁ - ℓ * x₁ = ν := ⟨_, rfl⟩
  simp only [hν] at hy₂ e1 e0
  have hy₁ : y₁ = ℓ * x₁ + ν := by linear_combination hν
  obtain ⟨x₃, hx₃⟩ : ∃ x₃, ℓ ^ 2 - I.c - x₁ - x₂ = x₃ := ⟨_, rfl⟩
  simp only [hx₃] at e1 e0
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * ℓ * x₁ * x₂ + ν * x₁ + ν * x₂ := ⟨_, rfl⟩
  -- X₁ - X₂ = ν (x₂ - x₁) D / (u² x₁² x₂²)
  have hfac : I.imX x₁ y₁ - I.imX x₂ y₂ = ν * (x₂ - x₁) * D / (I.u ^ 2 * x₁ ^ 2 * x₂ ^ 2) := by
    simp only [imX]; rw [hy₁, hy₂, hD]; field_simp; ring
  have hXne : I.imX x₁ y₁ - I.imX x₂ y₂ ≠ 0 := sub_ne_zero.mpr hX
  rw [hfac] at hXne
  have hn : ν ≠ 0 := by intro h'; apply hXne; rw [h']; ring
  have hD0 : D ≠ 0 := by intro h'; apply hXne; rw [h']; ring
  have hx30 : x₃ ≠ 0 := by
    intro h'; apply hn
    have : ν ^ 2 = 0 := by rw [← e0, h']; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hX₃ : (curve I.c I.d).addX x₁ x₂ ((curve I.c I.d).slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [curve_addX, hℓ, hx₃]
  have hX₃0 : (curve I.c I.d).addX x₁ x₂ ((curve I.c I.d).slope x₁ x₂ y₁ y₂) ≠ 0 := by
    rw [hX₃]; exact hx30
  rw [I.phi_some_of_ne _ hX₃0, I.phi_some_of_ne _ hx₁, I.phi_some_of_ne _ hx₂]
  have hXY : ¬(I.imX x₁ y₁ = I.imX x₂ y₂ ∧
      I.imY x₁ y₁ = (curve I.A I.B).negY (I.imX x₂ y₂) (I.imY x₂ y₂)) := fun h' => hX h'.1
  rw [Point.add_some hXY]
  have hc : I.c = ℓ ^ 2 - x₁ - x₂ - x₃ := by linear_combination -hx₃
  have hd : I.d = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + 2 * ℓ * ν := by linear_combination -e1
  have hR : ν ^ 2 = x₁ * x₂ * x₃ := e0.symm
  have hslope : (curve I.A I.B).slope (I.imX x₁ y₁) (I.imX x₂ y₂) (I.imY x₁ y₁) (I.imY x₂ y₂) =
      (-(2*ℓ^2*ν*x₁*x₂ + 2*ℓ*x₁^2*x₂^2 + 3*ℓ*x₁^2*x₂*x₃ + 3*ℓ*x₁*x₂^2*x₃ + ν*x₁^2*x₂ + ν*x₁^2*x₃
        + ν*x₁*x₂^2 + 2*ν*x₁*x₂*x₃ + ν*x₂^2*x₃))/(-ν*I.u*D) := by
    rw [slope_of_X_ne (W := curve I.A I.B) hX, div_eq_iff (sub_ne_zero.mpr hX)]
    have := idSlopeChord hc hd I.hA I.hB hR I.hu hn hx₁ hx₂ hx30 hD hD0
    simp only [imX, imY]
    rw [hy₁, hy₂]
    linear_combination -this
  have hy₃ : (curve I.c I.d).addY x₁ x₂ y₁ ((curve I.c I.d).slope x₁ x₂ y₁ y₂) = -(ℓ * x₃ + ν) := by
    rw [curve_addY, hℓ, ← hx₃, hy₁]; ring
  have hx' := idAddX hc hd I.hA I.hB hR I.hu hn hx₁ hx₂ hx30 hD hD0
  have hy' := idAddY hc hd I.hA I.hB hR I.hu hn hx₁ hx₂ hx30 hD hD0
  refine some_eq ?_ ?_
  · rw [hX₃, hy₃, curve_addX, hslope]
    simp only [imX]
    rw [hy₁, hy₂]
    linear_combination hx'
  · rw [hX₃, hy₃, curve_addY, hslope]
    simp only [imX, imY]
    rw [hy₁, hy₂]
    generalize hLg : (-(2*ℓ^2*ν*x₁*x₂ + 2*ℓ*x₁^2*x₂^2 + 3*ℓ*x₁^2*x₂*x₃ + 3*ℓ*x₁*x₂^2*x₃
        + ν*x₁^2*x₂ + ν*x₁^2*x₃ + ν*x₁*x₂^2 + 2*ν*x₁*x₂*x₃ + ν*x₂^2*x₃))/(-ν*I.u*D) = L at hx' hy' ⊢
    linear_combination hy' - L * hx'

/-! ### φ は準同型 -/

/-- **`φ_u` は群の準同型**。 -/
theorem phi_add (P Q : (curve I.c I.d).Point) : I.phi (P + Q) = I.phi P + I.phi Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, phi_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, phi_zero, add_zero]
  by_cases hx₁ : x₁ = 0
  · rw [I.eq_T h₁ hx₁, add_comm, phi_add_T, phi_T, zero_add]
  by_cases hx₂ : x₂ = 0
  · rw [I.eq_T h₂ hx₂, phi_add_T, phi_T, add_zero]
  by_cases hX : I.imX x₁ y₁ = I.imX x₂ y₂
  · set P := Point.some x₁ y₁ h₁
    rcases I.classify h₁ h₂ hx₁ hx₂ hX with hQ | hQ | hQ | hQ <;> rw [hQ]
    · exact I.phi_double P
    · rw [add_neg_cancel, phi_zero, phi_neg, add_neg_cancel]
    · rw [← add_assoc, phi_add_T, phi_double, phi_add_T]
    · rw [show P + -(P + I.T) = -I.T by abel, phi_neg, phi_neg, phi_T, phi_add_T, neg_zero,
        add_neg_cancel]
  · exact I.phi_add_chord h₁ h₂ hx₁ hx₂ hX

/-- `φ_u` を加法群の準同型として束ねたもの。 -/
noncomputable def phiHom : (curve I.c I.d).Point →+ (curve I.A I.B).Point where
  toFun := I.phi
  map_zero' := rfl
  map_add' := I.phi_add

/-! ### `ker α ⊆ φ_u(E)` -/

/-- **核の包含**：`α(P) = 1` なら `P` は `φ_u` の像に入る。 -/
theorem exists_phi_eq_of_alpha_eq_one (P : (curve I.A I.B).Point) (hP : alpha I.A I.B P = 1) :
    ∃ Q, I.phi Q = P := by
  have hu := I.hu
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  rw [alpha_some] at hP
  by_cases hx : x = 0
  · -- P = T：B = e²、Q = ((-c + u²e)/2, 0)
    rw [ite_eq_left hx] at hP
    obtain ⟨e, -, he⟩ := eq_sq_of_cls_eq_one I.hB0 hP
    set X := (-I.c + I.u ^ 2 * e) / 2 with hXdef
    have hB' : I.u ^ 4 * e ^ 2 = I.c ^ 2 - 4 * I.d := by rw [← he, I.hB]; field_simp
    have hprod : X * ((-I.c - I.u ^ 2 * e) / 2) = I.d := by
      rw [hXdef]; linear_combination (-1/4 : ℚ) * hB'
    have hX0 : X ≠ 0 := by intro h'; apply I.hd; rw [← hprod, h']; ring
    have hQ : (curve I.c I.d).Nonsingular X 0 :=
      nonsingular_of_eq I.hd I.hcd (by rw [hXdef]; linear_combination (-((-I.c + I.u ^ 2 * e) / 2) / 4) * hB')
    refine ⟨.some X 0 hQ, ?_⟩
    rw [I.phi_some_of_ne _ hX0]
    exact some_eq (by simp [imX, hx]) (by simp [imY, y_eq_zero_of_x_eq_zero h hx])
  · -- x = w²：Q = (X, -uwX)、X = (u²w² - c + u²y/w)/2
    rw [ite_eq_right hx] at hP
    obtain ⟨w, hw, hxw⟩ := eq_sq_of_cls_eq_one hx hP
    have e := curve_equation h
    rw [hxw] at e
    set X := (I.u ^ 2 * w ^ 2 - I.c + I.u ^ 2 * y / w) / 2 with hXdef
    have hprod := jKerProd I.hA I.hB e I.hu hw hXdef
    have hX0 : X ≠ 0 := by intro h'; apply I.hd; rw [← hprod, h']; ring
    have hQ : (curve I.c I.d).Nonsingular X (-I.u * w * X) :=
      nonsingular_of_eq I.hd I.hcd (jKerEq I.hA I.hB e I.hu hw hXdef)
    refine ⟨.some X _ hQ, ?_⟩
    rw [I.phi_some_of_ne _ hX0]
    refine some_eq ?_ (jKerY I.hA I.hB e I.hu hw hXdef hX0)
    simp only [imX]; rw [hxw]; field_simp

end Data

/-! ## `ψ ∘ φ = [2]` -/

/-- `φ : E → E'`（`u = 1`）。 -/
abbrev dataPhi (a b a' b' : ℚ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) (ha' : a' = -2 * a)
    (hb' : b' = a ^ 2 - 4 * b) : Data where
  c := a; d := b; A := a'; B := b'; u := 1
  hu := one_ne_zero; hd := hb; hcd := hab
  hA := by rw [ha']; ring
  hB := by rw [hb']; ring

/-- `ψ : E' → E`（`u = 2`）。 -/
abbrev dataPsi (a b a' b' : ℚ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) (ha' : a' = -2 * a)
    (hb' : b' = a ^ 2 - 4 * b) : Data where
  c := a'; d := b'; A := a; B := b; u := 2
  hu := two_ne_zero; hd := by rw [hb']; exact hab
  hcd := by rw [ha', hb']; ring_nf; exact mul_ne_zero hb (by norm_num)
  hA := by rw [ha']; ring
  hB := by rw [ha', hb']; ring

/-- **`ψ ∘ φ = [2]`**。 -/
theorem psi_phi {a b a' b' : ℚ} (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) (ha' : a' = -2 * a)
    (hb' : b' = a ^ 2 - 4 * b) (P : (curve a b).Point) :
    (dataPsi a b a' b' hb hab ha' hb').phi ((dataPhi a b a' b' hb hab ha' hb').phi P) = 2 • P := by
  rw [two_nsmul]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : x = 0
  · have hy := y_eq_zero_of_x_eq_zero h hx
    rw [(dataPhi a b a' b' hb hab ha' hb').phi_some_of_eq h hx, Point.add_of_Y_eq rfl (by simp [hy])]; rfl
  by_cases hy : y = 0
  · rw [(dataPhi a b a' b' hb hab ha' hb').phi_some_of_ne h hx, Point.add_of_Y_eq rfl (by simp [hy])]
    exact (dataPsi a b a' b' hb hab ha' hb').phi_some_of_eq _ (by simp [Data.imX, hy])
  have e := curve_equation h
  have hyy : y ≠ -y := fun h' => hy (by linear_combination h' / 2)
  have hxy : ¬(x = x ∧ y = (curve a b).negY x y) := by simpa using hyy
  rw [Point.add_some hxy, (dataPhi a b a' b' hb hab ha' hb').phi_some_of_ne h hx]
  have hX0 : (dataPhi a b a' b' hb hab ha' hb').imX x y ≠ 0 := by simp only [Data.imX]; positivity
  rw [(dataPsi a b a' b' hb hab ha' hb').phi_some_of_ne _ hX0]
  have hl : (curve a b).slope x x y y = (3 * x ^ 2 + 2 * a * x + b) / (2 * y) := by
    rw [slope_of_Y_ne (W := curve a b) rfl (by simpa using hyy)]
    simp only [curve_a₁, curve_a₂, curve_a₄, curve_negY, zero_mul, sub_zero]
    ring
  have hXd : (dataPhi a b a' b' hb hab ha' hb').imX x y = y ^ 2 / x ^ 2 := by simp [Data.imX]
  have hYd : (dataPhi a b a' b' hb hab ha' hb').imY x y = y * (b - x ^ 2) / x ^ 2 := by simp [Data.imY]
  refine some_eq ?_ ?_
  · have := jTwoX (l := (curve a b).slope x x y y) (x3 := (curve a b).slope x x y y ^ 2 - a - 2 * x)
      ha' hb' e hx hy hXd hYd hl rfl
    rw [curve_addX]
    simp only [Data.imX, Data.imY] at this ⊢
    linear_combination this
  · have := jTwoY (l := (curve a b).slope x x y y) (x3 := (curve a b).slope x x y y ^ 2 - a - 2 * x)
      ha' hb' e hx hy hXd hYd hl rfl
    rw [curve_addY]
    simp only [Data.imX, Data.imY] at this ⊢
    linear_combination this

end Mordell.Isogeny
