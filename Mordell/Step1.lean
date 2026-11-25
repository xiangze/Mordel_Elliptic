import Mathlib.NumberTheory.Height.EllipticCurve
import Mordell.Descent

/-!
# Mordell の定理 Step 1：naive height の性質 (a)(b)(c)

Mathlib の楕円曲線の有理点群 `W.Point`（本物の群構造）と、
Mathlib の naive height `P.naiveHeight = logHeight (x(P) : 1)`（`x(P) = m/n` なら `log max(|m|,|n|)`）
について、教科書 Step 1 の 3 性質を示す。

* (a) `finite_height_le`    : `{P | h P ≤ B}` は有限
* (b) `height_add_le`       : `h (P + Q) ≤ 2 h P + c_Q`
* (c) `height_two_smul_ge`  : `4 h P - c ≤ h (2 • P)`

体 `F` は高さの理論を持つ体（`AdmissibleAbsValues F`）とし、(a) には Northcott 性を仮定する。
`F = ℚ`（およびすべての数体）はこれらの仮定を満たす：
インスタンスは `Mathlib.NumberTheory.Height.NumberField` にある。

(b)(c) は Mathlib の **近似平行四辺形則**（M. Stoll, 2026）
  `|h(P+Q) + h(P-Q) - 2(h P + h Q)| ≤ C`
から導く。その証明の中身は、加法・減法写像 `addSubMap : ℙ² → ℙ²` が射であること
（教科書での「倍点公式の分子・分母に終結式を当てる」議論の一般化）である。

最後に Step 0（`Mordell.Descent` の `descent_lemma'`）と組み合わせ、
**弱 Mordell–Weil（`W(F)/2W(F)` が有限）を仮定すれば `W(F)` は有限生成**
であることを、Mathlib の本物の点群に対して示す。
-/

namespace Mordell.Step1

open WeierstrassCurve.Affine Height

variable {F : Type*} [Field F] [AdmissibleAbsValues F] (W : WeierstrassCurve.Affine F)

/-- naive height は非負。 -/
lemma naiveHeight_nonneg (P : W.Point) : 0 ≤ P.naiveHeight :=
  logHeight_nonneg _

/-- 有限遠点 `O` の高さは 0（`xRep O = (1 : 0)`）。 -/
lemma naiveHeight_zero : (0 : W.Point).naiveHeight = 0 := by
  simp [Point.naiveHeight_eq_logHeight₁, Point.xRep]

variable [DecidableEq F] [W.IsElliptic]

/-- **(b)** 各 `Q` について定数 `c_Q` があり、`h (P + Q) ≤ 2 h P + c_Q`。 -/
theorem height_add_le :
    ∀ Q : W.Point, ∃ c : ℝ, ∀ P : W.Point, (P + Q).naiveHeight ≤ 2 * P.naiveHeight + c := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  intro Q
  refine ⟨2 * Q.naiveHeight + C, fun P => ?_⟩
  have h1 := (abs_le.mp (hC P Q)).2
  have h2 := naiveHeight_nonneg W (P - Q)
  linarith

/-- **(c)** 定数 `c` があり、`4 h P - c ≤ h (2 • P)`。 -/
theorem height_two_smul_ge :
    ∃ c : ℝ, ∀ P : W.Point, 4 * P.naiveHeight - c ≤ (2 • P).naiveHeight := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨C, fun P => ?_⟩
  have h1 := (abs_le.mp (hC P P)).1
  rw [sub_self, naiveHeight_zero, ← two_nsmul] at h1
  linarith

variable [Northcott (logHeight₁ (K := F))]

omit [DecidableEq F] [W.IsElliptic] in
/-- **(a)** 高さが `B` 以下の点は有限個。 -/
theorem finite_height_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  finite_naiveHeight_le W B

/-- **Step 0 + Step 1**：弱 Mordell–Weil（`W(F) ⧸ 2W(F)` が有限）を仮定すると、
`W(F)` は有限生成。昨日の降下補題 `descent_lemma'`（値域 `K = ℝ`）を使う。 -/
theorem fg_of_finite_quotient_two [Finite (W.Point ⧸ twoG W.Point)] : AddGroup.FG W.Point :=
  descent_lemma' (K := ℝ) (fun P : W.Point => P.naiveHeight)
    (finite_height_le W) (height_add_le W) (height_two_smul_ge W)

/-- 同じ結論を Mathlib 自身の降下定理 `AddCommGroup.fg_of_descent'` から得る版（照合用）。 -/
theorem fg_of_finite_quotient_two' [Finite (W.Point ⧸ twoG W.Point)] : AddGroup.FG W.Point := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  have : (twoG W.Point).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact AddCommGroup.fg_of_descent' this (naiveHeight_nonneg W) hC

end Mordell.Step1
