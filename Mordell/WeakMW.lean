import Mordell.Isogeny
import Mordell.Step1

/-!
# 弱 Mordell–Weil と Mordell の定理（位数 2 の有理点を持つ曲線）

## (3) 群論的な部分：`finite_reps_two`
アーベル群 `Γ, Γ'` と
* 加法的な `ψ : Γ' →+ Γ`、写像 `φ : Γ → Γ'` で `ψ (φ P) = 2 • P`
* 準同型 `α : Γ →+ A`、`α' : Γ' →+ A'` で像が有限、
  `ker α ⊆ ψ(Γ')`、`ker α' ⊆ φ(Γ)`

があれば、`Γ / 2Γ` の有限代表系が存在する。
（教科書の `[Γ : 2Γ] ≤ [Γ : ψΓ'] [Γ' : φΓ] = |α(Γ)| |α'(Γ')|` の代表元版）

## 結論
* `weak_mordell_weil` : `E : y² = x³ + ax² + bx`（`a, b ∈ ℤ`, `b ≠ 0`, `a² - 4b ≠ 0`）について
  `E(ℚ) / 2E(ℚ)` の有限代表系が存在する
* `mordell` : `E(ℚ)` は有限生成（ℚ の高さの公理系と Northcott 性をインスタンス引数とする）
-/

namespace Mordell.Weak

/-! ## (3) 群論 -/

section GroupTheory

variable {Γ Γ' A A' : Type*} [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup A] [AddCommGroup A']

/-- 像が有限な準同型 `α` について、`α` の値ごとに代表元を 1 つずつ取った有限集合。 -/
lemma exists_reps (α : Γ →+ A) (hfin : (Set.range α).Finite) :
    ∃ R : Finset Γ, ∀ P : Γ, ∃ r ∈ R, α (P - r) = 0 := by
  classical
  have : Finite (Set.range α) := hfin.to_subtype
  have : Fintype (Set.range α) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun v : Set.range α => v.2.choose, fun P => ?_⟩
  refine ⟨(⟨α P, P, rfl⟩ : Set.range α).2.choose,
    Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [map_sub, (⟨α P, P, rfl⟩ : Set.range α).2.choose_spec, sub_self]

/-- **(3)** 2-同種写像の組から `Γ / 2Γ` の有限代表系を得る。 -/
theorem finite_reps_two (φ : Γ → Γ') (ψ : Γ' →+ Γ) (hψφ : ∀ P, ψ (φ P) = 2 • P)
    (α : Γ →+ A) (α' : Γ' →+ A')
    (hker : ∀ P, α P = 0 → ∃ P', ψ P' = P) (hker' : ∀ P', α' P' = 0 → ∃ P, φ P = P')
    (hfin : (Set.range α).Finite) (hfin' : (Set.range α').Finite) :
    ∃ S : Finset Γ, ∀ P : Γ, ∃ Q ∈ S, ∃ R : Γ, P = Q + 2 • R := by
  classical
  obtain ⟨R, hR⟩ := exists_reps α hfin
  obtain ⟨R', hR'⟩ := exists_reps α' hfin'
  refine ⟨(R ×ˢ R').image (fun p => p.1 + ψ p.2), fun P => ?_⟩
  obtain ⟨r, hr, hα⟩ := hR P
  obtain ⟨P', hP'⟩ := hker _ hα          -- P - r = ψ P'
  obtain ⟨r', hr', hα'⟩ := hR' P'
  obtain ⟨Q, hQ⟩ := hker' _ hα'          -- P' - r' = φ Q
  refine ⟨r + ψ r', Finset.mem_image.mpr ⟨(r, r'), Finset.mem_product.mpr ⟨hr, hr'⟩, rfl⟩, Q, ?_⟩
  -- P = r + ψ P' = r + ψ r' + ψ (φ Q) = r + ψ r' + 2Q
  have h1 : P = r + ψ P' := by rw [hP']; abel
  have h2 : P' = r' + φ Q := by rw [hQ]; abel
  rw [h1, h2, map_add, hψφ, add_assoc]

end GroupTheory

/-! ## 組み立て -/

open WeierstrassCurve WeierstrassCurve.Affine Mordell.Step2 Mordell.Isogeny

lemma alphaHom_eq_zero {a b : ℚ} (hb : b ≠ 0) (P : (curve a b).Point) :
    alphaHom hb P = 0 ↔ alpha a b P = 1 := by
  change Additive.ofMul (alpha a b P) = 0 ↔ _
  exact ofMul_eq_zero

lemma finite_range_alphaHom {a b : ℤ} (hb : (b : ℚ) ≠ 0) (hb' : b ≠ 0) :
    (Set.range (alphaHom (a := (a : ℚ)) hb)).Finite := by
  have := (finite_range_alpha (a := a) hb').image Additive.ofMul
  refine this.subset ?_
  rintro _ ⟨P, rfl⟩
  exact ⟨alpha (a : ℚ) b P, ⟨P, rfl⟩, rfl⟩

/-- **弱 Mordell–Weil の定理**（位数 2 の有理点を持つ曲線）：
`E(ℚ) / 2E(ℚ)` の有限代表系が存在する。 -/
theorem weak_mordell_weil (a b : ℤ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) :
    ∃ S : Finset (curve (a : ℚ) b).Point,
      ∀ P : (curve (a : ℚ) b).Point, ∃ Q ∈ S, ∃ R, P = Q + 2 • R := by
  -- E' : y² = x³ + a' x² + b' x、a' = -2a、b' = a² - 4b（整数）
  set a' : ℤ := -2 * a with ha'
  set b' : ℤ := a ^ 2 - 4 * b with hb'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have habq : (a : ℚ) ^ 2 - 4 * b ≠ 0 := by exact_mod_cast hab
  have ha'q : (a' : ℚ) = -2 * a := by rw [ha']; push_cast; ring
  have hb'q : (b' : ℚ) = a ^ 2 - 4 * b := by rw [hb']; push_cast; ring
  have hb'0 : b' ≠ 0 := hab
  have hb'q0 : (b' : ℚ) ≠ 0 := by exact_mod_cast hb'0
  let I₁ := dataPhi (a : ℚ) b a' b' hbq habq ha'q hb'q
  let I₂ := dataPsi (a : ℚ) b a' b' hbq habq ha'q hb'q
  exact finite_reps_two (A := Additive (SqClass ℚ)) (A' := Additive (SqClass ℚ))
    I₁.phi I₂.phiHom (psi_phi hbq habq ha'q hb'q)
    (alphaHom hbq) (alphaHom hb'q0)
    (fun P hP => I₂.exists_phi_eq_of_alpha_eq_one P ((alphaHom_eq_zero hbq P).mp hP))
    (fun P' hP' => I₁.exists_phi_eq_of_alpha_eq_one P' ((alphaHom_eq_zero hb'q0 P').mp hP'))
    (finite_range_alphaHom hbq hb) (finite_range_alphaHom hb'q0 hb'0)

/-- **Mordell の定理**（位数 2 の有理点を持つ曲線 `y² = x³ + ax² + bx`）：
`E(ℚ)` は有限生成アーベル群。

`ℚ` の高さの公理系 `AdmissibleAbsValues ℚ` と Northcott 性はインスタンス引数とした。
どちらも Mathlib の `Mathlib.NumberTheory.Height.NumberField` に（数体一般の）インスタンスがある。 -/
theorem mordell [Height.AdmissibleAbsValues ℚ] [Northcott (Height.logHeight₁ (K := ℚ))]
    (a b : ℤ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ≠ 0) :
    AddGroup.FG (curve (a : ℚ) b).Point := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have habq : (a : ℚ) ^ 2 - 4 * b ≠ 0 := by exact_mod_cast hab
  have := isElliptic_curve hbq habq
  obtain ⟨S, hS⟩ := weak_mordell_weil a b hb hab
  exact descent_lemma (K := ℝ) (fun P => P.naiveHeight)
    (Step1.finite_height_le _) (Step1.height_add_le _) (Step1.height_two_smul_ge _) S hS

end Mordell.Weak
