import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# 降下補題（Mordell の定理 Step 0）

`G` をアーベル群、`h : G → K`（`K` はアルキメデス的順序体、典型例は `ℝ`） を「高さ」とし、次を仮定する。

* (a) `h_fin`  : 各 `C` について `{P | h P ≤ C}` は有限
* (b) `h_add`  : 各 `Q` について定数 `c_Q` があり `h (P + Q) ≤ 2 h P + c_Q`
* (c) `h_dbl`  : 定数 `c` があり `4 h P - c ≤ h (2 • P)`
* (d) `G / 2G` が有限

このとき `G` は有限生成である。

(d) は二通りの形で与える：
* `descent_lemma` : 代表元の有限集合 `S` を明示する形
* `descent_lemma'` : 商群 `G ⧸ 2G` が `Finite` である形
-/

namespace Mordell

variable {G : Type*} [AddCommGroup G]
-- 高さの値域：アルキメデス的順序体（`ℝ` を含む）
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]

/-- 降下補題：`G / 2G` の代表元の有限集合 `S` が与えられた形。 -/
theorem descent_lemma (h : G → K)
    (h_fin : ∀ C : K, {P : G | h P ≤ C}.Finite)
    (h_add : ∀ Q : G, ∃ c : K, ∀ P : G, h (P + Q) ≤ 2 * h P + c)
    (h_dbl : ∃ c : K, ∀ P : G, 4 * h P - c ≤ h (2 • P))
    (S : Finset G) (hS : ∀ P : G, ∃ Q ∈ S, ∃ R : G, P = Q + 2 • R) :
    AddGroup.FG G := by
  choose cf hcf using h_add
  obtain ⟨c, hc⟩ := h_dbl
  -- c' ≥ c_{-Q} が全ての代表元 Q ∈ S で成り立つ一様な定数
  set c' : K := ∑ Q ∈ S, |cf (-Q)| with hc'
  have hc'_ge : ∀ Q ∈ S, cf (-Q) ≤ c' := fun Q hQ =>
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun Q => |cf (-Q)|) (fun _ _ => abs_nonneg _) hQ)
  set k : K := (c + c') / 4 with hk
  -- 生成系：代表元 S ∪ 高さが 2k+1 以下の点（有限集合）
  set B : Set G := {P | h P ≤ 2 * k + 1} with hB
  set H : AddSubgroup G := AddSubgroup.closure ((S : Set G) ∪ B) with hH
  -- 降下の一歩： P = Q + 2R なら h R ≤ h P / 2 + k
  have step : ∀ P Q R : G, Q ∈ S → P = Q + 2 • R → h R ≤ h P / 2 + k := by
    intro P Q R hQ hP
    have h1 := hc R
    have h2 : (2 • R) = P + -Q := by rw [hP]; abel
    rw [h2] at h1
    have h3 := hcf (-Q) P
    have h4 := hc'_ge Q hQ
    rw [hk]
    linarith
  -- 高さ ≤ 2k + 1 + n/2 の点は H に属する（n に関する帰納法）
  have main : ∀ n : ℕ, ∀ P : G, h P ≤ 2 * k + 1 + n / 2 → P ∈ H := by
    intro n
    induction n with
    | zero =>
      intro P hP
      apply AddSubgroup.subset_closure
      right
      show h P ≤ 2 * k + 1
      simpa using hP
    | succ n ih =>
      intro P hP
      by_cases hPB : h P ≤ 2 * k + 1
      · exact AddSubgroup.subset_closure (Or.inr hPB)
      · rw [not_le] at hPB
        obtain ⟨Q, hQ, R, rfl⟩ := hS P
        have hR := step _ Q R hQ rfl
        have hRH : R ∈ H := ih R (by push_cast at hP; linarith)
        exact H.add_mem (AddSubgroup.subset_closure (Or.inl hQ)) (H.nsmul_mem hRH 2)
  -- したがって H = ⊤
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro P _
    obtain ⟨n, hn⟩ := exists_nat_ge (2 * (h P - 2 * k - 1))
    exact main n P (by linarith)
  exact AddGroup.fg_iff.2 ⟨_, htop, S.finite_toSet.union (h_fin _)⟩

/-- `2G`：2 倍写像の像。 -/
abbrev twoG (G : Type*) [AddCommGroup G] : AddSubgroup G :=
  (nsmulAddMonoidHom 2 : G →+ G).range

/-- 降下補題：`G ⧸ 2G` が有限群である形（教科書の (d) そのもの）。 -/
theorem descent_lemma' (h : G → K)
    (h_fin : ∀ C : K, {P : G | h P ≤ C}.Finite)
    (h_add : ∀ Q : G, ∃ c : K, ∀ P : G, h (P + Q) ≤ 2 * h P + c)
    (h_dbl : ∃ c : K, ∀ P : G, 4 * h P - c ≤ h (2 • P))
    [Finite (G ⧸ twoG G)] :
    AddGroup.FG G := by
  classical
  -- 各剰余類の代表元を取る
  have hfin : (Set.range fun q : G ⧸ twoG G => q.out).Finite := Set.finite_range _
  refine descent_lemma h h_fin h_add h_dbl hfin.toFinset ?_
  intro P
  refine ⟨(P : G ⧸ twoG G).out, by simp, ?_⟩
  -- P - out ∈ 2G
  have hmem : -(P : G ⧸ twoG G).out + P ∈ twoG G :=
    QuotientAddGroup.leftRel_apply.mp (Quotient.exact' (QuotientAddGroup.out_eq' (P : G ⧸ twoG G)))
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, ?_⟩
  simp only [nsmulAddMonoidHom_apply] at hR
  rw [hR]
  abel

end Mordell
