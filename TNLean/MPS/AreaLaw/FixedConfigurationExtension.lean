/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.SupportedMarginalTails
import TNLean.MPS.AreaLaw.OpenMPSCutRank

/-!
# Extension by a fixed exterior configuration

A state on a contiguous interval extends to the full chain by fixing a basis
configuration on its complement. At each cut, the extended coefficient matrix
is obtained from the corresponding interior coefficient matrix by the two
configuration restriction maps and by diagonal matching indicators. Its rank
is therefore at most the interior cut rank. Cuts outside the interval have
rank at most one.

Consequently an interior bond bound `D` gives the full-chain bound `max 1 D`.
The maximum accounts for empty and one-site intervals, whose internal bond
conditions allow `D = 0` even for a nonzero state.
-/

namespace TNLean.MPS.AreaLaw

/-- Extend an interval state by a fixed configuration on its complement, with
open-boundary bond bound `max 1 D`. The cut-rank argument also includes empty
and one-site intervals. This is elementary cut-movement algebra used in ALVV,
arXiv:1602.08828v2, Proposition 5.7, `prop:Cheby-AGSP-eff`, line 1332. -/
theorem IsOpenMPS.extend_interval_by_configuration {T L q D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) :
    IsOpenMPS T q (max 1 D) (fun σ ↦
      if (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η
      then ψ (fun r : Fin L ↦ σ ⟨a + r.val, by omega⟩) else 0) := by
  classical
  let χ : EuclideanSpace ℂ (Fin T → Fin q) := WithLp.toLp 2 fun σ ↦
    if (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η
    then ψ (fun r : Fin L ↦ σ ⟨a + r.val, by omega⟩) else 0
  change IsOpenMPS T q (max 1 D) (fun σ ↦ χ σ)
  apply isOpenMPS_of_internal_cutMatrix_rank_le χ
  intro j _ _
  let k := min L (j - a)
  have hcut (r : Fin L) : r.val < k ↔ a + r.val < j := by
    change r.val < min L (j - a) ↔ a + r.val < j
    rw [lt_min_iff]
    omega
  let f : ((v : {v : Fin T // v ∈ leftBlock T j}) → Fin q) →
      ((v : {v : Fin L // v ∈ leftBlock L k}) → Fin q) := fun x r ↦
    x ⟨⟨a + r.val.val, by omega⟩,
      mem_leftBlock.mpr ((hcut r.val).mp (mem_leftBlock.mp r.property))⟩
  let g : ((v : {v : Fin T // v ∉ leftBlock T j}) → Fin q) →
      ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) := fun y r ↦
    y ⟨⟨a + r.val.val, by omega⟩, by
      intro hr
      exact r.property (mem_leftBlock.mpr ((hcut r.val).mpr (mem_leftBlock.mp hr)))⟩
  let P := fun x : ((v : {v : Fin T // v ∈ leftBlock T j}) → Fin q) ↦
    ∀ (v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)})
      (hv : v.val ∈ leftBlock T j), x ⟨v.val, hv⟩ = η v
  let Q := fun y : ((v : {v : Fin T // v ∉ leftBlock T j}) → Fin q) ↦
    ∀ (v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)})
      (hv : v.val ∉ leftBlock T j), y ⟨v.val, hv⟩ = η v
  let u := fun x ↦ if P x then (1 : ℂ) else 0
  let v := fun y ↦ if Q y then (1 : ℂ) else 0
  let M := (cutMatrix ψ k).submatrix f g
  have hfactor : cutMatrix χ j = Matrix.diagonal u * M * Matrix.diagonal v := by
    ext x y
    have hmatch :
        (fun w : {w : Fin T // ¬(a ≤ w.val ∧ w.val < a + L)} ↦
          (Entropy.cutEquiv (fun _ : Fin T ↦ q) (leftBlock T j)).symm (x, y) w.val) = η
        ↔ P x ∧ Q y := by
      constructor
      · intro h
        constructor
        · intro w hw
          have he := congrFun h w
          rw [Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin T ↦ q) x y hw] at he
          exact he
        · intro w hw
          have he := congrFun h w
          rw [Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin T ↦ q) x y hw] at he
          exact he
      · rintro ⟨hp, hq⟩
        funext w
        by_cases hw : w.val ∈ leftBlock T j
        · rw [Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin T ↦ q) x y hw]
          exact hp w hw
        · rw [Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin T ↦ q) x y hw]
          exact hq w hw
    have hcore :
        (fun r : Fin L ↦
          (Entropy.cutEquiv (fun _ : Fin T ↦ q) (leftBlock T j)).symm (x, y)
            ⟨a + r.val, by omega⟩) =
          (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm (f x, g y) := by
      funext r
      by_cases hr : r ∈ leftBlock L k
      · have hv : (⟨a + r.val, by omega⟩ : Fin T) ∈ leftBlock T j :=
          mem_leftBlock.mpr ((hcut r).mp (mem_leftBlock.mp hr))
        rw [Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin T ↦ q) x y hv,
          Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin L ↦ q) (f x) (g y) hr]
      · have hv : (⟨a + r.val, by omega⟩ : Fin T) ∉ leftBlock T j := by
          intro hv
          exact hr (mem_leftBlock.mpr ((hcut r).mpr (mem_leftBlock.mp hv)))
        rw [Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin T ↦ q) x y hv,
          Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin L ↦ q) (f x) (g y) hr]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, cutMatrix_apply]
    change (if
      (fun w : {w : Fin T // ¬(a ≤ w.val ∧ w.val < a + L)} ↦
        (Entropy.cutEquiv (fun _ : Fin T ↦ q) (leftBlock T j)).symm (x, y) w.val) = η
      then ψ (fun r : Fin L ↦
        (Entropy.cutEquiv (fun _ : Fin T ↦ q) (leftBlock T j)).symm (x, y)
          ⟨a + r.val, by omega⟩) else 0) =
        (if P x then 1 else 0) * (cutMatrix ψ k) (f x) (g y) * (if Q y then 1 else 0)
    simp only [hmatch, hcore, cutMatrix_apply]
    by_cases hp : P x <;> by_cases hq : Q y <;> simp [hp, hq]
  have hrank : (cutMatrix χ j).rank ≤ (cutMatrix ψ k).rank := by
    rw [hfactor]
    exact ((Matrix.rank_mul_le_left (Matrix.diagonal u * M) (Matrix.diagonal v)).trans
      (Matrix.rank_mul_le_right (Matrix.diagonal u) M)).trans
        (Matrix.rank_submatrix_le (cutMatrix ψ k) f g)
  apply hrank.trans
  by_cases hk0 : k = 0
  · rw [hk0]
    exact (rank_cutMatrix_zero_le ψ).trans (le_max_left 1 D)
  · by_cases hkL : L ≤ k
    · exact (rank_cutMatrix_le_one_of_le hkL ψ).trans (le_max_left 1 D)
    · exact (hψ.rank_cutMatrix_le (Nat.pos_of_ne_zero hk0) (lt_of_not_ge hkL)).trans
        (le_max_right 1 D)

end TNLean.MPS.AreaLaw
