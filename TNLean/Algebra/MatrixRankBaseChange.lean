/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank under scalar extension

This file proves rank invariance for finite matrices under scalar extension.

## Main results

* `Matrix.rank_map_algebraMap`: extending scalars along a faithful field
  extension preserves the rank of a finite matrix.
-/

open Matrix Module Submodule Set

namespace Matrix

variable {K m n : Type*} [Field K] [Fintype n]

variable [Finite m]

/-- Extending scalars along a faithful field extension does not change the rank
of a finite matrix. -/
theorem rank_map_algebraMap {L : Type*}
    [Field L] [Algebra K L] [FaithfulSMul K L]
    (A : Matrix m n K) :
    (A.map (algebraMap K L)).rank = A.rank := by
  classical
  have hli (s : ℕ) (j : Fin s → n) :
      LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) ↔
        LinearIndependent K (fun i ↦ A.col (j i)) := by
    have hcols :
        (fun i ↦ (A.map (algebraMap K L)).col (j i)) =
          (fun i ↦ (algebraMap K L) ∘ A.col (j i)) := by
      funext i x
      rfl
    rw [hcols]
    exact linearIndependent_algebraMap_comp_iff
  apply le_antisymm
  · rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨v, hv_mem, _, hv_ind⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq L
        (Set.range (A.map (algebraMap K L)).col)
    choose j hj using hv_mem
    have hselectedL :
        LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) := by
      rw [funext hj]
      exact hv_ind
    have hselectedK : LinearIndependent K (fun i ↦ A.col (j i)) :=
      (hli _ j).mp hselectedL
    have hrange : Set.range (fun i ↦ A.col (j i)) ⊆ Set.range A.col := by
      rintro _ ⟨i, rfl⟩
      exact ⟨j i, rfl⟩
    simpa using (linearIndependent_iff_card_le_finrank_span.mp hselectedK).trans
      (Submodule.finrank_mono (Submodule.span_mono hrange))
  · rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨v, hv_mem, _, hv_ind⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
    choose j hj using hv_mem
    have hselectedK : LinearIndependent K (fun i ↦ A.col (j i)) := by
      rw [funext hj]
      exact hv_ind
    have hselectedL :
        LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) :=
      (hli _ j).mpr hselectedK
    have hrange :
        Set.range (fun i ↦ (A.map (algebraMap K L)).col (j i)) ⊆
          Set.range (A.map (algebraMap K L)).col := by
      rintro _ ⟨i, rfl⟩
      exact ⟨j i, rfl⟩
    simpa using (linearIndependent_iff_card_le_finrank_span.mp hselectedL).trans
      (Submodule.finrank_mono (Submodule.span_mono hrange))

end Matrix
