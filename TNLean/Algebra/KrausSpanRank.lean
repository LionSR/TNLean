/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausRank
import QICLean.Kraus.WordSpan

/-!
# Choi rank and the one-letter Kraus span

The rank of the Choi matrix of a finite Kraus map is the dimension of the
linear span of its Kraus operators. This identifies the channel-theoretic
Kraus rank with the one-letter word-span dimension used in tensor networks.
-/

open scoped Matrix BigOperators ComplexOrder Pointwise
open Matrix

namespace Channel

private theorem rank_sum_vecMulVec_eq_finrank_span
    {n ι : Type*} [Fintype n] [Fintype ι] (v : ι → n → ℂ) :
    (∑ i : ι, Matrix.vecMulVec (v i) (star (v i))).rank =
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  classical
  let C : Matrix n ι ℂ := fun p i ↦ v i p
  have hsum :
      ∑ i : ι, Matrix.vecMulVec (v i) (star (v i)) = C * Cᴴ := by
    ext p q
    rw [Matrix.sum_apply, Matrix.mul_apply]
    rfl
  rw [hsum, Matrix.rank_self_mul_conjTranspose, Matrix.rank_eq_finrank_span_cols]
  rfl

/-- The Choi rank of a finite Kraus map equals the dimension of the span of
its Kraus operators. The normalization of the Choi matrix has no effect on
rank, including when the matrix algebra has dimension zero. -/
theorem choiRank_mapLM_eq_finrank_span {r D : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    choiRank (Kraus.mapLM K) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range K)) := by
  classical
  by_cases hD : D = 0
  · subst D
    have hchoi : ChoiJamiolkowski.choiMatrix (Kraus.mapLM K) = 0 :=
      Subsingleton.elim _ _
    have hspan : Submodule.span ℂ (Set.range K) = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        rw [Subsingleton.elim (K j) 0]
        exact Submodule.zero_mem _
      · exact bot_le
    change (ChoiJamiolkowski.choiMatrix (Kraus.mapLM K)).rank = _
    rw [hchoi, Matrix.rank_zero, hspan]
    simp
  · let c : ℂ := 1 / ((D : ℝ).sqrt : ℂ)
    let v : Fin r → (Fin D × Fin D → ℂ) :=
      fun j p ↦ c * K j p.1 p.2
    have hc : c ≠ 0 := by
      dsimp [c]
      have hDpos : 0 < D := Nat.pos_of_ne_zero hD
      have hsqrt : Real.sqrt (D : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (by exact_mod_cast hDpos)
      simp [hsqrt]
    change (ChoiJamiolkowski.choiMatrix (Kraus.mapLM K)).rank = _
    rw [choiMatrix_mapLM_eq_sum_vecMulVec]
    change (∑ j : Fin r, Matrix.vecMulVec (v j) (star (v j))).rank = _
    rw [rank_sum_vecMulVec_eq_finrank_span]
    let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] (Fin D × Fin D → ℂ) :=
      (LinearEquiv.curry ℂ ℂ (Fin D) (Fin D)).symm
    have hv : v = fun j ↦ c • e (K j) := by
      funext j p
      rfl
    rw [hv]
    have hrange : Set.range (fun j ↦ c • e (K j)) =
        c • Set.range (fun j ↦ e (K j)) := by
      ext x
      simp only [Set.mem_range, Set.mem_smul_set]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e (K j), ⟨j, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
    rw [hrange, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hc)]
    have hmap : (Submodule.span ℂ (Set.range K)).map (e : _ →ₗ[ℂ] _) =
        Submodule.span ℂ (Set.range (fun j ↦ e (K j))) := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp
    rw [← hmap, e.finrank_map_eq]

/-- The Choi rank of a finite Kraus map is the dimension of its exact
one-letter word span. -/
theorem choiRank_mapLM_eq_finrank_wordSpan_one {r D : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    choiRank (Kraus.mapLM K) = Module.finrank ℂ (Kraus.wordSpan K 1) := by
  rw [choiRank_mapLM_eq_finrank_span, Kraus.wordSpan_one]

end Channel
