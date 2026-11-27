/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.OpenMPS.OpenMPSCutRank
import QICLean.ManyBody.Entropy.Cut.RegionRank
import QICLean.Channel.Schmidt.MaximalOverlap
import QICLean.ManyBody.Entropy.Cut.RegionTraceNorm

/-!
# Rank of a reduced state of an open-boundary matrix product state

The reduced density matrix at an internal cut has rank at most the bond dimension.
No normalization is required. This is the rank estimate in the proof of
Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, Eq. (eps-lower), lines 247–264.
-/

open scoped ComplexOrder
open ManyBody (cutMatrix interval mem_interval)

namespace TNLean.MPS.AreaLaw

/-- The reduced state at an internal cut of an open-boundary MPS has rank at
most its bond dimension. Source: SWVC08, arXiv:0705.0292v2,
Eq. (eps-lower), lines 247–264. -/
theorem IsOpenMPS.rank_regionState_interval_le {L q D : ℕ}
    {φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    (ManyBody.regionState (X := fun _ ↦ Fin q) φ (interval L 0 k)).rank ≤ D := by
  rw [ManyBody.rank_regionState_eq_cutRank]
  exact hφ.rank_cutMatrix_le hk0 hkL

/-- Taking a reduced state at a chain cut cannot increase the full trace-norm
error of two pure states, without normalization assumptions.
Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower), lines 247–264. -/
theorem rectangularTraceNorm_regionState_interval_sub_le {L q : ℕ}
    (ψ φ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ) :
    Matrix.rectangularTraceNorm
      (ManyBody.regionState (X := fun _ ↦ Fin q) ψ (interval L 0 k) -
        ManyBody.regionState (X := fun _ ↦ Fin q) φ (interval L 0 k)) ≤
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) := by
  exact Entropy.rectangularTraceNorm_regionState_sub_le ψ φ (interval L 0 k)

/-- A block strictly between two chain cuts has reduced-state rank at most the
square of the bond dimension. No normalization is required. This is an elementary
consequence of the single-cut bound in SWVC08, arXiv:0705.0292v2, lines 247–264. -/
theorem IsOpenMPS.rank_regionState_sdiff_interval_le_sq {L q D : ℕ}
    {φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < L) :
    (ManyBody.regionState (X := fun _ ↦ Fin q)
      φ (interval L 0 b \ interval L 0 a)).rank ≤ D ^ 2 := by
  have hsub : interval L 0 a ⊆ interval L 0 b :=
    fun _ hi ↦ mem_interval.mpr ⟨Nat.zero_le _, (mem_interval.mp hi).2.trans_le hab⟩
  simpa only [pow_two] using (Entropy.rank_regionState_sdiff_le φ hsub).trans
    (Nat.mul_le_mul (hφ.rank_regionState_interval_le ha (hab.trans_lt hb))
      (hφ.rank_regionState_interval_le (ha.trans_le hab) hb))

/-- Every prefix reduction has rank at most the larger of one and the bond
budget, including the two endpoint cuts and chains of length zero or one.
This is an elementary consequence of the internal-cut bound and endpoint ranks. -/
theorem IsOpenMPS.rank_regionState_interval_le_max {L q D : ℕ}
    {φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (k : ℕ) :
    (ManyBody.regionState (X := fun _ ↦ Fin q) φ (interval L 0 k)).rank ≤ max 1 D := by
  have hcut : (cutMatrix (interval L 0 k) φ).rank ≤ max 1 D := by
    by_cases hk0 : k = 0
    · subst k
      exact (rank_cutMatrix_zero_le φ).trans (le_max_left _ _)
    by_cases hkL : L ≤ k
    · exact (rank_cutMatrix_le_one_of_le hkL φ).trans (le_max_left _ _)
    exact (hφ.rank_cutMatrix_le (Nat.pos_of_ne_zero hk0) (Nat.lt_of_not_ge hkL)).trans
      (le_max_right _ _)
  rw [ManyBody.rank_regionState_eq_cutRank]
  exact hcut

/-- The rank bound for an arbitrary contiguous block, including endpoint cuts,
empty blocks, and chains of length zero or one. This is an elementary consequence
of equality of complementary ranks and the product bound for disjoint regions. -/
theorem IsOpenMPS.rank_regionState_sdiff_interval_le_max_sq {L q D : ℕ}
    {φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) {a b : ℕ} (hab : a ≤ b) :
    (ManyBody.regionState (X := fun _ ↦ Fin q)
      φ (interval L 0 b \ interval L 0 a)).rank ≤ (max 1 D) ^ 2 := by
  have hsub : interval L 0 a ⊆ interval L 0 b :=
    fun _ hi ↦ mem_interval.mpr ⟨Nat.zero_le _, (mem_interval.mp hi).2.trans_le hab⟩
  simpa only [pow_two] using (Entropy.rank_regionState_sdiff_le φ hsub).trans
    (Nat.mul_le_mul (hφ.rank_regionState_interval_le_max a)
      (hφ.rank_regionState_interval_le_max b))

end TNLean.MPS.AreaLaw
