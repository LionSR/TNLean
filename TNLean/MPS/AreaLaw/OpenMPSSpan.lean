/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite spans of open-boundary matrix product states

A vector in the span of a finite set of matrix product states of bond dimension at most
`D` has bond dimension at most the cardinality of the set times `D`. The estimate follows
from subadditivity of the ranks of the coefficient matrices at each internal cut.

This is the finite-span estimate used in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`, lines 520–527. It is independent of the
Hamiltonian and of any choice of a viable witness.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

/-- A vector in the span of `S` has bond dimension at most `S.card * D` if each member of
`S` has bond dimension at most `D`. This is the finite-span estimate in LVV13,
`algo53.tex`, Claim `c:2`, lines 520–527. No normalization or positivity of `D` is required. -/
theorem isOpenMPS_of_mem_span {L q D : ℕ}
    (S : Finset ((Fin L → Fin q) → ℂ))
    (hS : ∀ w ∈ S, IsOpenMPS L q D w) {v : (Fin L → Fin q) → ℂ}
    (hv : v ∈ Submodule.span ℂ (S : Set ((Fin L → Fin q) → ℂ))) :
    IsOpenMPS L q (S.card * D) v := by
  classical
  obtain ⟨a, -, rfl⟩ := Submodule.mem_span_finset.mp hv
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le
    (WithLp.toLp 2 (∑ w ∈ S, a w • w))).mpr
  intro k hk0 hkL
  let A := fun w : (Fin L → Fin q) → ℂ ↦ a w • cutMatrix (WithLp.toLp 2 w) k
  have hcut : cutMatrix (WithLp.toLp 2 (∑ w ∈ S, a w • w)) k = ∑ w ∈ S, A w := by
    ext p r
    simp [A, cutMatrix_apply, Finset.sum_apply, Matrix.sum_apply]
  rw [hcut]
  have hA (w) (hw : w ∈ S) : (A w).rank ≤ D := by
    by_cases ha : a w = 0
    · simp [A, ha]
    · simpa only [A, rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero ha)] using
        (hS w hw).rank_cutMatrix_le (ψ := WithLp.toLp 2 w) hk0 hkL
  have hr := LinearMap.rank_finsetSum_le S (fun w ↦ Matrix.toLin' (A w))
  have hcard (w) (hw : w ∈ S) : (Matrix.toLin' (A w)).rank ≤ (D : Cardinal) := by
    rw [LinearMap.rank, ← Module.finrank_eq_rank', Matrix.toLin'_apply']
    exact_mod_cast hA w hw
  have hsum : (∑ w ∈ S, Matrix.toLin' (A w)).rank ≤
      ((S.card * D : ℕ) : Cardinal) := by
    simpa using hr.trans (Finset.sum_le_sum hcard)
  rw [← map_sum] at hsum
  convert (Cardinal.toNat_le_toNat hsum Cardinal.natCast_lt_aleph0) using 1
  all_goals simp only [Matrix.rank, Module.finrank, LinearMap.rank,
    Matrix.toLin'_apply', Cardinal.toNat_natCast]
  congr 3

end TNLean.MPS.AreaLaw
