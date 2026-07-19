/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.SectorTrace

/-!
# Marginal stability from source zero correlation length

This file isolates the finite-chain consequence of source zero correlation
length used in the converse commuting-form argument of Appendix C.2 of
arXiv:1606.00608.  If the physical-trace transfer satisfies
`E * E = lambda * E`, then tracing two sites from a chain of length `N + 2`
gives the same normalized `N`-site marginal as tracing one site from a chain
of length `N + 1`.

This statement does not assert the rank-one trace factorization printed later
at source line 1613 and does not construct a quantum Markov decomposition.

## Main results

* `MPOTensor.reducedBlockState_apply_eq_trace_evalWord_mul_verticalLoop_pow`
* `MPOTensor.reducedBlockState_succ_succ_eq_succ_of_isSourceZCL`
* `MPOTensor.reducedBlockState_add_three_eq_succ_of_isSourceZCL`

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, line 1613
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- A contiguous reduced-state entry is the normalized trace of the retained
word followed by the appropriate power of the physical-trace transfer.

Source: arXiv:1606.00608, Appendix C.2, line 1613. -/
theorem reducedBlockState_apply_eq_trace_evalWord_mul_verticalLoop_pow
    (M : MPOTensor d D) {N L : ℕ} (hL : L ≤ N)
    (u v : Fin L → Fin d) :
    M.reducedBlockState N L hL u v =
      (mpo M N).trace⁻¹ *
        Matrix.trace
          (M.evalWord (List.ofFn u) (List.ofFn v) * M.verticalLoop ^ (N - L)) := by
  rw [reducedBlockState_eq_sum]
  simp only [normalizedMPO, Matrix.smul_apply, smul_eq_mul, mpo_apply, mpoMatrixEntry]
  rw [← Finset.mul_sum]
  congr 1
  have hwords (a : Fin L → Fin d) (w : Fin (N - L) → Fin d) :
      List.ofFn
          (Fin.append a w ∘ Fin.cast (show N = L + (N - L) by omega)) =
        List.ofFn a ++ List.ofFn w := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (Nat.add_sub_of_le hL) (Fin.append a w)).symm
  simp_rw [hwords]
  have heval (w : Fin (N - L) → Fin d) :
      M.evalWord (List.ofFn u ++ List.ofFn w) (List.ofFn v ++ List.ofFn w) =
        M.evalWord (List.ofFn u) (List.ofFn v) *
          M.evalWord (List.ofFn w) (List.ofFn w) := by
    exact M.evalWord_append _ _ _ _ (by simp)
  simp_rw [heval]
  rw [← Matrix.trace_sum]
  congr 1
  rw [← Finset.mul_sum, M.sum_evalWord_diag_eq_verticalLoop_pow]

/-- Under source zero correlation length, tracing two sites from length
`N + 2` gives the same normalized `N`-site marginal as tracing one site from
length `N + 1`.

This is the valid ZCL replacement at the beginning of the argument at source
line 1613.  It does not imply that the neighboring trace matrix has rank one.

Source: arXiv:1606.00608, Appendix C.2, line 1613. -/
theorem reducedBlockState_succ_succ_eq_succ_of_isSourceZCL
    (M : MPOTensor d D) (hZCL : IsSourceZCL M) (N : ℕ) :
    M.reducedBlockState (N + 2) N (by omega) =
      M.reducedBlockState (N + 1) N (by omega) := by
  ext u v
  rw [reducedBlockState_apply_eq_trace_evalWord_mul_verticalLoop_pow,
    reducedBlockState_apply_eq_trace_evalWord_mul_verticalLoop_pow]
  rw [show N + 2 - N = 2 by omega, show N + 1 - N = 1 by omega, pow_one]
  obtain ⟨hE0, lam, hlam, hsq⟩ := hZCL
  have hsq' : M.verticalLoop ^ 2 = (lam : ℂ) • M.verticalLoop := by
    rw [pow_two, verticalLoop_eq_physTraceTransfer, hsq]
  have hnum :
      Matrix.trace
          (M.evalWord (List.ofFn u) (List.ofFn v) * M.verticalLoop ^ 2) =
        (lam : ℂ) *
          Matrix.trace (M.evalWord (List.ofFn u) (List.ofFn v) * M.verticalLoop) := by
    rw [hsq', Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hsplit : M.verticalLoop ^ (N + 2) =
      M.verticalLoop ^ N * M.verticalLoop ^ 2 := by
    rw [pow_add]
  have hpow : M.verticalLoop ^ (N + 2) =
      (lam : ℂ) • M.verticalLoop ^ (N + 1) := by
    rw [hsplit, hsq', Matrix.mul_smul, ← pow_succ]
  have htrace : (mpo M (N + 2)).trace =
      (lam : ℂ) * (mpo M (N + 1)).trace := by
    rw [trace_mpo_eq_trace_verticalLoop_pow,
      trace_mpo_eq_trace_verticalLoop_pow, hpow, Matrix.trace_smul, smul_eq_mul]
  have htr : (mpo M (N + 1)).trace ≠ 0 := by
    exact trace_mpo_ne_zero_of_isSourceZCL M ⟨hE0, lam, hlam, hsq⟩ (by omega)
  have hlamC : (lam : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlam
  rw [htrace, hnum]
  field_simp

/-- Under source zero correlation length, tracing three sites from length
`L + 3` gives the same normalized `L`-site marginal as tracing one site from
length `L + 1`.

This is the iterated marginal replacement needed for the four-region argument:
first apply the ZCL replacement while retaining `L + 1` sites, trace the last
retained site, and then apply the ZCL replacement while retaining `L` sites.
It makes no assertion that the neighboring trace matrix equals its square.

Source: arXiv:1606.00608, Appendix C.2, lines 1606–1617. -/
theorem reducedBlockState_add_three_eq_succ_of_isSourceZCL
    (M : MPOTensor d D) (hZCL : IsSourceZCL M) (L : ℕ) :
    M.reducedBlockState (L + 3) L (by omega) =
      M.reducedBlockState (L + 1) L (by omega) := by
  have hstep :
      M.reducedBlockState (L + 3) (L + 1) (by omega) =
        M.reducedBlockState (L + 2) (L + 1) (by omega) := by
    simpa [Nat.add_assoc] using
      reducedBlockState_succ_succ_eq_succ_of_isSourceZCL M hZCL (L + 1)
  have htrace :
      M.reducedBlockState (L + 3) L (by omega) =
        M.reducedBlockState (L + 2) L (by omega) := by
    ext u v
    have hcollapse3 :=
      collapse_last M (N := L + 3) (a := L) (b := 0) (c := 1) (by omega) u v
    have hcollapse2 :=
      collapse_last M (N := L + 2) (a := L) (b := 0) (c := 1) (by omega) u v
    simp only [Nat.add_zero] at hcollapse3 hcollapse2
    rw [← hcollapse3, ← hcollapse2]
    exact Finset.sum_congr rfl fun y _ ↦ congr_fun (congr_fun hstep (Fin.append u y))
      (Fin.append v y)
  exact htrace.trans (reducedBlockState_succ_succ_eq_succ_of_isSourceZCL M hZCL L)

end MPOTensor
