/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.TimeReversal.PrintedBlockingHalfFactors
import TNLean.MPS.MPU.Symmetry.TimeReversal.IntrinsicBlockingParity
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalSignIntrinsic
import TNLean.MPS.MPU.StandardForm.SuppliedTwoBlockStandardForm

/-!
# The trace of the actual printed arbitrary-blocking gates

The constructed standard form identifies the printed gate trace with the
intrinsic trace of the actual blocked tensor. The existing intrinsic
parity theorem then applies to these particular representatives.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1643--1733.
The input is supplied square standard-form data; extracting square gates
from a general symmetry-invariant presentation remains separate.

**Scope restriction (square supplied gates):** The supplied-form applications
start with both intermediate spaces equal to the original spin space.
Reduction from a general rectangular standard form is separate; see
`docs/paper-gaps/mpu_printed_blocking_square_scope.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPOTensor

private theorem periodic_trace_sum {d D : ℕ} (W : MPOTensor d D) :
    timeReversalPeriodicTrace W =
      ∑ a : Fin d, ∑ b : Fin d, mpo W 2 ![b, a] ![a, b] := by
  simp [timeReversalPeriodicTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.swapMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, finTwoArrowEquiv, ite_mul, ite_and]

private theorem intrinsic_reindex {d d' D : ℕ} (e : Fin d' ≃ Fin d)
    (W : MPOTensor d D) :
    intrinsicTimeReversalSign (reindexPhysical e W) = intrinsicTimeReversalSign W := by
  have hdim : d' = d := by simpa using Fintype.card_congr e
  have ht : timeReversalPeriodicTrace (reindexPhysical e W) =
      timeReversalPeriodicTrace W := by
    rw [periodic_trace_sum, periodic_trace_sum]
    rw [← e.sum_comp (fun a ↦ ∑ b : Fin d, mpo W 2 ![b, a] ![a, b])]
    apply Finset.sum_congr rfl
    intro a _
    rw [← e.sum_comp (fun b ↦ mpo W 2 ![b, e a] ![e a, b])]
    apply Finset.sum_congr rfl
    intro b _
    simp [mpoMatrixEntry, List.ofFn_succ, evalWord_cons, evalWord_nil, reindexPhysical]
  rw [intrinsicTimeReversalSign, intrinsicTimeReversalSign, ht, hdim]

/-- The trace of the literal printed k-block gates is the intrinsic
trace of the actual k-blocked input tensor. The identification uses the
constructed open standard form and its explicit physical relabelling.
No canonical presentation or symmetry premise is needed for this equality.
Source: arXiv:1703.09188, lines 1689--1705. -/
theorem TwoSiteStandardFormData.printedBlocking_trace_eq_intrinsic {d D : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (k : ℕ) (hk : 0 < k) :
    timeReversalSign (printedBlockedInputGate k hk u v) (printedBlockedOutputGate k hk v) =
      intrinsicTimeReversalSign (blockTensor W k) := by
  rw [(S.printedBlock k hk).timeReversalSign_eq_intrinsic]
  exact intrinsic_reindex _ _

/-- The actual printed blocked representatives have the source odd/even
trace parity whenever the supplied square standard form has adjoint
symmetry on every even ring of length greater than one. No canonical
ambient hypothesis is used. This reuses the intrinsic parity theorem and
the newly constructed actual blocked standard forms.
Source: arXiv:1703.09188, lines 1643--1733. -/
theorem TwoSiteStandardFormData.printed_blocking_trace_parity {d D : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ)
    (k : ℕ) (hk : 0 < k) :
    (Odd k → timeReversalSign (printedBlockedInputGate k hk u v)
      (printedBlockedOutputGate k hk v) = timeReversalSign u v) ∧
    (Even k → timeReversalSign (printedBlockedInputGate k hk u v)
      (printedBlockedOutputGate k hk v) =
        timeReversalSign (twoBlockInputGate u v) (twoBlockOutputGate v)) := by
  let : NeZero d := ⟨Nat.ne_of_gt S.phys_pos⟩
  let : NeZero D := ⟨Nat.ne_of_gt S.bond_pos⟩
  obtain ⟨ho, he⟩ := S.isMPU.intrinsic_blocking_trace_parity hTR k hk
  have htwo : timeReversalSign (twoBlockInputGate u v) (twoBlockOutputGate v) =
      intrinsicTimeReversalSign (blockTensor W 2) := by
    rw [S.blockTwo.timeReversalSign_eq_intrinsic]
    have hb : MPOTensor.blockTwo W =
        reindexPhysical (twoSiteBlockEquiv (d * d)) (blockTensor W 2) :=
      blockTwo_eq_blockTensor_reindex W
    rw [hb]
    exact intrinsic_reindex _ _
  rw [S.printedBlocking_trace_eq_intrinsic k hk]
  constructor
  · intro hodd
    exact (ho hodd).trans S.timeReversalSign_eq_intrinsic.symm
  · intro heven
    exact (he heven).trans htwo.symm

end MPOTensor
