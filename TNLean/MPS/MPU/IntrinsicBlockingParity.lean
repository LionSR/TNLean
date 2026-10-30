/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalTwistedTransfer
import TNLean.MPS.MPU.ReducedCanonicalRepresentative

/-!
# Intrinsic time-reversal blocking parity for arbitrary MPUs

The intrinsic blocked trace depends only on the actual positive-length
periodic family. The existing reduced canonical representative therefore
transports the canonical parity result to every positive-dimensional MPU.
This does not identify source factors across different auxiliary spaces.

The conclusion concerns the intrinsic trace. Constructing the particular
blocked gates printed in the source and their sequential unwinding remains
a separate statement; no such supplier is assumed here.

Source: arXiv:1703.09188, canonical replacement, lines 319--356,
`prop:sigma-well-defined`, lines 1613--1631, and
`prop:sigma1-and-sigma2-equal`, lines 1643--1733.
-/

namespace MPOTensor

variable {d D E : ℕ}

/-- Equal positive-length periodic families have equal intrinsic traces at
every positive physical blocking, even at different bond dimensions. The
actual blocked periodic operators are the same reindexing of length `2*k`.
No equality at length zero or bond-space identification is asserted.

Source: arXiv:1703.09188, canonical replacement and
`prop:sigma-well-defined`, lines 319--356 and 1613--1631. -/
theorem intrinsicTimeReversalSign_blockTensor_eq_of_mpo_eq
    {U : MPOTensor d D} {V : MPOTensor d E}
    (hEq : ∀ N : ℕ, 0 < N → mpo U N = mpo V N) (k : ℕ) (hk : 0 < k) :
    intrinsicTimeReversalSign (blockTensor U k) =
      intrinsicTimeReversalSign (blockTensor V k) := by
  apply intrinsicTimeReversalSign_eq_of_mpo_two_eq
  rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex,
    hEq (2 * k) (Nat.mul_pos (by omega) hk)]

/-- Intrinsic time-reversal blocking parity for any positive-dimensional
MPU with actual adjoint symmetry on every even ring. Canonical replacement
and all spectral data are derived internally; there is no canonical,
full-support, simplicity, source-factor, local-certificate or stabilization
premise on the input tensor.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1643--1733,
using canonical replacement from lines 319--356. This gives the intrinsic
numerical parity identities, not the printed blocked-gate construction. -/
theorem IsMPU.intrinsic_blocking_trace_parity
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ) :
    ∀ k : ℕ, 0 < k →
      (Odd k → intrinsicTimeReversalSign (blockTensor U k) =
        intrinsicTimeReversalSign U) ∧
      (Even k → intrinsicTimeReversalSign (blockTensor U k) =
        intrinsicTimeReversalSign (blockTensor U 2)) := by
  obtain ⟨Dred, _, V, hV, _, hMpo⟩ := hU.exists_reduced_cfii_representative
  have hEq : ∀ N : ℕ, 0 < N → mpo U N = mpo V N :=
    fun N hN ↦ (hMpo N hN).symm
  have hTRV : ∀ N : ℕ, 1 < N → Even N → mpo V N = (mpo V N)ᴴ := by
    intro N hN heven
    simpa only [hMpo N (Nat.zero_lt_of_lt hN)] using hTR N hN heven
  have hfirst : intrinsicTimeReversalSign U = intrinsicTimeReversalSign V :=
    intrinsicTimeReversalSign_eq_of_mpo_two_eq (hEq 2 (by omega))
  have hsecond := intrinsicTimeReversalSign_blockTensor_eq_of_mpo_eq hEq 2 (by omega)
  intro k hk
  have hblocked := intrinsicTimeReversalSign_blockTensor_eq_of_mpo_eq hEq k hk
  constructor
  · intro hodd
    exact hblocked.trans ((hV.intrinsic_blocking_trace_eq_of_odd hTRV k hk hodd).trans
      hfirst.symm)
  · intro heven
    exact hblocked.trans ((hV.intrinsic_blocking_trace_eq_of_even hTRV k hk heven).trans
      hsecond.symm)

end MPOTensor
