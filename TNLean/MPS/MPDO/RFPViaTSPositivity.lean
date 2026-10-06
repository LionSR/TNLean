/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFPViaTSGlobal

/-!
# One-length positivity for an operational renormalization fixed point

Once the all-boundary channels of arXiv:1606.00608, Definition 4.1, exist,
positivity of the one-site periodic operator implies positivity at every
positive length. Thus the global MPDO positivity condition reduces to one
matrix inequality in this class. The refinement channel supplies the proof;
this reduction does not apply to tensors without the channel identities.
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d D : ℕ} {M : MPOTensor d D}

/-- Positivity at length one propagates to every positive length through the
refinement channel of arXiv:1606.00608, Definition 4.1 and Appendix C. -/
theorem IsRFPViaTS.isMPDO_of_mpo_one_posSemidef (hRFP : IsRFPViaTS M)
    (h₁ : (mpo M 1).PosSemidef) : IsMPDO M := by
  obtain ⟨S, T, hS, hT, hSclose, hTclose⟩ := hRFP
  have hpos : ∀ n : ℕ, (mpo M (n + 1)).PosSemidef := by
    intro n
    induction n with
    | zero => exact h₁
    | succ n ih =>
      rw [← refineFirstSite_mpo M T hTclose n]
      exact (refineFirstSite_isKrausCPTP hT n).map_posSemidef ih
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hpos k

/-- In the operational RFP class, global MPDO positivity is equivalent to
one-site positivity. This is a finite consequence of arXiv:1606.00608,
Definition 4.1, rather than a positivity test for arbitrary MPO tensors. -/
theorem IsRFPViaTS.isMPDO_iff_mpo_one_posSemidef (hRFP : IsRFPViaTS M) :
    IsMPDO M ↔ (mpo M 1).PosSemidef := by
  exact ⟨fun h ↦ h 1 one_pos, hRFP.isMPDO_of_mpo_one_posSemidef⟩

end MPOTensor
