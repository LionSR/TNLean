/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CompositionIndex
import TNLean.MPS.MPU.ReducedCanonicalRepresentative
import TNLean.MPS.MPU.SimpleReduction
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# A standard-form representative of a simple MPU

Canonical reduction preserves simplicity at the given physical scale through
an actual full-word reduction. The two-site standard form can therefore use
the corrected literal source gates of the reduced representative, with no
preliminary blocking to make that representative simple.

Source: arXiv:1703.09188, canonical-form discussion, Definition III.2,
Theorem III.8, and Definition III.9 (`SF`), lines 257--374 and 563--622.
-/

namespace MPOTensor

variable {d D : ℕ}

/-- A simple MPU has a simple canonical-form-II representative of no larger
bond dimension, generating exactly the same positive-length periodic family.
Simplicity is transported through the normal-target full-word reduction, not
inferred from periodic equality alone.

Source: arXiv:1703.09188, canonical-form discussion and Definition III.2,
lines 257--374. -/
theorem IsMPUSimple.exists_reduced_cfii_representative
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPUSimple U) :
    ∃ (E : ℕ) (_hE : 0 < E) (V : MPOTensor d E)
      (_hV : IsMPUCanonicalFormII V),
      IsMPUSimple V ∧ E ≤ D ∧
        (∀ N : ℕ, 0 < N → mpo V N = mpo U N) := by
  obtain ⟨E, hE, V, hV, hdim, hsame⟩ := hU.isMPU.exists_reduced_cfii_representative
  obtain ⟨A, B, hred⟩ := exists_isReduction_of_mpo_eq_cfii hV
    (fun N hN ↦ (hsame N hN).symm)
  exact ⟨E, hE, V, hV, hV.isMPUSimple_of_isReduction hU hred, hdim, hsame⟩

/-- Every simple MPU admits a reduced standard-form representative whose two
gates are literally the corrected source gates of that representative.
The representative is already simple before the single two-site blocking
appearing in the source standard form. There is no canonical-form, full-support,
or prescribed-factor hypothesis on the input tensor.

Source: arXiv:1703.09188, Theorem III.8 (`ThmFund1`), equation `StandardForm`,
and Definition III.9 (`SF`), lines 563--622. -/
theorem IsMPUSimple.exists_reduced_twoSiteStandardFormData
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPUSimple U) :
    ∃ (E : ℕ) (_hE : 0 < E) (V : MPOTensor d E)
      (hV : IsMPUCanonicalFormII V),
      IsMPUSimple V ∧ E ≤ D ∧
        (∀ N : ℕ, 0 < N → mpo V N = mpo U N) ∧
        Nonempty (TwoSiteStandardFormData (blockTwo V)
          (sourceU V hV.ρ hV.ρ_posDef) (sourceV V hV.ρ hV.ρ_posDef)) := by
  obtain ⟨E, hE, V, hV, hsimple, hdim, hsame⟩ := hU.exists_reduced_cfii_representative
  exact ⟨E, hE, V, hV, hsimple, hdim, hsame, ⟨hV.twoSiteStandardFormData hsimple⟩⟩

end MPOTensor
