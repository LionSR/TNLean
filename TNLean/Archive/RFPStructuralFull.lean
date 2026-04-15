/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.StructuralForm

/-!
# Scaffolding: full structural form for RFP tensors (Lemma B.1)

This file contains the **statement** of the full Appendix B structural decomposition
for renormalization fixed-point tensors (arXiv:1606.00608, Lemma B.1). The proof
is deferred (marked `sorry`) pending the forward Kraus-to-isometry extraction
step after the rank-one classification of idempotent irreducible CP maps.

This file lives in `Archive/` because `sorry` is a proof-integrity blocker
for core modules (see `docs/PROOF_INTEGRITY.md`). Tracked by issue #233.

## Proof strategy

The fully-proved stepping stones are:
* `rfp_nt_structural_of_leftCanonical` — left-canonical normal RFP ⟹ injective
* `rfp_nt_cfii_diagonal_fixedPoint` — after unitary conjugation, a diagonal
  positive-definite fixed point for the transfer map exists
* `transferMap_eq_fixedPointProj_of_isRFP_injective` — rank-one classification:
  for an injective left-canonical RFP tensor, the transfer map equals
  `fixedPointProj ρ`, i.e. `X ↦ (tr X / tr ρ) • ρ`

The remaining gap:
1. ~~Classify idempotent irreducible CP maps as rank-one projectors~~ ✓ Done
2. Extract the physical-index isometry family from the rank-one structure
   via Kraus freedom (construct canonical Kraus operators for `fixedPointProj`
   with diagonal PosDef fixed point, then apply `kraus_rectangular_freedom'`)
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma B.1** (arXiv:1606.00608, Appendix B): a normal tensor in canonical
form II that is an RFP should admit the decomposition `A i = X * Λ * U i * X⁻¹`
with diagonal positive `Λ` and a physical-index isometry `U`.

The rank-one classification step is now proved as
`transferMap_eq_fixedPointProj_of_isRFP_injective` in `MPS/RFP/StructuralForm.lean`.
The remaining gap is extracting the physical-index isometry family from the
rank-one structure via `kraus_rectangular_freedom'`: construct the canonical
Kraus operators for `fixedPointProj Λ_mat` with diagonal PosDef `Λ_mat`,
verify they generate the same CPM, and assemble the `X * diag(Λ) * U_i * X⁻¹`
witnesses. -/
theorem rfp_nt_structural_full (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹) := by
  classical
  have _hInj : IsInjective A :=
    rfp_nt_structural_of_leftCanonical A hNT hRFP hLeft
  obtain ⟨_U, _Λmat, _hΛ_pd, _hΛ_diag, _hB_left, _hB_fix⟩ :=
    rfp_nt_cfii_diagonal_fixedPoint A hNT hRFP hLeft
  -- TODO(#233): The rank-one classification is now proved
  -- (`transferMap_eq_fixedPointProj_of_isRFP_injective`). Remaining:
  -- 1. prove that the unitary-conjugated tensor from
  --    `rfp_nt_cfii_diagonal_fixedPoint` remains injective and RFP;
  -- 2. apply the rank-one classification to that conjugated tensor;
  -- 3. construct an explicit canonical Kraus family for
  --    `fixedPointProj Λmat` with diagonal PosDef `Λmat`;
  -- 4. apply `kraus_rectangular_freedom'` to extract the physical-index
  --    isometry family;
  -- 5. assemble the witnesses `X`, `Λ`, and `U`.
  sorry

end MPSTensor
