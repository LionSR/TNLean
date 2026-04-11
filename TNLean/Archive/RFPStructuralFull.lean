/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.StructuralForm

/-!
# Scaffolding: full structural form for RFP tensors (Lemma B.1)

This file contains the **statement** of the full Appendix B structural decomposition
for renormalization fixed-point tensors (arXiv:1606.00608, Lemma B.1). The proof
is deferred (marked `sorry`) pending the rank-one classification of idempotent
irreducible CP maps and the forward Kraus-to-isometry extraction step.

This file lives in `Archive/` because `sorry` is a proof-integrity blocker
for core modules (see `docs/PROOF_INTEGRITY.md`). Tracked by issue #233.

## Proof strategy

The fully-proved stepping stones are:
* `rfp_nt_structural_of_leftCanonical` — left-canonical normal RFP ⟹ injective
* `rfp_nt_cfii_diagonal_fixedPoint` — after unitary conjugation, a diagonal
  positive-definite fixed point for the transfer map exists

The remaining gap:
1. Classify idempotent irreducible CP maps as rank-one projectors of the form
   `X ↦ (trace X / trace Λ) • Λ` using `posSemidef_fixedPoint_unique_of_irreducible`
2. Extract the physical-index isometry family from the rank-one structure
   via Kraus freedom
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma B.1** (arXiv:1606.00608, Appendix B): a normal tensor in canonical
form II that is an RFP should admit the decomposition `A i = X * Λ * U i * X⁻¹`
with diagonal positive `Λ` and a physical-index isometry `U`.

The current formalization isolates the missing step to the expected gap:
classifying idempotent irreducible CP maps as rank-one projections and then
identifying the resulting Kraus family with the canonical `Λ * U i` form via
Kraus freedom. The injectivity and CFII diagonal-fixed-point reduction are
already available as `rfp_nt_structural_of_leftCanonical` and
`rfp_nt_cfii_diagonal_fixedPoint`. -/
theorem rfp_nt_structural_full (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹) := by
  -- TODO(#233): use `rfp_nt_cfii_diagonal_fixedPoint` to pass to CFII, prove that the
  -- idempotent irreducible transfer map is a rank-one projector `X ↦ trace X • ρ`, and
  -- then apply Kraus freedom in the forward direction to extract the physical-index isometry.
  sorry

end MPSTensor
