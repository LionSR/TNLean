/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.PiAlgebra.CanonicalFormSepAux

/-!
# Normal canonical forms as period-one irreducible forms

This file records the implication from normal canonical block hypotheses to
irreducible form in the period-one case.
-/

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- A normal canonical block family with positive real weights is an irreducible-form
decomposition whose block periods are all equal to `1`.

Source context: arXiv:1708.00029, lines 258--271. The paper's irreducible form
uses weights `μ_j > 0`. The local normal-canonical definition only assumes
nonzero complex weights, so the positive-weight convention is stated here as a
separate hypothesis. The imaginary-zero conjunct records the paper's real-weight
convention. See
`docs/paper-gaps/1708_normal_canonical_irreducible_form_weights.tex`. -/
def toIsIrreducibleFormOfWeightPos
    (hNCF : IsNormalCanonicalForm (d := d) μ blocks)
    (hμpos : ∀ k, 0 < (μ k).re ∧ (μ k).im = 0) :
    IsIrreducibleForm (toTensorFromBlocks (d := d) (μ := μ) blocks) where
  r := r
  dim := dim
  blocks := blocks
  μ := μ
  period := fun _ => 1
  periodic := by
    intro k
    rw [IsPeriodic.one_iff_primitive]
    exact ⟨hNCF.block_irreducible k, hNCF.leftCanonical k, hNCF.block_primitive k⟩
  weight_pos := hμpos
  sameMPV := fun _ _ => rfl

/-- In the irreducible-form witness obtained from positive-weight normal canonical
hypotheses, every block period is `1`.

Source context: arXiv:1708.00029, lines 258--271. -/
theorem toIsIrreducibleFormOfWeightPos_period_eq_one
    (hNCF : IsNormalCanonicalForm (d := d) μ blocks)
    (hμpos : ∀ k, 0 < (μ k).re ∧ (μ k).im = 0) :
    ∀ k : Fin r,
      (toIsIrreducibleFormOfWeightPos
        (d := d) (μ := μ) (blocks := blocks) hNCF hμpos).period k = 1 := by
  intro k
  rfl

end MPSTensor
