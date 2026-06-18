/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.SharedInfra.Scaling
import TNLean.PiAlgebra.CanonicalFormSepAux

/-!
# Normal canonical forms as period-one irreducible forms

This file records the implication from normal canonical block hypotheses to
irreducible form in the period-one case.
-/

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Replace each nonzero complex normal-canonical weight by its positive real
modulus, as in the irreducible-form convention of arXiv:1708.00029, lines
252--261. -/
noncomputable def positiveRealWeights (μ : Fin r → ℂ) : Fin r → ℂ :=
  fun k => (‖μ k‖ : ℂ)

/-- Absorb the phase of each nonzero normal-canonical weight into its block.
With weights `positiveRealWeights μ`, these blocks generate the same MPV family
as the original weighted block tensor. -/
noncomputable def phaseNormalizedBlocks
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k)) :
    (k : Fin r) → MPSTensor d (dim k) :=
  fun k i => (μ k / (‖μ k‖ : ℂ)) • blocks k i

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

/-- Phase normalization does not change the MPV family represented by the
weighted block tensor.  The identity is
\[
  \mu_k^N V^{(N)}(A_k)
    = \|\mu_k\|^N V^{(N)}((\mu_k/\|\mu_k\|)A_k)
\]
for each block contribution. -/
theorem sameMPV₂_toTensorFromBlocks_phaseNormalized
    (hμ : ∀ k, μ k ≠ 0) :
    SameMPV₂
      (toTensorFromBlocks (d := d) (μ := μ) blocks)
      (toTensorFromBlocks (d := d) (μ := positiveRealWeights μ)
        (phaseNormalizedBlocks μ blocks)) := by
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [positiveRealWeights]
  change μ k ^ N • (blocks k).mpv σ =
    (↑‖μ k‖ : ℂ) ^ N •
      mpv (fun i => (μ k / (‖μ k‖ : ℂ)) • blocks k i) σ
  rw [mpv_smul]
  have hnorm_ne : ((‖μ k‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (hμ k)
  have hphase : (‖μ k‖ : ℂ) * (μ k / (‖μ k‖ : ℂ)) = μ k := by
    field_simp [hnorm_ne]
  let t := mpv (blocks k) σ
  change μ k ^ N * t =
    (↑‖μ k‖ : ℂ) ^ N * ((μ k / (‖μ k‖ : ℂ)) ^ N * t)
  calc
    μ k ^ N * t =
        ((↑‖μ k‖ : ℂ) * (μ k / (‖μ k‖ : ℂ))) ^ N * t := by
      rw [hphase]
    _ = (↑‖μ k‖ : ℂ) ^ N * ((μ k / (‖μ k‖ : ℂ)) ^ N * t) := by
      rw [mul_pow, mul_assoc]

/-- A normal canonical block family gives an irreducible-form witness after
absorbing each block-weight phase into the corresponding block.

Source context: arXiv:1708.00029, lines 252--271. The paper writes the
irreducible-form weights as positive real numbers `μ_j > 0`. If the same
decomposition is first written with nonzero complex coefficients, replacing
`μ_j` by `‖μ_j‖` and `A_j` by `(μ_j / ‖μ_j‖) A_j` gives the paper's convention
without changing the represented MPV family. -/
noncomputable def toIsIrreducibleFormOfPhaseNormalized
    (hNCF : IsNormalCanonicalForm (d := d) μ blocks) :
    IsIrreducibleForm (toTensorFromBlocks (d := d) (μ := μ) blocks) where
  r := r
  dim := dim
  blocks := phaseNormalizedBlocks μ blocks
  μ := positiveRealWeights μ
  period := fun _ => 1
  periodic := by
    intro k
    have hPeriod : IsPeriodic 1 (blocks k) := by
      rw [IsPeriodic.one_iff_primitive]
      exact ⟨hNCF.block_irreducible k, hNCF.leftCanonical k, hNCF.block_primitive k⟩
    change IsPeriodic 1 (fun i => (μ k / (‖μ k‖ : ℂ)) • blocks k i)
    exact isPeriodic_smul_of_norm_one
      (phase_norm_one (hNCF.mu_ne_zero k)) (blocks k) hPeriod
  weight_pos := by
    intro k
    constructor
    · simpa [positiveRealWeights] using norm_pos_iff.mpr (hNCF.mu_ne_zero k)
    · simp [positiveRealWeights]
  sameMPV := sameMPV₂_toTensorFromBlocks_phaseNormalized hNCF.mu_ne_zero

/-- In the irreducible-form witness obtained by phase-normalizing a normal
canonical block family, every block period is `1`.

Source context: arXiv:1708.00029, lines 258--271. -/
theorem toIsIrreducibleFormOfPhaseNormalized_period_eq_one
    (hNCF : IsNormalCanonicalForm (d := d) μ blocks) :
    ∀ k : Fin r,
      (toIsIrreducibleFormOfPhaseNormalized
        (d := d) (μ := μ) (blocks := blocks) hNCF).period k = 1 := by
  intro k
  rfl

end MPSTensor
