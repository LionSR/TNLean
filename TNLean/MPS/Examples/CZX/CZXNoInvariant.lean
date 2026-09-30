/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CZX.CZXAnomalyClass
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction

/-!
# No normal matrix product state is invariant under the decorated CZX operator

The decorated CZX representation of `ℤ₂` has nontrivial anomaly class
(`CZXCompression.not_isTrivialGaugeClass_omega_czx`), so by the anomaly obstruction
(`MPOTensor.GroupFamily.IsNormalRepresentation.not_exists_invariant_of_not_isTrivialGaugeClass`)
no normal matrix product state of positive bond dimension is invariant under it.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 570 (an anomalous
symmetry has no invariant injective matrix product state) and lines 1128--1136;
arXiv:2502.20257, `main.tex` line 1545.
-/

noncomputable section

open scoped Matrix
open MPOTensor

namespace CZXCompression

/-- **The decorated CZX operator fixes no normal matrix product state**: there is no
normal matrix product state of positive bond dimension whose periodic vector is fixed
by the decorated CZX operator at every positive length.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 570 and lines
1128--1136; arXiv:2502.20257, `main.tex` line 1545. -/
theorem not_exists_normal_fixesMPV_czxDecoratedTensor :
    ¬ ∃ (D : ℕ) (A : MPSTensor 2 D), 0 < D ∧ Kraus.IsNormal A ∧
      GroupFamily.FixesMPV czxDecoratedTensor A := by
  rintro ⟨D, A, hD, hA, hU⟩
  refine czxFamily_isNormalRepresentation.not_exists_invariant_of_not_isTrivialGaugeClass
    czxFusionData (not_isTrivialGaugeClass_omega_czx czxFusionData) ⟨D, A, hD, hA, ?_⟩
  refine Multiplicative.forall_zmod_two (fun N _ ↦ ?_) hU
  change mpo (MPOTensor.idTensor 2) N *ᵥ _ = _
  rw [mpo_idTensor, Matrix.one_mulVec]

end CZXCompression
