/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockIntervalDefectDecay

/-!
# Projector error decay for a block-diagonal tensor

A weighted direct sum of pairwise inequivalent normalized primitive tensors
has uniformly small interval projector error when the overlap is sufficiently
long. The nonzero block weights do not affect the interval ground spaces.
This is the estimate from Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma `commutation` (ii), applied to the ground spaces of the direct sum.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]

/-- The projector error of a weighted direct sum tends uniformly to zero
in the overlap length. This is the consequence of Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), used in condition C3′
with a positive right outer interval. The block coefficients are nonzero. -/
theorem eventually_toTensorFromBlocks_projector_defect_le
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) :
    let B := toTensorFromBlocks (d := d) (μ := μ) A
    ∀ᶠ L : ℕ in atTop, ∀ K Q : ℕ, 0 < Q →
      ‖(groundSpaceES B (K + L + Q)).starProjection -
        (leftBoundaryMapES B (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES B K L Q).range.starProjection‖ ≤ η := by
  filter_upwards [eventually_iSup_groundSpaceES_projector_defect_le_of_inequivalent
    A ρ hP hρ hDistinct hη] with L hL K Q hQ
  simpa only [groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ,
    range_leftBoundaryMapES_toTensorFromBlocks_eq_iSup μ A hμ,
    range_reassocTailBoundaryMapES_toTensorFromBlocks_eq_iSup μ A hμ] using hL K Q hQ

end MPSTensor
