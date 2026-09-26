/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntervalDefectDecay
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold

/-!
# Uniform projector error decay for inequivalent primitive blocks

For finitely many pairwise inequivalent normalized primitive tensors, the
projector error for two overlapping intervals tends to zero as the overlap
length tends to infinity, uniformly in the outer interval lengths. This is
the consequence of Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma
`commutation` (ii), used in condition C3′ with a positive right interval.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- Uniform decay of the joint interval projector error for inequivalent
primitive blocks. The block dimensions may differ. The right outer interval
has positive length, as required in Nachtergaele, arXiv:cond-mat/9410110,
condition C3′; the estimate follows from Lemma `commutation` (ii) and the
limits in Section 6. -/
theorem eventually_iSup_groundSpaceES_projector_defect_le_of_inequivalent
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L : ℕ in atTop, ∀ K Q : ℕ, 0 < Q →
      let U := fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range
      let V := fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range
      ‖(⨆ i, groundSpaceES (A i) (K + L + Q)).starProjection -
        (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤ η := by
  refine eventually_iSup_groundSpaceES_projector_defect_le A ?_ ?_ hη
  · exact fun ε hε ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      eventually_all.2 fun hij ↦
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε
  · exact fun ε hε ↦ eventually_all.2 fun i ↦
      (hP i).eventually_wholeIncrement_groundProjection_defect_le (hρ i) hε

end MPSTensor
