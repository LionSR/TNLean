/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.DirectSumBlockPermutation
import TNLean.MPS.MPDO.VerticalSectorIdentity

/-!
# Relabelling of transported vertical sectors

The mutually inverse transported vertical-sector maps determine the same
matching of simple matrix summands as their trace-adjoint star-algebra
equivalence.  This file specializes the abstract classification to the
vertical canonical forms of an MPDO.

The source is CPSV16, arXiv:1606.00608, Appendix C.4, line 1997.  The
multiplicity and coefficient calculation at lines 2001--2008 is not used.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

/-- The two transported vertical-sector algebras have matched simple summands,
and their mutually inverse maps act by conjugation with the same unitaries.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, line 1997. The multiplicity
and coefficient comparison at lines 2001--2008 is not asserted here. -/
theorem transportedVerticalSector_exists_unitaryBlockEquiv
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    ∃ sigma : Fin g₁ ≃ Fin g₂, ∃ hDim : ∀ i, h.dim₁ i = h.dim₂ (sigma i),
      ∃ V : ∀ i, Matrix.unitaryGroup (Fin (h.dim₂ (sigma i))) ℂ,
        (∀ (i : Fin g₁) (X : Matrix (Fin (h.dim₁ i)) (Fin (h.dim₁ i)) ℂ),
            h.Tbar (Pi.single i X) = Pi.single (sigma i)
              ((V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X *
                  (V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ)ᴴ)) ∧
          ∀ (i : Fin g₁) (Y : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ),
            h.Sbar (Pi.single (sigma i) Y) = Pi.single i
              ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
                ((V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ)ᴴ * Y *
                  (V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ))) := by
  classical
  let : ∀ i, NeZero (h.dim₁ i) := fun i ↦ ⟨(h.hBNT₁.blocks_dim_pos i).ne'⟩
  let : ∀ j, NeZero (h.dim₂ j) := fun j ↦ ⟨(h.hBNT₂.blocks_dim_pos j).ne'⟩
  have hTbar : Matrix.IsKrausDirectSumMap h.Tbar := by
    exact transportedVerticalSectorT_isKrausDirectSumMap
      h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
      h.U₁ h.U₂ h.T h.hTCPTP.isKrausCP
  have hSbar : Matrix.IsKrausDirectSumMap h.Sbar := by
    exact transportedVerticalSectorS_isKrausDirectSumMap
      h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
      h.U₁ h.U₂ h.S h.hSCPTP.isKrausCP
  obtain ⟨_, _, hTbarTP, hSbarTP⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  obtain ⟨hST, hTS⟩ := transportedVerticalSector_composites_eq_id h
  obtain ⟨sigma, hDim, V, hVT, hVS⟩ :=
    Matrix.exists_blockEquiv_dim_eq_unitary_forward_of_mutual_inverse_kraus_direct_sum_maps
      h.Tbar h.Sbar hTbar hSbar hTbarTP hSbarTP hST hTS
  exact ⟨sigma, hDim, V, hVT, hVS⟩

end MPOTensor
