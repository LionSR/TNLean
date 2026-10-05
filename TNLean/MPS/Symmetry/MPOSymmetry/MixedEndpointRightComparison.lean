/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSwap
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorOrder

/-!
# Local interaction comparison at the second mixed endpoint

The explicit sector exchange transports the first-endpoint comparison to
the second endpoint. This derives the same three-term bound from the actual
second diagonal tensor and its extended support, without repeating the
boundary compression or projection argument.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

private theorem bondInterpolationWeight_zero_swap (i : Fin (D₀ + D₁)) :
    bondInterpolationWeight D₁ D₀ 0 (mixedEndpointBondSwap D₀ D₁ i) =
      1 - bondInterpolationWeight D₀ D₁ 0 i := by
  unfold mixedEndpointBondSwap
  simp only [Equiv.trans_apply]
  cases h : finSumFinEquiv.symm i <;> simp [bondInterpolationWeight, h]

/-- The first-sector row projection in the reversed pair is the second-sector
row projection in the original pair. Source: arXiv:2203.12563, Section 5,
lines 1586–1601 and 1690–1692. -/
theorem mixedEndpointRowSector_conj_swap (site : Fin 2) :
    (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).toLinearEquiv.conj
      (mixedEndpointRowSector D₁ D₀ site) = 1 - mixedEndpointRowSector D₀ D₁ site := by
  rw [mixedEndpointRowSector, physicalReindexLinearIsometryEquiv_conj_diagonal]
  ext v σ
  change (Matrix.diagonal (fun ω => bondInterpolationWeight D₁ D₀ 0
      (finProdFinEquiv.symm (mixedEndpointPhysicalSwap D₀ D₁ (ω site))).1)).mulVec v σ =
    v σ - mixedEndpointRowSector D₀ D₁ site v σ
  rw [Matrix.mulVec_diagonal, mixedEndpointRowSector_apply]
  simp only [mixedEndpointPhysicalSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply, Prod.map_fst, bondInterpolationWeight_zero_swap]
  ring

/-- The first-sector column projection in the reversed pair is the second-sector
column projection in the original pair. Source: arXiv:2203.12563, Section 5,
lines 1586–1601 and 1690–1692. -/
theorem mixedEndpointColumnSector_conj_swap (site : Fin 2) :
    (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).toLinearEquiv.conj
      (mixedEndpointColumnSector D₁ D₀ site) = 1 - mixedEndpointColumnSector D₀ D₁ site := by
  rw [mixedEndpointColumnSector, physicalReindexLinearIsometryEquiv_conj_diagonal]
  ext v σ
  change (Matrix.diagonal (fun ω => bondInterpolationWeight D₁ D₀ 0
      (finProdFinEquiv.symm (mixedEndpointPhysicalSwap D₀ D₁ (ω site))).2)).mulVec v σ =
    v σ - mixedEndpointColumnSector D₀ D₁ site v σ
  rw [Matrix.mulVec_diagonal, mixedEndpointColumnSector_apply]
  simp only [mixedEndpointPhysicalSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply, Prod.map_snd, bondInterpolationWeight_zero_swap]
  ring

/-- The canonical right-endpoint interaction is the transported left-endpoint
interaction for the reversed pair. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem parentInteractionES_mixedEndpointRightTensor_eq_conj
    (A₁ : MPSTensor (D₁ * D₁) D₁) :
    parentInteractionES (mixedEndpointRightTensor A₁ D₀) 2 =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).toLinearEquiv.conj
        (parentInteractionES (mixedEndpointLeftTensor A₁ D₀) 2) :=
  parentInteractionES_reindexPhysical_equiv _ _ _

/-- The actual extended second-endpoint term is bounded by the canonical
embedded right-endpoint term. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_one_le_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap ≤
      parentInteractionES (mixedEndpointRightTensor A₁ D₀) 2 := by
  rw [mixedEndpointParentInteraction_one_eq_conj_swap,
    parentInteractionES_mixedEndpointRightTensor_eq_conj]
  exact ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).conj_le_conj_iff
    _ _).mpr
    (mixedEndpointParentInteraction_zero_le_parentInteractionES A₁ A₀)

/-- The actual extended second-endpoint term and its two outer first-sector
penalties bound the canonical embedded right-endpoint term.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem parentInteractionES_mixedEndpointRightTensor_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    parentInteractionES (mixedEndpointRightTensor A₁ D₀) 2 ≤
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap +
        mixedEndpointRowSector D₀ D₁ 0 + mixedEndpointColumnSector D₀ D₁ 1 := by
  have h := ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).conj_le_conj_iff
     _ _).mpr (parentInteractionES_mixedEndpointLeftTensor_le A₁ A₀)
  simpa only [map_add, map_sub, map_one, mixedEndpointRowSector_conj_swap,
    mixedEndpointColumnSector_conj_swap, sub_sub_cancel,
    ← mixedEndpointParentInteraction_one_eq_conj_swap,
    ← parentInteractionES_mixedEndpointRightTensor_eq_conj] using h

/-- The first-column first-sector penalty lies below the actual second-endpoint
interaction. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_columnSector_zero_le_parentInteraction_one
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointColumnSector D₀ D₁ 0 ≤
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap := by
  have h := ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).conj_le_conj_iff
     _ _).mpr
      (mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₁ A₀)
  simpa only [map_sub, map_one, mixedEndpointColumnSector_conj_swap, sub_sub_cancel,
    ← mixedEndpointParentInteraction_one_eq_conj_swap] using h

/-- The second-row first-sector penalty lies below the actual second-endpoint
interaction. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_rowSector_one_le_parentInteraction_one
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointRowSector D₀ D₁ 1 ≤
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap := by
  have h := ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).conj_le_conj_iff
     _ _).mpr
      (mixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₁ A₀)
  simpa only [map_sub, map_one, mixedEndpointRowSector_conj_swap, sub_sub_cancel,
    ← mixedEndpointParentInteraction_one_eq_conj_swap] using h

end MPOSymmetry
end MPSTensor
