/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumBlockPermutation
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
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim₁ α, A₁ α⟩))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hTCPTP : IsKrausCPTP T)
    (hSCPTP : IsKrausCPTP S)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hTphys : ∀ X, T (physClose1 M X) = physClose2 M X)
    (hSphys : ∀ X, S (physClose2 M X) = physClose1 M X) :
    let Tbar := transportedVerticalSectorT
      dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
    let Sbar := transportedVerticalSectorS
      dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
    ∃ sigma : Fin g₁ ≃ Fin g₂, ∃ hDim : ∀ i, dim₁ i = dim₂ (sigma i),
      ∃ V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ,
        (∀ (i : Fin g₁) (X : Matrix (Fin (dim₁ i)) (Fin (dim₁ i)) ℂ),
            Tbar (Pi.single i X) = Pi.single (sigma i)
              ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X *
                  (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ)) ∧
          ∀ (i : Fin g₁) (Y : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ),
            Sbar (Pi.single (sigma i) Y) = Pi.single i
              ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
                ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ * Y *
                  (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ))) := by
  classical
  let h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D) :=
    { dim₁ := dim₁
      mult₁ := mult₁
      weight₁ := weight₁
      dim₂ := dim₂
      mult₂ := mult₂
      weight₂ := weight₂
      hMult₁ := hMult₁
      hWeight₁ := hWeight₁
      hMult₂ := hMult₂
      hWeight₂ := hWeight₂
      M := M
      A₁ := A₁
      A₂ := A₂
      U₁ := U₁
      U₂ := U₂
      T := T
      S := S
      hForward₁ := hForward₁
      hReconstruct₁ := hReconstruct₁
      hForward₂ := hForward₂
      hReconstruct₂ := hReconstruct₂
      hTphys := hTphys
      hSphys := hSphys
      hBNT₁ := hBNT₁
      hBNT₂ := hBNT₂
      hU₁ := hU₁
      hU₂ := hU₂
      hTCPTP := hTCPTP
      hSCPTP := hSCPTP }
  let Tbar := transportedVerticalSectorT
    dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
  let Sbar := transportedVerticalSectorS
    dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
  letI : ∀ i, NeZero (dim₁ i) := fun i ↦ ⟨(hBNT₁.blocks_dim_pos i).ne'⟩
  letI : ∀ j, NeZero (dim₂ j) := fun j ↦ ⟨(hBNT₂.blocks_dim_pos j).ne'⟩
  have hTbar : Matrix.IsKrausDirectSumMap Tbar := by
    exact transportedVerticalSectorT_isKrausDirectSumMap
      dim₁ mult₁ weight₁ dim₂ mult₂ hMult₁ hWeight₁ U₁ U₂ T hTCPTP.isKrausCP
  have hSbar : Matrix.IsKrausDirectSumMap Sbar := by
    exact transportedVerticalSectorS_isKrausDirectSumMap
      dim₁ mult₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ U₁ U₂ S hSCPTP.isKrausCP
  obtain ⟨_, _, hTbarTP, hSbarTP⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  obtain ⟨hST, hTS⟩ := transportedVerticalSector_composites_eq_id h
  obtain ⟨sigma, hDim, V, hVT, hVS⟩ :=
    Matrix.exists_blockEquiv_dim_eq_unitary_forward_of_mutual_inverse_kraus_direct_sum_maps
      Tbar Sbar hTbar hSbar hTbarTP hSbarTP hST hTS
  exact ⟨sigma, hDim, V, hVT, hVS⟩

end MPOTensor
