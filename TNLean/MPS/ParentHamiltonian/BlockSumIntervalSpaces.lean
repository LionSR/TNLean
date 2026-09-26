/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Interval ground spaces of a block-diagonal tensor

The local ground space of a weighted direct sum with nonzero coefficients
is the sum of the block ground spaces. The same identity holds after adding
free sites on either side. These are the interval spaces in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2444--2463.
-/

private theorem pi_univ_iSup_const {ι α M : Type*} [Finite α]
    [AddCommMonoid M] [Module ℂ M] (S : ι → Submodule ℂ M) :
    Submodule.pi (Set.univ : Set α) (fun _ ↦ ⨆ i, S i) =
      ⨆ i, Submodule.pi (Set.univ : Set α) (fun _ ↦ S i) := by
  classical
  simp only [← Submodule.iSup_map_single, Submodule.map_iSup]
  exact iSup_comm

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The weighted block sum has the sum of the block ground spaces in the
physical Hilbert space. This is the local identity used in PGVWC07,
Theorem 12, with nonzero block coefficients. -/
theorem groundSpaceES_toTensorFromBlocks_eq_iSup
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (L : ℕ) :
    groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) L =
      ⨆ j, groundSpaceES (A j) L := by
  simp only [groundSpaceES, groundSpace_toTensorFromBlocks_eq_iSup μ A hμ,
    Submodule.map_iSup]

private theorem leftBoundaryMap_range_toTensorFromBlocks
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (K L : ℕ) :
    (leftBoundaryMap (toTensorFromBlocks (d := d) (μ := μ) A) K L).range =
      ⨆ j, (leftBoundaryMap (A j) K L).range := by
  let T : (Cfg d L → NSiteSpace d K) →ₗ[ℂ] NSiteSpace d (K + L) :=
    LinearMap.pi fun σ ↦
      (LinearMap.proj (σ ∘ Fin.castAdd L) : NSiteSpace d K →ₗ[ℂ] ℂ).comp
        (LinearMap.proj (σ ∘ Fin.natAdd K))
  have hfac {D : ℕ} (B : MPSTensor d D) :
      leftBoundaryMap B K L = T.comp ((groundSpaceMap B K).compLeft (Cfg d L)) := rfl
  simp only [hfac, LinearMap.range_comp, LinearMap.range_compLeft,
    show (groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) K).range =
      ⨆ j, (groundSpaceMap (A j) K).range from
        groundSpace_toTensorFromBlocks_eq_iSup μ A hμ K,
    pi_univ_iSup_const, Submodule.map_iSup]

/-- Adding free sites to the right preserves the sum of the block ground
spaces. This identifies the left interval in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), for a weighted direct sum. -/
theorem range_leftBoundaryMapES_toTensorFromBlocks_eq_iSup
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (K L : ℕ) :
    (leftBoundaryMapES (toTensorFromBlocks (d := d) (μ := μ) A) K L).range =
      ⨆ j, (leftBoundaryMapES (A j) K L).range := by
  simp only [leftBoundaryMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    leftBoundaryMap_range_toTensorFromBlocks μ A hμ, Submodule.map_iSup]

private theorem tailBoundaryMap_range_toTensorFromBlocks
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (K L : ℕ) :
    (tailBoundaryMap (toTensorFromBlocks (d := d) (μ := μ) A) K L).range =
      ⨆ j, (tailBoundaryMap (A j) K L).range := by
  let T : (Cfg d K → NSiteSpace d L) →ₗ[ℂ] NSiteSpace d (K + L) :=
    LinearMap.pi fun σ ↦
      (LinearMap.proj (σ ∘ Fin.natAdd K) : NSiteSpace d L →ₗ[ℂ] ℂ).comp
        (LinearMap.proj (σ ∘ Fin.castAdd L))
  have hfac {D : ℕ} (B : MPSTensor d D) :
      tailBoundaryMap B K L = T.comp ((groundSpaceMap B L).compLeft (Cfg d K)) := rfl
  simp only [hfac, LinearMap.range_comp, LinearMap.range_compLeft,
    show (groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) L).range =
      ⨆ j, (groundSpaceMap (A j) L).range from
        groundSpace_toTensorFromBlocks_eq_iSup μ A hμ L,
    pi_univ_iSup_const, Submodule.map_iSup]

/-- Adding free sites to the left preserves the sum of the block ground
spaces. This identifies the right interval in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), for a weighted direct sum. -/
theorem range_tailBoundaryMapES_toTensorFromBlocks_eq_iSup
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (K L : ℕ) :
    (tailBoundaryMapES (toTensorFromBlocks (d := d) (μ := μ) A) K L).range =
      ⨆ j, (tailBoundaryMapES (A j) K L).range := by
  simp only [tailBoundaryMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    tailBoundaryMap_range_toTensorFromBlocks μ A hμ, Submodule.map_iSup]

/-- Reassociating three consecutive intervals preserves the sum of the
right interval ground spaces of the blocks. This is the right projector
space in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem range_reassocTailBoundaryMapES_toTensorFromBlocks_eq_iSup
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (K L Q : ℕ) :
    (reassocTailBoundaryMapES (toTensorFromBlocks (d := d) (μ := μ) A) K L Q).range =
      ⨆ j, (reassocTailBoundaryMapES (A j) K L Q).range := by
  simp only [reassocTailBoundaryMapES, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, range_tailBoundaryMapES_toTensorFromBlocks_eq_iSup μ A hμ,
    Submodule.map_iSup]

end MPSTensor
