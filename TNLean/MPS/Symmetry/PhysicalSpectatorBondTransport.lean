/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CommonPhysicalEndpoints
import TNLean.MPS.Symmetry.PhysicalSpectatorCoordinates
import TNLean.MPS.Symmetry.TwoSiteBondInteraction
import TNLean.MPS.Symmetry.PhysicalSpectatorBondExtension

/-!
# Identifying the physical spectator interaction

The sector bond interaction is the original two-site bond interaction on
the included active space, with identity on its orthogonal complement.
Thus its sector construction agrees with the physical isometric extension.

Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2,
equation eq:1d-sym:jointsym.
-/

open scoped Matrix Kronecker
namespace MPSTensor

private theorem physicalSumInclusion_eq_coordinateInclusion (m d : ℕ) :
    physicalSumInclusion m d = Matrix.coordinateInclusion (Fin.castAddEmb d) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [physicalSumInclusion, Matrix.coordinateInclusion,
    Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff]
  omega

/-- The shared active-space inclusion is the coordinate inclusion into
the first physical summand. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonFixedPointInclusion_eq_coordinateInclusion (m d₀ d₁ : ℕ) :
    commonFixedPointInclusion m d₀ d₁ = Matrix.coordinateInclusion
      ((Fin.castAddEmb d₀).trans (Fin.castAddEmb d₁)) := by
  rw [commonFixedPointInclusion, physicalSumInclusion_eq_coordinateInclusion,
    physicalSumInclusion_eq_coordinateInclusion, Matrix.mul_coordinateInclusion]
  rfl

private theorem commonFixedPointInclusion_eta_apply (K d₀ d₁ : ℕ)
    (x : Matrix.EtaSiteIndex 3 ![K, d₀, d₁] ![K, 1, 1]) (l r : Fin K) :
    commonFixedPointInclusion (K * K) d₀ d₁
        (Matrix.physicalSpectatorEquiv K d₀ d₁ x) (finProdFinEquiv (l, r)) =
      if x = ⟨0, (r, l)⟩ then 1 else 0 := by
  rw [commonFixedPointInclusion_eq_coordinateInclusion]
  change (if Matrix.physicalSpectatorEquiv K d₀ d₁ x =
      Matrix.physicalSpectatorEquiv K d₀ d₁ ⟨0, (r, l)⟩ then 1 else 0) =
    if x = ⟨0, (r, l)⟩ then 1 else 0
  simp only [(Matrix.physicalSpectatorEquiv K d₀ d₁).injective.eq_iff]

private abbrev SpectatorPairSpace (K d₀ d₁ : ℕ) (qh : Fin 3 × Fin 3) :=
  ((Fin (![K, d₀, d₁] qh.1) ×
    (Fin (![K, 1, 1] qh.1) × Fin (![K, d₀, d₁] qh.2))) × Fin (![K, 1, 1] qh.2))

private abbrev SpectatorPairIndex (K d₀ d₁ : ℕ) :=
  (qh : Fin 3 × Fin 3) × SpectatorPairSpace K d₀ d₁ qh

private def activePairEmbedding (K d₀ d₁ : ℕ) :
    ((Fin K × (Fin K × Fin K)) × Fin K) ↪ SpectatorPairIndex K d₀ d₁ :=
  Function.Embedding.sigmaMk (α := Fin 3 × Fin 3)
    (β := fun qh => ((Fin (![K, d₀, d₁] qh.1) ×
      (Fin (![K, 1, 1] qh.1) × Fin (![K, d₀, d₁] qh.2))) × Fin (![K, 1, 1] qh.2)))
    (0, 0)

private def spectatorPairConfigurationEquiv (K d₀ d₁ : ℕ) :
    SpectatorPairIndex K d₀ d₁ ≃ Cfg ((K * K + d₀) + d₁) 2 :=
  (Matrix.etaPairSpatialBlockEquiv (Matrix.physicalSpectatorEquiv K d₀ d₁)).trans
    (finTwoArrowEquiv (Fin ((K * K + d₀) + d₁))).symm

private theorem singleKrausMap_coordinateInclusion_sigmaMk
    {α : Type*} {β : α → Type*} [Fintype α] [DecidableEq α]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (q : α) (C : Matrix (β q) (β q) ℂ) :
    singleKrausMap (Matrix.coordinateInclusion (Function.Embedding.sigmaMk q)) C =
      Matrix.blockDiagonal' (Pi.single q C) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases hi : i = q
  · subst i
    rcases eq_or_ne j q with rfl | hj
    · simp [singleKrausMap_apply, Matrix.coordinateInclusion, Function.Embedding.sigmaMk,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply,
        Sigma.mk.injEq, ite_mul, mul_ite]
    · simp [singleKrausMap_apply, Matrix.coordinateInclusion, Function.Embedding.sigmaMk,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply,
        Sigma.mk.injEq, hj, hj.symm]
  · simp [singleKrausMap_apply, Matrix.coordinateInclusion, Function.Embedding.sigmaMk,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply,
      Sigma.mk.injEq, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem sitewisePhysicalMatrix_commonFixedPointInclusion_sector
    (K d₀ d₁ : ℕ) :
    (MPOTensor.sitewisePhysicalMatrix (commonFixedPointInclusion (K * K) d₀ d₁) 2).submatrix
        ((Matrix.etaPairSpatialBlockEquiv (Matrix.physicalSpectatorEquiv K d₀ d₁)).trans
          (finTwoArrowEquiv (Fin ((K * K + d₀) + d₁))).symm)
        (twoSiteBondEquiv K).symm =
      Matrix.coordinateInclusion (activePairEmbedding K d₀ d₁) := by
  ext x y
  simp only [Matrix.submatrix_apply, MPOTensor.sitewisePhysicalMatrix, Fin.prod_univ_two,
    Equiv.trans_apply, Matrix.etaPairSpatialBlockEquiv, finTwoArrowEquiv_symm_apply,
    twoSiteBondEquiv, Matrix.cons_val_zero, Matrix.cons_val_one]
  change commonFixedPointInclusion (K * K) d₀ d₁
      (Matrix.physicalSpectatorEquiv K d₀ d₁ ⟨x.1.1, (x.2.1.2.1, x.2.1.1)⟩)
        (finProdFinEquiv (y.1.1, y.1.2.1)) *
    commonFixedPointInclusion (K * K) d₀ d₁
      (Matrix.physicalSpectatorEquiv K d₀ d₁ ⟨x.1.2, (x.2.2, x.2.1.2.2)⟩)
        (finProdFinEquiv (y.1.2.2, y.2)) =
      Matrix.coordinateInclusion (activePairEmbedding K d₀ d₁) x y
  simp only [commonFixedPointInclusion_eta_apply]
  rcases x with ⟨⟨q, h⟩, x⟩
  revert x
  fin_cases q <;> fin_cases h <;> intro x <;> simp [Matrix.coordinateInclusion, activePairEmbedding,
    Function.Embedding.sigmaMk, Sigma.mk.injEq]
  simp [Prod.ext_iff, ← ite_and, and_assoc, and_left_comm, and_comm]

private noncomputable def spectatorBondBlocks (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    (qh : Fin 3 × Fin 3) →
      Matrix (SpectatorPairSpace K d₀ d₁ qh) (SpectatorPairSpace K d₀ d₁ qh) ℂ :=
  fun qh => ((1 : Matrix (Fin (![K, d₀, d₁] qh.1)) (Fin (![K, d₀, d₁] qh.1)) ℂ) ⊗ₖ
    Matrix.physicalSpectatorEdgeInteraction K d₀ d₁ B qh.1 qh.2) ⊗ₖ
      (1 : Matrix (Fin (![K, 1, 1] qh.2)) (Fin (![K, 1, 1] qh.2)) ℂ)

set_option backward.isDefEq.respectTransparency false in
private theorem spectatorBondBlocks_complement (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    1 - spectatorBondBlocks K d₀ d₁ B =
      Pi.single (0, 0)
        (1 - (((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ B) ⊗ₖ
          (1 : Matrix (Fin K) (Fin K) ℂ))) := by
  funext qh
  rcases qh with ⟨q, h⟩
  fin_cases q <;> fin_cases h <;> simp [spectatorBondBlocks,
    Matrix.physicalSpectatorEdgeInteraction, Pi.single]

private theorem physicalSpectatorBondInteraction_sector (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    Matrix.reindex (spectatorPairConfigurationEquiv K d₀ d₁).symm
        (spectatorPairConfigurationEquiv K d₀ d₁).symm
        (physicalSpectatorBondInteraction K d₀ d₁ B) =
      Matrix.blockDiagonal' (spectatorBondBlocks K d₀ d₁ B) := by
  convert (Matrix.reindex (spectatorPairConfigurationEquiv K d₀ d₁)
    (spectatorPairConfigurationEquiv K d₀ d₁)).symm_apply_apply
      (Matrix.blockDiagonal' (spectatorBondBlocks K d₀ d₁ B)) using 1
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sector construction of the physical spectator interaction agrees
with the isometric extension through the actual common active-space
inclusion. No condition on the virtual bond matrix is required.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_eq_isometricInteractionExtension (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    physicalSpectatorBondInteraction K d₀ d₁ B =
      isometricInteractionExtension (commonFixedPointInclusion (K * K) d₀ d₁)
        (twoSiteBondInteraction B) := by
  apply (Matrix.reindexRingEquiv ℂ (spectatorPairConfigurationEquiv K d₀ d₁).symm).injective
  rw [isometricInteractionExtension, map_sub, map_one]
  simp only [Matrix.coe_reindexRingEquiv, physicalSpectatorBondInteraction_sector]
  rw [Matrix.reindex_singleKrausMap (twoSiteBondEquiv K)]
  rw [show Matrix.reindex (spectatorPairConfigurationEquiv K d₀ d₁).symm
      (twoSiteBondEquiv K)
        (MPOTensor.sitewisePhysicalMatrix (commonFixedPointInclusion (K * K) d₀ d₁) 2) =
      Matrix.coordinateInclusion (activePairEmbedding K d₀ d₁) from
        sitewisePhysicalMatrix_commonFixedPointInclusion_sector K d₀ d₁]
  rw [← Matrix.coe_reindexRingEquiv, map_sub, map_one]
  simp only [Matrix.coe_reindexRingEquiv, twoSiteBondInteraction,
    ← Matrix.reindex_symm, Equiv.apply_symm_apply]
  have hcorner := singleKrausMap_coordinateInclusion_sigmaMk
    (β := SpectatorPairSpace K d₀ d₁) (0, 0)
    ((1 - (((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ B) ⊗ₖ
      (1 : Matrix (Fin K) (Fin K) ℂ))) :
        Matrix ((Fin K × (Fin K × Fin K)) × Fin K)
          ((Fin K × (Fin K × Fin K)) × Fin K) ℂ)
  convert congrArg (fun M : Matrix (SpectatorPairIndex K d₀ d₁)
    (SpectatorPairIndex K d₀ d₁) ℂ => 1 - M) hcorner.symm using 1
  · simp only [← spectatorBondBlocks_complement,
      Matrix.blockDiagonal'_sub, Matrix.blockDiagonal'_one, sub_sub_self]
  · rfl

end MPSTensor
