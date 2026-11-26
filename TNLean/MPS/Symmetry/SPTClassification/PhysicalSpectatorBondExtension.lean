/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedPath.PhysicalInteractionGap
import TNLean.MPS.Symmetry.SPTClassification.PhysicalSpectatorCoordinates
import TNLean.MPS.Symmetry.FixedPoint.TwoSiteBondInteraction
import TNLean.MPS.Symmetry.SPTClassification.CommonPhysicalEndpoints

/-!
# Independent virtual bonds with additional physical sectors

The active virtual-pair sector carries the original independent-bond
interaction. Every neighboring pair that meets either additional physical
sector carries the identity penalty. This realizes the unused-state
penalty in the common physical space of arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, in coordinates where neighboring terms commute.

It also contains the following results.

* `MPSTensor.commonFixedPointInclusion_eq_coordinateInclusion`,
  `MPSTensor.physicalSpectatorBondInteraction_eq_isometricInteractionExtension`: identifying the
  physical spectator interaction.
-/

section PhysicalSpectatorBondExtension

open scoped Matrix Kronecker ComplexOrder

open ManyBody

namespace Matrix

/-- The active pair carries the prescribed virtual bond; every pair
meeting an additional physical sector carries the identity. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def _root_.TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) (q h : Fin 3) :
    Matrix (EtaEdgeIndex ![K, d₀, d₁] ![K, 1, 1] q h)
      (EtaEdgeIndex ![K, d₀, d₁] ![K, 1, 1] q h) ℂ :=
  if hq : q = 0 then
    if hh : h = 0 then by
      subst q
      subst h
      exact B
    else 1
  else 1

/-- Projection-valued active bonds give projection-valued interactions
on every pair of sectors. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem _root_.TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction_isStarProjection (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) (q h : Fin 3) :
    IsStarProjection (TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction K d₀ d₁ B q h) := by
  unfold TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction
  split_ifs with hq hh
  · subst q
    subst h
    exact hB
  all_goals exact IsStarProjection.one _

end Matrix

namespace MPSTensor

/-- Place a virtual bond in the active sector and penalize all other
pairs of sectors by the identity. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def physicalSpectatorBondInteraction (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    MPOTensor.ChainOperator ((K * K + d₀) + d₁) 2 :=
  sectorBondInteraction ![K, d₀, d₁] ![K, 1, 1]
    (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁)
    (TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction K d₀ d₁ B)

/-- An orthogonal-projection virtual bond gives an orthogonal-projection
interaction on the common physical space. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_isStarProjection (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) :
    IsStarProjection (physicalSpectatorBondInteraction K d₀ d₁ B) := by
  exact sectorBondInteraction_isStarProjection _ _ _ _
    (TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction_isStarProjection K d₀ d₁ B hB)

/-- All periodic translates of the extended independent-bond interaction
commute. Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_translate_commute {N : ℕ}
    (K d₀ d₁ : ℕ) (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hN : 2 ≤ N) (i j : Fin N) :
    Commute (placeAlong (X := fun _ ↦ Fin ((K * K + d₀) + d₁)) (ringWindow hN i)
      (physicalSpectatorBondInteraction K d₀ d₁ B))
      (placeAlong (X := fun _ ↦ Fin ((K * K + d₀) + d₁)) (ringWindow hN j)
        (physicalSpectatorBondInteraction K d₀ d₁ B)) := by
  exact sectorBondInteraction_translate_commute _ _ _ _ hN i j

/-- Every eigenvalue of the enlarged independent-bond Hamiltonian is `0` or
at least `1`, uniformly in the chain length and in the dimensions of the
additional physical sectors. Source context: arXiv:1010.3732, Sections II.D.2
and II.F.2, equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_eigenvalue_gap_one {N : ℕ}
    (K d₀ d₁ : ℕ) (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (Interaction.translationInvariant N
          (physicalSpectatorBondInteraction K d₀ d₁ B)).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  exact sectorBondInteraction_eigenvalue_gap_one _ _ _ _
    (TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction_isStarProjection K d₀ d₁ B hB) hN

end MPSTensor

end PhysicalSpectatorBondExtension

section PhysicalSpectatorBondTransport

/-!
## Identifying the physical spectator interaction

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
        (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁ x) (finProdFinEquiv (l, r)) =
      if x = ⟨0, (r, l)⟩ then 1 else 0 := by
  rw [commonFixedPointInclusion_eq_coordinateInclusion]
  change (if TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁ x =
      TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁ ⟨0, (r, l)⟩ then 1 else 0) =
    if x = ⟨0, (r, l)⟩ then 1 else 0
  simp only [(TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁).injective.eq_iff]

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
  (Matrix.etaPairSpatialBlockEquiv (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁)).trans
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
private theorem piKronecker_commonFixedPointInclusion_sector
    (K d₀ d₁ : ℕ) :
    (Matrix.piKronecker fun _ : Fin 2 ↦ (commonFixedPointInclusion (K * K) d₀ d₁)).submatrix
        ((Matrix.etaPairSpatialBlockEquiv (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁)).trans
          (finTwoArrowEquiv (Fin ((K * K + d₀) + d₁))).symm)
        (twoSiteBondEquiv K).symm =
      Matrix.coordinateInclusion (activePairEmbedding K d₀ d₁) := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.piKronecker_apply, Fin.prod_univ_two,
    Equiv.trans_apply, Matrix.etaPairSpatialBlockEquiv, finTwoArrowEquiv_symm_apply,
    twoSiteBondEquiv, Matrix.cons_val_zero, Matrix.cons_val_one]
  change commonFixedPointInclusion (K * K) d₀ d₁
      (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁ ⟨x.1.1, (x.2.1.2.1, x.2.1.1)⟩)
        (finProdFinEquiv (y.1.1, y.1.2.1)) *
    commonFixedPointInclusion (K * K) d₀ d₁
      (TNLean.MPS.Symmetry.physicalSpectatorEquiv K d₀ d₁ ⟨x.1.2, (x.2.2, x.2.1.2.2)⟩)
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
    TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction K d₀ d₁ B qh.1 qh.2) ⊗ₖ
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
    TNLean.MPS.Symmetry.physicalSpectatorEdgeInteraction, Pi.single]

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
        (Matrix.piKronecker fun _ : Fin 2 ↦ (commonFixedPointInclusion (K * K) d₀ d₁)) =
      Matrix.coordinateInclusion (activePairEmbedding K d₀ d₁) from
        piKronecker_commonFixedPointInclusion_sector K d₀ d₁]
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

end PhysicalSpectatorBondTransport
