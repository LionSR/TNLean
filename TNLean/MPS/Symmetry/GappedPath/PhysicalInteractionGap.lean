/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPoint.BondProductSpectralGap
import QICLean.Analysis.Projection.MatrixStarProjection
import TNLean.MPS.Operator.Interaction.GappedInteractionPath
import Mathlib.Analysis.Matrix.Order
import TNLean.MPS.Operator.PhysicalSector.CommutingBondEtaCyclicCore
import TNLean.MPS.FundamentalTheorem.PhysicalSupport.PhysicalSupportProductTransport
import TNLean.MPS.ParentHamiltonian.ParentInteraction.PhysicalEmbedding

/-!
# Spectral gaps for sector-decomposed bond interactions

A one-site Hilbert space may contain unused sectors in addition to the
left and right virtual registers of a matrix product state. A neighboring
interaction still consists of commuting projections if it acts only on
the outgoing right register and incoming left register in each pair of
sectors. Consequently every eigenvalue of its periodic Hamiltonian is `0`
or at least `1`, independently of the chain length.

This is the commuting-projection argument needed when the common physical
space in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, also retains unused physical states. The zero
eigenvalue requires a separate ground-state identification.

## Canonical parents as isometric interaction extensions

The canonical parent of a physically embedded tensor is the isometric
extension of its original parent, with energy one on the unused two-site
space. This identifies the canonical endpoint projections with the local
extensions used in the common physical space of arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym.
-/

section

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace Kronecker

open ManyBody

namespace MPSTensor

/-- A periodic sum of commuting projection-valued interactions satisfies
\(H^2\ge H\). Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2,
the independent-bond parent Hamiltonian. -/
theorem hamiltonian_translationInvariant_quadratic_gap_of_commuting_projection
    {d N : ℕ} (A : MPOTensor.ChainOperator d 2)
    (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A)
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) A))
    (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    (⟪Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian v,
      v⟫_ℂ).re ≤
      (⟪Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian v,
        Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian v⟫_ℂ).re := by
  have : NeZero N := ⟨by omega⟩
  let P (i : Fin N) := (bondMatrixEquiv d N).symm
    (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A)
  have hP (i : Fin N) : (P i).IsSymmetricProjection :=
    bondMatrixEquiv_symm_isSymmetricProjection _
      (hA.map (placeAlongHom (X := fun _ ↦ Fin d) (ringWindow hN i)))
  have hPC (i j : Fin N) : Commute (P i) (P j) :=
    (hcomm i j).map (bondMatrixEquiv d N).symm
  have hcross (i j : Fin N) (w : EuclideanSpace ℂ (Cfg d N)) :
      0 ≤ (⟪P i w, P j w⟫_ℂ).re :=
    LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hP i) (hP j) (fun x => congrArg (fun T => T x) (hPC i j).eq) w
  have h := ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum
    (γ := 1) (by norm_num) P hP (fun _ _ => (0 : ℝ))
    (by intro i; simp)
    (by intro i j hj w; simpa using hcross i j w) v
  simpa only [one_mul, P, ← map_sum, Interaction.hamiltonian_translationInvariant_of_le _ hN,
    bondMatrixEquiv_symm_eq_toEuclideanLin] using h

/-- Every eigenvalue of a periodic sum of commuting projection-valued local
terms is `0` or at least `1`. No ground state is asserted. Source context:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem hamiltonian_translationInvariant_eigenvalue_gap_one_of_commuting_projection
    {d N : ℕ} (A : MPOTensor.ChainOperator d 2)
    (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A)
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) A)) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ :=
  haveI : NeZero N := ⟨by omega⟩
  forall_hasEigenvalue_of_quadratic_gap _
    (Interaction.posSemidef_hamiltonian fun _ ↦
      Matrix.LE.le.posSemidef (Interaction.translationInvariant_term_nonneg hA.nonneg _))
    (hamiltonian_translationInvariant_quadratic_gap_of_commuting_projection A hA hN hcomm)

private theorem sectorBondBlock_isStarProjection {p q : ℕ} {ι : Type*}
    [Fintype ι] (A : Matrix ι ι ℂ) (hA : IsStarProjection A) :
    IsStarProjection (((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ A) ⊗ₖ
      (1 : Matrix (Fin q) (Fin q) ℂ)) := by
  rw [isStarProjection_iff']
  constructor
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hA.isIdempotentElem.eq, mul_one, mul_one]
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one] using congrArg
        (fun M : Matrix ι ι ℂ =>
          ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ M) ⊗ₖ
            (1 : Matrix (Fin q) (Fin q) ℂ)) hA.isSelfAdjoint.star_eq

/-- Assemble a neighboring interaction from its sector matrices, with
identity on the two exterior registers. Source context: arXiv:1010.3732,
Sections II.D.2 and II.F.2; the sector-coordinate formula is the neighboring
operator decomposition of Beigi, J. Phys. A 45 (2012) 025306, Section III,
equations (2)–(3). -/
noncomputable def sectorBondInteraction {K d : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ) :
    MPOTensor.ChainOperator d 2 :=
  Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
    (finTwoArrowEquiv (Fin d)).symm
    (Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e)
      (Matrix.etaPairSpatialBlockEquiv e)
      (Matrix.blockDiagonal' fun qh : Fin K × Fin K =>
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)))

/-- Every pair of periodic translates of a sector-decomposed bond
interaction commutes, including sectors carrying unused physical states.
Source context: arXiv:1010.3732, Section II.F.2; Beigi, J. Phys. A 45 (2012)
025306, Section III, equations (2)–(3). -/
theorem sectorBondInteraction_translate_commute {K d N : ℕ}
    (dl dr : Fin K → ℕ) (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hN : 2 ≤ N) (i j : Fin N) :
    Commute (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (sectorBondInteraction dl dr e η))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) (sectorBondInteraction dl dr e η)) := by
  apply MPOTensor.placeAlong_ringWindow_commute_of_etaPair_decomposition hN dl dr e η
  exact (Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e)
    (Matrix.etaPairSpatialBlockEquiv e)).symm_apply_apply _

/-- Projection-valued neighboring matrices give a projection-valued
sector interaction. In particular, unused sectors may carry the identity
penalty. Source context: arXiv:1010.3732, Section II.F.2; Beigi,
J. Phys. A 45 (2012) 025306, Section III, equations (2)–(3). -/
theorem sectorBondInteraction_isStarProjection {K d : ℕ}
    (dl dr : Fin K → ℕ) (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hη : ∀ q h, IsStarProjection (η q h)) :
    IsStarProjection (sectorBondInteraction dl dr e η) := by
  let B (qh : Fin K × Fin K) :=
    ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
      η qh.1 qh.2) ⊗ₖ
        (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)
  have hB (qh : Fin K × Fin K) : IsStarProjection (B qh) :=
    sectorBondBlock_isStarProjection _ (hη qh.1 qh.2)
  have hIdem : IsIdempotentElem B :=
    funext fun qh => (hB qh).isIdempotentElem.eq
  have hDiag : IsStarProjection (Matrix.blockDiagonal' B) :=
    ⟨hIdem.map (Matrix.blockDiagonal'RingHom _ ℂ),
      (Matrix.isHermitian_blockDiagonal'_iff.mpr
        (fun qh => (hB qh).isSelfAdjoint.isHermitian)).isSelfAdjoint⟩
  exact Matrix.isStarProjection_reindex _ _
    (Matrix.isStarProjection_reindex (Matrix.etaPairSpatialBlockEquiv e) _ hDiag)

/-- Every eigenvalue of every periodic Hamiltonian of a projection-valued
sector bond interaction is `0` or at least `1`, uniformly in its sector
dimensions and chain length. This includes identity penalties on unused
sectors. Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2;
Beigi, J. Phys. A 45 (2012) 025306, Section III, equations (2)–(3). -/
theorem sectorBondInteraction_eigenvalue_gap_one {K d N : ℕ}
    (dl dr : Fin K → ℕ) (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hη : ∀ q h, IsStarProjection (η q h)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (Interaction.translationInvariant N (sectorBondInteraction dl dr e η)).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  let : NeZero N := ⟨by omega⟩
  exact hamiltonian_translationInvariant_eigenvalue_gap_one_of_commuting_projection _
    (sectorBondInteraction_isStarProjection dl dr e η hη) hN
    (sectorBondInteraction_translate_commute dl dr e η hN)

/-- A local Hermitian interaction, transported through a one-site
isometry, intertwines with the isometry on the whole periodic chain.
Source context: arXiv:1010.3732, Section II.F.2, equation
eq:1d-sym:jointsym, physical embeddings. -/
theorem placeAlong_ringWindow_isometry_intertwiner {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian)
    (hN : 2 ≤ N) (i : Fin N) :
    placeAlong (X := fun _ ↦ Fin m) (ringWindow hN i)
        (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ E) A) *
        (Matrix.piKronecker fun _ : Fin N ↦ E) =
      (Matrix.piKronecker fun _ : Fin N ↦ E) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A := by
  have h := MPOTensor.singleKrausMap_placeAlong_ringWindow_eq_range_mul_lift
    E hE hN i A
  have hAdj := congrArg Matrix.conjTranspose h
  have hLocal : ((Matrix.piKronecker fun _ : Fin 2 ↦ E) * A *
      (Matrix.piKronecker fun _ : Fin 2 ↦ E)ᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ hA
  simp only [singleKrausMap_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_one,
    (isHermitian_placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) hA).eq,
    (isHermitian_placeAlong (X := fun _ ↦ Fin m) (ringWindow hN i) hLocal).eq] at hAdj
  have hMul := congrArg (fun M => M * (Matrix.piKronecker fun _ : Fin N ↦ E)) hAdj
  simpa only [singleKrausMap_apply, Matrix.mul_assoc,
    MPOTensor.tensorPower_isometry E hE N,
    Matrix.mul_one] using hMul.symm

/-- Extend a two-site interaction through a physical isometry and give
energy one to the orthogonal complement of the included two-site space.
Equivalently, \(h'=T h T^\dagger+1-TT^\dagger\).
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, physical endpoint embeddings. -/
noncomputable def isometricInteractionExtension {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPOTensor.ChainOperator d 2) :
    MPOTensor.ChainOperator m 2 :=
  1 - singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ E) (1 - A)

/-- Adding the unused-state penalty preserves the intertwining identity
on the included chain. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem embed_isometricInteractionExtension_intertwiner {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian)
    (hN : 2 ≤ N) (i : Fin N) :
    placeAlong (X := fun _ ↦ Fin m) (ringWindow hN i) (isometricInteractionExtension E A) *
        (Matrix.piKronecker fun _ : Fin N ↦ E) =
      (Matrix.piKronecker fun _ : Fin N ↦ E) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A := by
  have h := placeAlong_ringWindow_isometry_intertwiner E hE (1 - A)
    (Matrix.isHermitian_one.sub hA) hN i
  change (placeAlongHom (X := fun _ ↦ Fin m) (ringWindow hN i))
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ E) (1 - A)) *
      (Matrix.piKronecker fun _ : Fin N ↦ E) =
    (Matrix.piKronecker fun _ : Fin N ↦ E) *
      (placeAlongHom (X := fun _ ↦ Fin d) (ringWindow hN i)) (1 - A) at h
  have hSub := congrArg (fun M => (Matrix.piKronecker fun _ : Fin N ↦ E) - M) h
  change (placeAlongHom (X := fun _ ↦ Fin m) (ringWindow hN i))
      (1 - singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ E) (1 - A)) *
      (Matrix.piKronecker fun _ : Fin N ↦ E) =
    (Matrix.piKronecker fun _ : Fin N ↦ E) *
      (placeAlongHom (X := fun _ ↦ Fin d) (ringWindow hN i)) A
  simpa only [map_sub, map_one, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, sub_sub_cancel] using hSub

/-- The enlarged periodic Hamiltonian agrees with the original Hamiltonian
on the isometrically included chain. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem hamiltonian_translationInvariant_isometricInteractionExtension_intertwiner
    {d m N : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian *
        (Matrix.piKronecker fun _ : Fin N ↦ E) =
      (Matrix.piKronecker fun _ : Fin N ↦ E) * (Interaction.translationInvariant N
          A).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  simpa only [Interaction.hamiltonian_translationInvariant_of_le _ hN, Matrix.sum_mul,
    Matrix.mul_sum] using
    Finset.sum_congr rfl (fun i _ =>
      embed_isometricInteractionExtension_intertwiner E hE A hA hN i)

/-- A nonzero zero mode remains a nonzero zero mode after an isometric
physical inclusion with energy one on unused local states.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem isometricInteractionExtension_zero_mode {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N)
    (ψ : Cfg d N → ℂ) (hψ : ψ ≠ 0)
    (hzero : haveI : NeZero N := ⟨by omega⟩;
      (Interaction.translationInvariant N A).hamiltonian.mulVec ψ = 0) :
    haveI : NeZero N := ⟨by omega⟩; (Matrix.piKronecker fun _ : Fin N ↦ E).mulVec ψ ≠ 0 ∧
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian.mulVec
        ((Matrix.piKronecker fun _ : Fin N ↦ E).mulVec ψ) = 0 := by
  have : NeZero N := ⟨by omega⟩
  have h := congrArg (fun M => M.mulVec ψ)
    (hamiltonian_translationInvariant_isometricInteractionExtension_intertwiner E hE A hA hN)
  simp only [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero] at h
  refine ⟨?_, h⟩
  exact fun h0 => hψ (by
    simpa only [Matrix.mulVec_mulVec,
      MPOTensor.tensorPower_isometry E hE N, Matrix.one_mulVec,
      Matrix.mulVec_zero] using
      congrArg (fun v => (Matrix.piKronecker fun _ : Fin N ↦ E)ᴴ.mulVec v) h0)

/-- A nontrivial original zero mode gives zero in the spectrum of the
isometrically enlarged periodic Hamiltonian. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem isometricInteractionExtension_zero_mem_spectrum {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N)
    (ψ : Cfg d N → ℂ) (hψ : ψ ≠ 0)
    (hzero : haveI : NeZero N := ⟨by omega⟩;
      (Interaction.translationInvariant N A).hamiltonian.mulVec ψ = 0) :
    haveI : NeZero N := ⟨by omega⟩; (0 : ℂ) ∈ spectrum ℂ
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hne, hz⟩ := isometricInteractionExtension_zero_mode E hE A hA hN ψ hψ hzero
  simpa only [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩

end MPSTensor

end

section

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- Physical interaction extension preserves the order of local
Hermitian interactions. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, comparison of the embedded parent projections. -/
theorem isometricInteractionExtension_mono {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) {A B : MPOTensor.ChainOperator d 2}
    (hAB : A ≤ B) :
    isometricInteractionExtension E A ≤ isometricInteractionExtension E B := by
  unfold isometricInteractionExtension
  apply sub_le_sub_left
  rw [← sub_nonneg, ← map_sub, sub_sub_sub_cancel_left]
  exact Matrix.nonneg_iff_posSemidef.mpr
    ((singleKrausMap_isKrausCP _).map_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)))

/-- The canonical two-site parent of an isometrically embedded tensor is
the isometric extension of its original parent interaction. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension
    {d m D : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) :
    LinearMap.toMatrix' (parentInteraction (rotatePhysical E A) 2) =
      isometricInteractionExtension E (LinearMap.toMatrix' (parentInteraction A 2)) := by
  rw [parentInteraction_matrix_rotatePhysical_isometry E hE A 2]
  simp only [isometricInteractionExtension, map_sub, singleKrausMap_apply, Matrix.mul_one]
  rw [show Matrix.piKronecker (fun _ : Fin 2 => E) =
    (Matrix.piKronecker fun _ : Fin 2 ↦ E) from rfl]
  abel

end MPSTensor

end
