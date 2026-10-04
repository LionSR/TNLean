/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductSpectralGap
import TNLean.Algebra.MatrixProjectionReindex
import TNLean.MPS.Symmetry.InteractionHamiltonianOrder
import TNLean.MPS.MPDO.CommutingBondEtaCyclicCore
import TNLean.MPS.MPDO.PhysicalSupportProductTransport

/-!
# Spectral gaps for sector-decomposed bond interactions

A one-site Hilbert space may contain unused sectors in addition to the
left and right virtual registers of a matrix product state. A neighboring
interaction still consists of commuting projections if it acts only on
the outgoing right register and incoming left register in each pair of
sectors. Consequently its periodic Hamiltonian has no eigenvalues in
\((0,1)\), independently of the chain length.

This is the commuting-projection argument needed when the common physical
space in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, also retains unused physical states. The zero
spectral value requires a separate ground-state identification.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace Kronecker

namespace MPSTensor

/-- A periodic sum of commuting projection-valued interactions satisfies
\(H^2\ge H\). Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2,
the independent-bond parent Hamiltonian. -/
theorem interactionHamiltonian_quadratic_gap_of_commuting_projection
    {d N : ℕ} (A : MPOTensor.ChainOperator d 2)
    (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A))
    (v : EuclideanSpace ℂ (Cfg d N)) :
    (⟪Matrix.toEuclideanLin (interactionHamiltonian A hN) v, v⟫_ℂ).re ≤
      (⟪Matrix.toEuclideanLin (interactionHamiltonian A hN) v,
        Matrix.toEuclideanLin (interactionHamiltonian A hN) v⟫_ℂ).re := by
  let P (i : Fin N) := (bondMatrixEquiv d N).symm
    (MPOTensor.embedLocalOperator 2 N hN i A)
  have hP (i : Fin N) : (P i).IsSymmetricProjection :=
    bondMatrixEquiv_symm_isSymmetricProjection _
      (MPOTensor.embedLocalOperator_isStarProjection 2 N hN i hA)
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
  simpa only [one_mul, P, ← map_sum, interactionHamiltonian,
    bondMatrixEquiv_symm_eq_toEuclideanLin] using h

/-- The spectrum of a periodic sum of commuting projection-valued local
terms is contained in \(\{0\}\cup[1,\infty)\). Source context:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem interactionHamiltonian_spectrum_gap_one_of_commuting_projection
    {d N : ℕ} (A : MPOTensor.ChainOperator d 2)
    (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A)) :
    ∀ z ∈ spectrum ℂ (interactionHamiltonian A hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) :=
  spectrum_separated_of_quadratic_gap _
    (interactionHamiltonian_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp hA.nonneg) hN)
    (interactionHamiltonian_quadratic_gap_of_commuting_projection A hA hN hcomm)

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
theorem sectorBondInteraction_translate_commute {K d N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ) (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hN : 2 ≤ N) (i j : Fin N) :
    Commute (MPOTensor.embedLocalOperator 2 N hN i (sectorBondInteraction dl dr e η))
      (MPOTensor.embedLocalOperator 2 N hN j (sectorBondInteraction dl dr e η)) := by
  apply MPOTensor.embedLocalOperator_commute_of_etaPair_decomposition hN dl dr e η
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

/-- Every periodic Hamiltonian of a projection-valued sector bond
interaction has spectrum in \(\{0\}\cup[1,\infty)\), uniformly in
its sector dimensions and chain length. This includes identity penalties
on unused sectors. Source context: arXiv:1010.3732, Sections II.D.2 and
II.F.2; Beigi, J. Phys. A 45 (2012) 025306, Section III, equations (2)–(3). -/
theorem sectorBondInteraction_spectrum_gap_one {K d N : ℕ}
    (dl dr : Fin K → ℕ) (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hη : ∀ q h, IsStarProjection (η q h)) (hN : 2 ≤ N) :
    ∀ z ∈ spectrum ℂ (interactionHamiltonian (sectorBondInteraction dl dr e η) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  let : NeZero N := ⟨by omega⟩
  exact interactionHamiltonian_spectrum_gap_one_of_commuting_projection _
    (sectorBondInteraction_isStarProjection dl dr e η hη) hN
    (sectorBondInteraction_translate_commute dl dr e η hN)

/-- A local Hermitian interaction, transported through a one-site
isometry, intertwines with the isometry on the whole periodic chain.
Source context: arXiv:1010.3732, Section II.F.2, equation
eq:1d-sym:jointsym, physical embeddings. -/
theorem embedLocalOperator_isometry_intertwiner {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian)
    (hN : 2 ≤ N) (i : Fin N) :
    MPOTensor.embedLocalOperator 2 N hN i
        (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) A) *
        MPOTensor.sitewisePhysicalMatrix E N =
      MPOTensor.sitewisePhysicalMatrix E N *
        MPOTensor.embedLocalOperator 2 N hN i A := by
  have h := MPOTensor.singleKrausMap_embedLocalOperator_eq_range_mul_lift
    E hE hN i A
  have hAdj := congrArg Matrix.conjTranspose h
  have hLocal : (MPOTensor.sitewisePhysicalMatrix E 2 * A *
      (MPOTensor.sitewisePhysicalMatrix E 2)ᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ hA
  simp only [singleKrausMap_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_one,
    (MPOTensor.embedLocalOperator_isHermitian 2 N hN i hA).eq,
    (MPOTensor.embedLocalOperator_isHermitian 2 N hN i hLocal).eq] at hAdj
  have hMul := congrArg (fun M => M * MPOTensor.sitewisePhysicalMatrix E N) hAdj
  simpa only [singleKrausMap_apply, Matrix.mul_assoc,
    MPOTensor.sitewisePhysicalMatrix_isometry E hE N,
    Matrix.mul_one] using hMul.symm

/-- Extend a two-site interaction through a physical isometry and give
energy one to the orthogonal complement of the included two-site space.
Equivalently, \(h'=T h T^\dagger+1-TT^\dagger\).
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, physical endpoint embeddings. -/
noncomputable def isometricInteractionExtension {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPOTensor.ChainOperator d 2) :
    MPOTensor.ChainOperator m 2 :=
  1 - singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)

/-- Adding the unused-state penalty preserves the intertwining identity
on the included chain. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem embed_isometricInteractionExtension_intertwiner {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian)
    (hN : 2 ≤ N) (i : Fin N) :
    MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A) *
        MPOTensor.sitewisePhysicalMatrix E N =
      MPOTensor.sitewisePhysicalMatrix E N *
        MPOTensor.embedLocalOperator 2 N hN i A := by
  have h := embedLocalOperator_isometry_intertwiner E hE (1 - A)
    (Matrix.isHermitian_one.sub hA) hN i
  change (MPOTensor.embedLocalOperatorAlgHom (d := m) 2 N hN i)
      (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)) *
      MPOTensor.sitewisePhysicalMatrix E N =
    MPOTensor.sitewisePhysicalMatrix E N *
      (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i) (1 - A) at h
  have hSub := congrArg (fun M => MPOTensor.sitewisePhysicalMatrix E N - M) h
  change (MPOTensor.embedLocalOperatorAlgHom (d := m) 2 N hN i)
      (1 - singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)) *
      MPOTensor.sitewisePhysicalMatrix E N =
    MPOTensor.sitewisePhysicalMatrix E N *
      (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i) A
  simpa only [map_sub, map_one, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, sub_sub_cancel] using hSub

/-- The enlarged periodic Hamiltonian agrees with the original Hamiltonian
on the isometrically included chain. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem interactionHamiltonian_isometricInteractionExtension_intertwiner
    {d m N : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N) :
    interactionHamiltonian (isometricInteractionExtension E A) hN *
        MPOTensor.sitewisePhysicalMatrix E N =
      MPOTensor.sitewisePhysicalMatrix E N * interactionHamiltonian A hN := by
  simpa only [interactionHamiltonian, Matrix.sum_mul, Matrix.mul_sum] using
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
    (hzero : (interactionHamiltonian A hN).mulVec ψ = 0) :
    (MPOTensor.sitewisePhysicalMatrix E N).mulVec ψ ≠ 0 ∧
      (interactionHamiltonian (isometricInteractionExtension E A) hN).mulVec
        ((MPOTensor.sitewisePhysicalMatrix E N).mulVec ψ) = 0 := by
  have h := congrArg (fun M => M.mulVec ψ)
    (interactionHamiltonian_isometricInteractionExtension_intertwiner E hE A hA hN)
  simp only [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero] at h
  refine ⟨?_, h⟩
  exact fun h0 => hψ (by
    simpa only [Matrix.mulVec_mulVec,
      MPOTensor.sitewisePhysicalMatrix_isometry E hE N, Matrix.one_mulVec,
      Matrix.mulVec_zero] using
      congrArg (fun v => (MPOTensor.sitewisePhysicalMatrix E N)ᴴ.mulVec v) h0)

/-- A nontrivial original zero mode gives zero in the spectrum of the
isometrically enlarged periodic Hamiltonian. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem isometricInteractionExtension_zero_mem_spectrum {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N)
    (ψ : Cfg d N → ℂ) (hψ : ψ ≠ 0)
    (hzero : (interactionHamiltonian A hN).mulVec ψ = 0) :
    (0 : ℂ) ∈ spectrum ℂ
      (interactionHamiltonian (isometricInteractionExtension E A) hN) := by
  obtain ⟨hne, hz⟩ := isometricInteractionExtension_zero_mode E hE A hA hN ψ hψ hzero
  simpa only [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩

end MPSTensor
