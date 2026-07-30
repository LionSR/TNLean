/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaDecomposition
import TNLean.MPS.MPDO.FixedBondProductTensor
import TNLean.MPS.MPDO.PhysicalSectorProductTransport

/-!
# Positive physical sectors retained by the fixed-product constructor

This file constructs a fixed-product tensor together with the Beigi spatial
decomposition used to build it.  The retained local witness is an explicit
`PhysicalSectorFactorization` whose neighboring operators are the positive
matrices in the commuting-bond decomposition.

## Main definitions and statements

* `TranslationInvariantBondData.PositivePhysicalSectorFixedProductTensorData`
  packages the exact tensor and its retained positive physical sectors.
* `TranslationInvariantBondData.nonempty_positivePhysicalSectorFixedProductTensorData`
  constructs the enriched fixed-product witness.
* `TranslationInvariantBondData.positivePhysicalSectorFixedProductTensorData`
  selects one enriched witness.

## References

* arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1605.
* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor.TranslationInvariantBondData

variable {d : ℕ}

private abbrev EtaRightMatrixUnitIndex {K : ℕ} (dr : Fin K → ℕ) :=
  Σ q : Fin K, Fin (dr q) × Fin (dr q)

private abbrev EtaLeftMatrixUnitIndex {K : ℕ} (dl : Fin K → ℕ) :=
  Σ h : Fin K, Fin (dl h) × Fin (dl h)

/-- The virtual index for the matrix-unit expansion of all neighboring
operators.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private abbrev EtaFactorIndex {K : ℕ} (dl dr : Fin K → ℕ) :=
  EtaRightMatrixUnitIndex dr × EtaLeftMatrixUnitIndex dl

/-- A nonempty physical space gives a genuine matrix-unit virtual index.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private theorem etaFactorIndex_nonempty {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d) (hd : d ≠ 0) :
    Nonempty (EtaFactorIndex dl dr) := by
  let z := e.symm ⟨0, Nat.pos_of_ne_zero hd⟩
  exact ⟨(⟨z.1, (z.2.1, z.2.1)⟩, ⟨z.1, (z.2.2, z.2.2)⟩)⟩

private noncomputable def etaRightFactor {K : ℕ} {dl dr : Fin K → ℕ}
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (q : Fin K) (a : EtaFactorIndex dl dr) :
    Matrix (Fin (dr q)) (Fin (dr q)) ℂ :=
  fun r r' ↦
    if ⟨q, (r, r')⟩ = a.1 then
      η a.1.1 a.2.1 (a.1.2.1, a.2.2.1) (a.1.2.2, a.2.2.2)
    else 0

private noncomputable def etaLeftFactor {K : ℕ} {dl dr : Fin K → ℕ}
    (h : Fin K) (a : EtaFactorIndex dl dr) :
    Matrix (Fin (dl h)) (Fin (dl h)) ℂ :=
  fun l l' ↦ if ⟨h, (l, l')⟩ = a.2 then 1 else 0

private theorem sum_etaRightFactor_mul_etaLeftFactor {K : ℕ}
    {dl dr : Fin K → ℕ}
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (q h : Fin K) (r r' : Fin (dr q)) (l l' : Fin (dl h)) :
    ∑ a : EtaFactorIndex dl dr,
        etaRightFactor η q a r r' * etaLeftFactor h a l l' =
      η q h (r, l) (r', l') := by
  simp [etaRightFactor, etaLeftFactor, Fintype.sum_prod_type]

private noncomputable def etaFactorFinEquiv {K : ℕ} (dl dr : Fin K → ℕ) :
    Fin (Fintype.card (EtaFactorIndex dl dr)) ≃ EtaFactorIndex dl dr :=
  (Fintype.equivFin _).symm

private noncomputable def etaRightFactorFin {K : ℕ} {dl dr : Fin K → ℕ}
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (q : Fin K) (a : Fin (Fintype.card (EtaFactorIndex dl dr))) :
    Matrix (Fin (dr q)) (Fin (dr q)) ℂ :=
  etaRightFactor η q (etaFactorFinEquiv dl dr a)

private noncomputable def etaLeftFactorFin {K : ℕ} {dl dr : Fin K → ℕ}
    (h : Fin K) (a : Fin (Fintype.card (EtaFactorIndex dl dr))) :
    Matrix (Fin (dl h)) (Fin (dl h)) ℂ :=
  etaLeftFactor h (etaFactorFinEquiv dl dr a)

private theorem sum_etaRightFactorFin_mul_etaLeftFactorFin {K : ℕ}
    {dl dr : Fin K → ℕ}
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (q h : Fin K) (r r' : Fin (dr q)) (l l' : Fin (dl h)) :
    ∑ a : Fin (Fintype.card (EtaFactorIndex dl dr)),
        (etaRightFactorFin η q a) r r' * (etaLeftFactorFin h a) l l' =
      η q h (r, l) (r', l') := by
  simpa only [etaRightFactorFin, etaLeftFactorFin] using
    ((etaFactorFinEquiv dl dr).sum_comp fun a : EtaFactorIndex dl dr ↦
      (etaRightFactor η q a) r r' * (etaLeftFactor h a) l l').trans
        (sum_etaRightFactor_mul_etaLeftFactor η q h r r' l l')

private def etaPhysicalSectorEquiv {K : ℕ} {dl dr : Fin K → ℕ}
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d) :
    Fin d ≃ Σ q : Fin K, Fin (dl q) × Fin (dr q) :=
  e.symm.trans (Equiv.sigmaCongrRight fun _ ↦ Equiv.prodComm _ _)

private noncomputable def positiveEtaSectorTensor {K : ℕ}
    (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ) :
    MPOTensor d (Fintype.card (EtaFactorIndex dl dr)) :=
  fun i j beta alpha ↦
    Matrix.blockDiagonal' (fun q : Fin K ↦
      etaLeftFactorFin q beta ⊗ₖ etaRightFactorFin η q alpha)
        (etaPhysicalSectorEquiv e i) (etaPhysicalSectorEquiv e j)

private noncomputable def positiveEtaPhysicalTensor {K : ℕ}
    (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ) :
    MPOTensor d (Fintype.card (EtaFactorIndex dl dr)) :=
  PhysicalSectorFactorization.changePhysicalBasis U
    (positiveEtaSectorTensor dl dr e η)

private noncomputable def positiveEtaPhysicalSectorFactorization {K : ℕ}
    (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q) :
    PhysicalSectorFactorization
      (positiveEtaPhysicalTensor dl dr e U η) where
  sectorCount := K
  leftDim := dl
  rightDim := dr
  leftDim_pos := hdl
  rightDim_pos := hdr
  sectorEquiv := etaPhysicalSectorEquiv e
  physicalIsometry := Uᴴ
  physicalIsometry_isometry := by
    rw [Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  leftTensor := etaLeftFactorFin
  rightTensor := etaRightFactorFin η
  factorization := by
    intro beta alpha
    have hUiso : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff'.mp hU)
    change Matrix.reindex (etaPhysicalSectorEquiv e) (etaPhysicalSectorEquiv e)
        (Uᴴ * (U * physicalSlice (positiveEtaSectorTensor dl dr e η) beta alpha *
          Uᴴ) * (Uᴴ)ᴴ) =
      Matrix.blockDiagonal' fun k ↦
        etaLeftFactorFin k beta ⊗ₖ etaRightFactorFin η k alpha
    rw [Matrix.conjTranspose_conjTranspose]
    have hcancel :
        Uᴴ * (U * physicalSlice (positiveEtaSectorTensor dl dr e η) beta alpha *
          Uᴴ) * U =
        physicalSlice (positiveEtaSectorTensor dl dr e η) beta alpha := by
      calc
        _ = (Uᴴ * U) *
            physicalSlice (positiveEtaSectorTensor dl dr e η) beta alpha *
              (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hUiso, Matrix.one_mul, Matrix.mul_one]
    rw [hcancel]
    ext x y
    change Matrix.blockDiagonal' (fun k : Fin K ↦
        etaLeftFactorFin k beta ⊗ₖ etaRightFactorFin η k alpha)
          (etaPhysicalSectorEquiv e ((etaPhysicalSectorEquiv e).symm x))
          (etaPhysicalSectorEquiv e ((etaPhysicalSectorEquiv e).symm y)) =
      Matrix.blockDiagonal' (fun k : Fin K ↦
        etaLeftFactorFin k beta ⊗ₖ etaRightFactorFin η k alpha) x y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem positiveEtaPhysicalSectorFactorization_neighboringOperator
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q)
    (q h : Fin K) :
    (positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
      |>.neighboringOperator q h) = η q h := by
  ext ⟨r, l⟩ ⟨r', l'⟩
  exact sum_etaRightFactorFin_mul_etaLeftFactorFin η q h r r' l l'

/-- The two-site physical coordinate matrix is the reindexed tensor square
of the Beigi unitary.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III. -/
private theorem positiveEtaPhysicalSectorFactorization_coordinateTwo
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    F.physicalCoordinateMatrixTwo =
      Matrix.reindex
        (Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv)
        (Equiv.refl (Fin d × Fin d)) (Uᴴ ⊗ₖ Uᴴ) := by
  dsimp only
  rw [PhysicalSectorFactorization.physicalCoordinateMatrixTwo,
    PhysicalSectorFactorization.physicalCoordinateMatrix,
    Matrix.kroneckerMap_reindex]
  rfl

/-- Conjugating the input pair bond by the retained physical coordinates is
the reindexed Beigi-conjugated bond.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III; arXiv:1606.00608,
equation `sigmaNK2`, lines 1581--1589. -/
private theorem positiveEtaPhysicalSectorFactorization_conjugate_pairBond
    (data : TranslationInvariantBondData d)
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    singleKrausMap F.physicalCoordinateMatrixTwo data.pairBond =
      Matrix.reindex
        (Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv)
        (Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv)
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) := by
  dsimp only
  rw [positiveEtaPhysicalSectorFactorization_coordinateTwo]
  let E := Equiv.prodCongr
    (positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
      |>.physicalFinEquiv)
    (positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
      |>.physicalFinEquiv)
  calc
    singleKrausMap (Matrix.reindex E (Equiv.refl _) (Uᴴ ⊗ₖ Uᴴ))
        data.pairBond =
      Matrix.reindex E E
        (singleKrausMap (Uᴴ ⊗ₖ Uᴴ) data.pairBond) := by
          rw [Matrix.reindex_singleKrausMap (Equiv.refl _) E]
          rfl
    _ = Matrix.reindex E E
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) := by
      congr 1
      simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose]

/-- The retained eta-pair coordinates are the Beigi coordinates followed by
the finite encoding used by `PhysicalSectorFactorization`. -/
private theorem positiveEtaPhysicalSectorFactorization_etaPairEquiv
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv =
      (Matrix.etaPairSpatialBlockEquiv e).trans
        (Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv) := by
  let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
  have hsite (z : Matrix.EtaSiteIndex K dl dr) :
      F.physicalFinEquiv (e z) = F.etaSectorFinEquiv z := by
    rw [PhysicalSectorFactorization.physicalFinEquiv,
      PhysicalSectorFactorization.etaSectorFinEquiv]
    change F.sectorFinEquiv.symm (F.sectorEquiv (e z)) =
      F.sectorFinEquiv.symm
        ((Equiv.sigmaCongrRight fun _ ↦ Equiv.prodComm _ _) z)
    congr 1
    change etaPhysicalSectorEquiv e (e z) =
      (Equiv.sigmaCongrRight fun _ ↦ Equiv.prodComm _ _) z
    simp [etaPhysicalSectorEquiv]
  change Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv =
    (Matrix.etaPairSpatialBlockEquiv e).trans
      (Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv)
  apply Equiv.ext
  rintro ⟨⟨q, h⟩, ⟨⟨lq, rq, lh⟩, rh⟩⟩
  apply Prod.ext
  · change F.etaSectorFinEquiv ⟨q, (rq, lq)⟩ =
      F.physicalFinEquiv (e ⟨q, (rq, lq)⟩)
    exact (hsite ⟨q, (rq, lq)⟩).symm
  · change F.etaSectorFinEquiv ⟨h, (rh, lh)⟩ =
      F.physicalFinEquiv (e ⟨h, (rh, lh)⟩)
    exact (hsite ⟨h, (rh, lh)⟩).symm

/-- The retained sector bond is exactly the input pair bond conjugated into
the physical-sector coordinates.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589; Beigi,
J. Phys. A 45 (2012) 025306, Section III. -/
private theorem positiveEtaPhysicalSectorFactorization_sectorBond_eq
    (data : TranslationInvariantBondData d)
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    F.sectorCoordinateBond =
      singleKrausMap F.physicalCoordinateMatrixTwo data.pairBond := by
  let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
  have hneighbor (q h : Fin K) : F.neighboringOperator q h = η q h :=
    positiveEtaPhysicalSectorFactorization_neighboringOperator
      dl dr e U η hU hdl hdr q h
  change F.sectorCoordinateBond =
    singleKrausMap F.physicalCoordinateMatrixTwo data.pairBond
  apply (Matrix.reindex (Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv).symm
    (Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv).symm).injective
  rw [F.sectorCoordinateBond_etaPair_decomposition]
  simp_rw [hneighbor]
  rw [positiveEtaPhysicalSectorFactorization_conjugate_pairBond]
  rw [positiveEtaPhysicalSectorFactorization_etaPairEquiv]
  let E := Equiv.prodCongr F.physicalFinEquiv F.physicalFinEquiv
  have hindex (z) :
      E.symm (((Matrix.etaPairSpatialBlockEquiv e).trans E) z) =
        Matrix.etaPairSpatialBlockEquiv e z := by
    exact E.symm_apply_apply _
  dsimp only [E] at hindex
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm]
  change (Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
      ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
        η qh.1 qh.2) ⊗ₖ
          (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) x y =
    (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
      (E.symm (((Matrix.etaPairSpatialBlockEquiv e).trans E) x))
      (E.symm (((Matrix.etaPairSpatialBlockEquiv e).trans E) y))
  rw [hindex x, hindex y]
  exact (congrFun (congrFun hB x) y).symm

/-- Transporting the retained sector bond back to the physical coordinates
recovers the input pair bond exactly.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private theorem positiveEtaPhysicalSectorFactorization_physicalPairBond_eq
    (data : TranslationInvariantBondData d)
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    F.physicalPairBond = data.pairBond := by
  let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
  change F.physicalPairBond = data.pairBond
  rw [PhysicalSectorFactorization.physicalPairBond,
    positiveEtaPhysicalSectorFactorization_sectorBond_eq
      data dl dr e U η hU hdl hdr hB]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    F.physicalCoordinateMatrixTwoᴴ *
          (F.physicalCoordinateMatrixTwo * data.pairBond *
            F.physicalCoordinateMatrixTwoᴴ) *
        F.physicalCoordinateMatrixTwo =
      (F.physicalCoordinateMatrixTwoᴴ * F.physicalCoordinateMatrixTwo) *
        data.pairBond *
          (F.physicalCoordinateMatrixTwoᴴ * F.physicalCoordinateMatrixTwo) := by
            simp only [Matrix.mul_assoc]
    _ = data.pairBond := by
      rw [F.physicalCoordinateMatrixTwo_isometry,
        Matrix.one_mul, Matrix.mul_one]

/-- The physical-sector bond of the retained factorization is the input bond.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private theorem positiveEtaPhysicalSectorFactorization_physicalBond_eq
    (data : TranslationInvariantBondData d)
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    F.physicalBond = data.bond := by
  let F := positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
  change F.physicalBond = data.bond
  rw [PhysicalSectorFactorization.physicalBond,
    positiveEtaPhysicalSectorFactorization_physicalPairBond_eq
      data dl dr e U η hU hdl hdr hB]
  exact (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).symm_apply_apply data.bond

/-- The unique tensor on the empty physical space with one virtual state.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private def emptyPhysicalTensor : MPOTensor 0 1 :=
  fun i _ _ _ ↦ Fin.elim0 i

/-- The zero-sector factorization of the tensor on the empty physical space.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private noncomputable def emptyPhysicalSectorFactorization :
    PhysicalSectorFactorization emptyPhysicalTensor where
  sectorCount := 0
  leftDim := Fin.elim0
  rightDim := Fin.elim0
  leftDim_pos := fun k ↦ Fin.elim0 k
  rightDim_pos := fun k ↦ Fin.elim0 k
  sectorEquiv := Equiv.equivOfIsEmpty _ _
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun k ↦ Fin.elim0 k
  rightTensor := fun k ↦ Fin.elim0 k
  factorization := by
    intro beta alpha
    ext x
    exact Fin.elim0 x.1

/-- A fixed-product tensor bundled with the positive physical-sector
factorization retained by its constructor.

The factorization belongs to the exact tensor stored in `repr`; it is not
transported from a second tensor with the same closed MPOs.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
structure PositivePhysicalSectorFixedProductTensorData
    (data : TranslationInvariantBondData d) where
  /-- The exact fixed-product representative. -/
  repr : FixedProductTensorData data
  /-- The physical-sector factorization of that exact representative. -/
  factorization : PhysicalSectorFactorization repr.tensor
  /-- The bond reconstructed from the retained sectors is the input bond. -/
  physicalBond_eq : factorization.physicalBond = data.bond
  /-- Positivity of the retained neighboring operators. -/
  neighboring_pos :
    ∀ q h, (factorization.neighboringOperator q h).PosSemidef

/-- The fixed-product representative on the empty physical space.

It has one virtual state and no physical sectors.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
private noncomputable def emptyPositivePhysicalSectorFixedProductTensorData
    (data : TranslationInvariantBondData 0) :
    PositivePhysicalSectorFixedProductTensorData data := by
  let repr : FixedProductTensorData data := {
    bondDim := 1
    bondDim_pos := by omega
    tensor := emptyPhysicalTensor
    mpo_eq_product := by
      intro N hN
      ext sigma tau
      exact Fin.elim0 (sigma ⟨0, by omega⟩) }
  let F : PhysicalSectorFactorization repr.tensor :=
    emptyPhysicalSectorFactorization
  have hbond : F.physicalBond = data.bond := by
    ext sigma tau
    exact Fin.elim0 (sigma 0)
  exact {
    repr := repr
    factorization := F
    physicalBond_eq := hbond
    neighboring_pos := by
      intro q
      change Fin 0 at q
      exact Fin.elim0 q }

/-- Every positive commuting bond has a fixed-product representative whose
constructor retains a positive physical-sector factorization.

No nonempty-physical-space hypothesis is needed.  When `d = 0`, a separate
one-dimensional virtual tensor carries the zero-sector factorization.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1605; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
theorem nonempty_positivePhysicalSectorFixedProductTensorData
    (data : TranslationInvariantBondData d) :
    Nonempty (PositivePhysicalSectorFixedProductTensorData data) := by
  classical
  by_cases hd : d = 0
  · subst d
    exact ⟨emptyPositivePhysicalSectorFixedProductTensorData data⟩
  · obtain ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, hB⟩ :=
      data.exists_positive_eta_pairBond_decomposition
    let tensor := positiveEtaPhysicalTensor dl dr e U η
    let F : PhysicalSectorFactorization tensor :=
      positiveEtaPhysicalSectorFactorization dl dr e U η hU hdl hdr
    have hneighbor (q h : Fin K) : F.neighboringOperator q h = η q h :=
      positiveEtaPhysicalSectorFactorization_neighboringOperator
        dl dr e U η hU hdl hdr q h
    have hbond : F.physicalBond = data.bond :=
      positiveEtaPhysicalSectorFactorization_physicalBond_eq
        data dl dr e U η hU hdl hdr hB
    let repr : FixedProductTensorData data := {
      bondDim := Fintype.card (EtaFactorIndex dl dr)
      bondDim_pos := Fintype.card_pos_iff.mpr
        (etaFactorIndex_nonempty dl dr e hd)
      tensor := tensor
      mpo_eq_product := by
        intro N hN
        rw [F.mpo_eq_product_physicalBond hN, hbond]
        rfl }
    refine ⟨{
      repr := repr
      factorization := F
      physicalBond_eq := hbond
      neighboring_pos := ?_ }⟩
    intro q h
    rw [hneighbor q h]
    exact hη q h

/-- The selected fixed-product construction retaining its positive
physical-sector witness.

Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1605; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
noncomputable def positivePhysicalSectorFixedProductTensorData
    (data : TranslationInvariantBondData d) :
    PositivePhysicalSectorFixedProductTensorData data :=
  Classical.choice data.nonempty_positivePhysicalSectorFixedProductTensorData

end MPOTensor.TranslationInvariantBondData
