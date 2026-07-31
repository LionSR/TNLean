/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorActiveRestriction

/-!
# Neighboring operators after active physical restriction

The canonical active restriction compresses the right factor of a source
sector and the left factor of a target sector.  Consequently its neighboring
operator is the congruence of the ambient neighboring operator by the
Kronecker product of those two support isometries.  Positive
semidefiniteness then follows directly from preservation under matrix
congruence.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `Appetakhetc`, `etarl`, and `StochT`, lines
  1435--1471.

**Scope restriction (active physical support compression):** the compressed
neighboring operator as an explicit congruence by the support isometries
does not appear in CPSV16 lines 1435--1471.  The source defines
$\eta_{k,h}$ at lines 1441--1445 and proves positivity at lines 1447--1450;
it defines $T_{k,h}$ at lines 1452--1455 and proves primitivity through
line 1471.  The congruence
$\tilde\eta_{k,h} = (V^R_k \otimes V^L_h)^\dagger \eta_{k,h}
(V^R_k \otimes V^L_h)$ and its positive semidefiniteness are additional
constructions.  Recorded in
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The retained neighboring index between a source sector `k` and a target
sector `h`. -/
abbrev SupportedNeighborIndex (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k h : Fin F.sectorCount) :=
  Fin (A.sector k).rightDim × Fin (A.sector h).leftDim

/-- The inclusion of the retained neighboring space into the ambient
neighboring space.  It uses the source right support and target left support.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines
1441--1445. -/
noncomputable def neighboringSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k h : Fin F.sectorCount) :
    Matrix (NeighborIndex F k h) (SupportedNeighborIndex F A k h) ℂ :=
  (A.sector k).rightInclusion ⊗ₖ (A.sector h).leftInclusion

/-- The neighboring inclusion is an isometry. -/
theorem neighboringSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k h : Fin F.sectorCount) :
    (F.neighboringSupportInclusion A k h)ᴴ *
        F.neighboringSupportInclusion A k h = 1 := by
  rw [neighboringSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    (A.sector k).rightInclusion_isometry,
    (A.sector h).leftInclusion_isometry]
  exact Matrix.one_kronecker_one

/-- The neighboring operator formed from the compressed source-right and
target-left factors.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
noncomputable def compressedNeighboringOperator
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k h : Fin F.sectorCount) :
    Matrix (SupportedNeighborIndex F A k h)
      (SupportedNeighborIndex F A k h) ℂ :=
  ∑ a : Fin D,
    F.compressedRightTensor A k a ⊗ₖ F.compressedLeftTensor A h a

/-- The ambient neighboring operator is the sum of the corresponding
right-left Kronecker products. -/
theorem neighboringOperator_eq_sum_kronecker
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    F.neighboringOperator k h =
      ∑ a : Fin D, F.rightTensor k a ⊗ₖ F.leftTensor h a := by
  ext x y
  simp [neighboringOperator, Matrix.sum_apply]

/-- The restricted neighboring operator is the explicit congruence of the
ambient neighboring operator by the source-right and target-left support
isometries.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
theorem compressedNeighboringOperator_eq_congruence
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k h : Fin F.sectorCount) :
    F.compressedNeighboringOperator A k h =
      (F.neighboringSupportInclusion A k h)ᴴ *
          F.neighboringOperator k h *
        F.neighboringSupportInclusion A k h := by
  rw [compressedNeighboringOperator, F.neighboringOperator_eq_sum_kronecker,
    Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [neighboringSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

/-- Positive semidefiniteness of an ambient neighboring operator passes to
the compressed neighboring operator by its explicit congruence.

Source: arXiv:1606.00608, Appendix C.2, equation `Appetakhetc`, lines
1435--1450. -/
theorem compressedNeighboringOperator_posSemidef
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : Fin F.sectorCount) :
    (F.compressedNeighboringOperator A k h).PosSemidef := by
  rw [F.compressedNeighboringOperator_eq_congruence]
  exact (hpos k h).conjTranspose_mul_mul_same
    (F.neighboringSupportInclusion A k h)

/-- The finite type of active sectors. -/
abbrev FactorActiveSector (F : PhysicalSectorFactorization K) :=
  {k : Fin F.sectorCount // F.IsActiveSector k}

/-- The active sectors form a finite type. -/
noncomputable instance activeSectorFintype
    (F : PhysicalSectorFactorization K) : Fintype (FactorActiveSector F) :=
  Fintype.ofFinite _

/-- The number of active sectors. -/
noncomputable def activeSectorCount (F : PhysicalSectorFactorization K) :=
  Fintype.card (FactorActiveSector F)

/-- A chosen finite enumeration of the active sectors. -/
noncomputable def activeSectorFinEquiv (F : PhysicalSectorFactorization K) :
    Fin F.activeSectorCount ≃ FactorActiveSector F :=
  (Fintype.equivFin _).symm

/-- A retained sector fiber is inhabited precisely when its ambient sector is
active. -/
theorem nonempty_supportedSectorIndex_iff_isActiveSector
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k : Fin F.sectorCount) :
    Nonempty (SupportedSectorIndex F A k) ↔ F.IsActiveSector k := by
  constructor
  · rintro ⟨x⟩
    by_contra hk
    have hzero := (A.sector k).leftDim_eq_zero_of_not_isActiveSector hk
    have hx := x.1.isLt
    omega
  · intro hk
    exact ⟨(⟨0, (A.sector k).leftDim_pos_of_isActiveSector hk⟩,
      ⟨0, (A.sector k).rightDim_pos_of_isActiveSector hk⟩)⟩

/-- Removing the empty inactive fibers identifies the active-sector
dependent sum with the retained physical index space. -/
noncomputable def activeSubtypeSigmaEquiv
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (Σ s : FactorActiveSector F, SupportedSectorIndex F A s.1) ≃
      SupportedPhysicalIndex F A :=
  Equiv.sigmaSubtypeEquivOfSubset
    (fun k ↦ SupportedSectorIndex F A k) F.IsActiveSector
    (fun k x ↦
      (F.nonempty_supportedSectorIndex_iff_isActiveSector A k).mp ⟨x⟩)

/-- The active-subtype equivalence forgets only the proof of activity. -/
@[simp] theorem activeSubtypeSigmaEquiv_apply
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (s : FactorActiveSector F) (x : SupportedSectorIndex F A s.1) :
    F.activeSubtypeSigmaEquiv A ⟨s, x⟩ = ⟨s.1, x⟩ :=
  rfl

/-- The active-sector dependent sum with active sectors enumerated by a
finite ordinal. -/
noncomputable def activeSectorSigmaEquiv
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (Σ j : Fin F.activeSectorCount,
      SupportedSectorIndex F A (F.activeSectorFinEquiv j).1) ≃
        SupportedPhysicalIndex F A :=
  (Equiv.sigmaCongrLeft (β := fun s : FactorActiveSector F ↦
    SupportedSectorIndex F A s.1) F.activeSectorFinEquiv).trans
      (F.activeSubtypeSigmaEquiv A)

/-- The enumerated active-sector equivalence preserves the fiber
coordinates. -/
@[simp] theorem activeSectorSigmaEquiv_apply
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (j : Fin F.activeSectorCount)
    (x : SupportedSectorIndex F A (F.activeSectorFinEquiv j).1) :
    F.activeSectorSigmaEquiv A ⟨j, x⟩ =
      ⟨(F.activeSectorFinEquiv j).1, x⟩ := by
  rfl

/-- The physical coordinates of the active restriction, decomposed as the
direct sum over active sectors. -/
noncomputable def activeRestrictionSectorEquiv
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Fin (F.supportedPhysicalDim A) ≃
      Σ j : Fin F.activeSectorCount,
        SupportedSectorIndex F A (F.activeSectorFinEquiv j).1 :=
  (F.supportedPhysicalFinEquiv A).trans (F.activeSectorSigmaEquiv A).symm

/-- In active-sector coordinates, the restricted physical slice is the direct
sum of the compressed left-right factors.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
theorem reindex_physicalSlice_activeRestriction_activeSectors
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (β α : Fin D) :
    Matrix.reindex (F.activeRestrictionSectorEquiv A)
        (F.activeRestrictionSectorEquiv A)
        (physicalSlice (F.activePhysicalSupportRestriction A) β α) =
      Matrix.blockDiagonal' fun j : Fin F.activeSectorCount ↦
        F.compressedLeftTensor A (F.activeSectorFinEquiv j).1 β ⊗ₖ
          F.compressedRightTensor A (F.activeSectorFinEquiv j).1 α := by
  have hfull :=
    F.reindex_physicalSlice_activePhysicalSupportRestriction A β α
  ext ⟨j, x⟩ ⟨l, y⟩
  have hEntry := congrFun (congrFun hfull
    (F.activeSectorSigmaEquiv A ⟨j, x⟩))
    (F.activeSectorSigmaEquiv A ⟨l, y⟩)
  have hjl :
      (F.activeSectorFinEquiv j).1 =
          (F.activeSectorFinEquiv l).1 ↔ j = l := by
    constructor
    · intro h
      apply F.activeSectorFinEquiv.injective
      exact Subtype.ext h
    · exact fun h ↦ h ▸ rfl
  simpa [activeRestrictionSectorEquiv, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply, hjl] using hEntry

/-- The physical-sector factorization of the active physical restriction.

Its sectors are precisely the active ambient sectors, and its left and right
factors are the corresponding support compressions.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
noncomputable abbrev activeRestrictedPhysicalSectorFactorization
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    PhysicalSectorFactorization (F.activePhysicalSupportRestriction A) where
  sectorCount := F.activeSectorCount
  leftDim := fun j ↦ (A.sector (F.activeSectorFinEquiv j).1).leftDim
  rightDim := fun j ↦ (A.sector (F.activeSectorFinEquiv j).1).rightDim
  leftDim_pos := fun j ↦
    (A.sector (F.activeSectorFinEquiv j).1).leftDim_pos_of_isActiveSector
      (F.activeSectorFinEquiv j).2
  rightDim_pos := fun j ↦
    (A.sector (F.activeSectorFinEquiv j).1).rightDim_pos_of_isActiveSector
      (F.activeSectorFinEquiv j).2
  sectorEquiv := F.activeRestrictionSectorEquiv A
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun j β ↦
    F.compressedLeftTensor A (F.activeSectorFinEquiv j).1 β
  rightTensor := fun j α ↦
    F.compressedRightTensor A (F.activeSectorFinEquiv j).1 α
  factorization := by
    intro β α
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    exact F.reindex_physicalSlice_activeRestriction_activeSectors A β α

/-- The active restricted factorization retains exactly the enumerated
ambient active sector. -/
@[simp] theorem activeRestrictedPhysicalSectorFactorization_sector
    (F : PhysicalSectorFactorization K) (_A : ActiveFactorSupportData F)
    (j : Fin F.activeSectorCount) :
    F.IsActiveSector (F.activeSectorFinEquiv j).1 :=
  (F.activeSectorFinEquiv j).2

/-- The neighboring operator of the restricted factorization is the
compressed neighboring operator of the corresponding ambient active
sectors. -/
theorem activeRestrictedPhysicalSectorFactorization_neighboringOperator
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (j l : Fin F.activeSectorCount) :
    (F.activeRestrictedPhysicalSectorFactorization A).neighboringOperator j l =
      F.compressedNeighboringOperator A
        (F.activeSectorFinEquiv j).1 (F.activeSectorFinEquiv l).1 := by
  ext x y
  simp [neighboringOperator, compressedNeighboringOperator,
    compressedLeftTensor, compressedRightTensor, Matrix.sum_apply]

/-- Every neighboring operator of the active restricted factorization is
the explicit congruence of its ambient neighboring operator.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
theorem activeRestrictedPhysicalSectorFactorization_neighboringOperator_eq_congruence
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (j l : Fin F.activeSectorCount) :
    (F.activeRestrictedPhysicalSectorFactorization A).neighboringOperator j l =
      (F.neighboringSupportInclusion A
          (F.activeSectorFinEquiv j).1 (F.activeSectorFinEquiv l).1)ᴴ *
        F.neighboringOperator
          (F.activeSectorFinEquiv j).1 (F.activeSectorFinEquiv l).1 *
        F.neighboringSupportInclusion A
          (F.activeSectorFinEquiv j).1 (F.activeSectorFinEquiv l).1 := by
  rw [F.activeRestrictedPhysicalSectorFactorization_neighboringOperator,
    F.compressedNeighboringOperator_eq_congruence]

/-- Neighboring positivity passes to every pair of sectors of the active
restricted factorization by the explicit congruence.

Source: arXiv:1606.00608, Appendix C.2, equation `Appetakhetc`, lines
1435--1450. -/
theorem activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (j l : Fin F.activeSectorCount) :
    ((F.activeRestrictedPhysicalSectorFactorization A).neighboringOperator
      j l).PosSemidef := by
  rw [F.activeRestrictedPhysicalSectorFactorization_neighboringOperator]
  exact F.compressedNeighboringOperator_posSemidef A hpos _ _

/-- The complete canonical active compression associated with a
physical-sector factorization.

The stored datum is only the simultaneous choice of factor-support
coordinates.  Its canonical projection, exact physical restriction,
active-sector factorization, sector correspondence, neighboring congruences,
and neighboring positivity are exposed below.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
structure ActivePhysicalCompressionWitness
    (F : PhysicalSectorFactorization K) where
  /-- The support coordinates chosen in every ambient sector. -/
  factorSupport : ActiveFactorSupportData F

namespace ActivePhysicalCompressionWitness

variable {F : PhysicalSectorFactorization K}

/-- The canonical active compression witness. -/
noncomputable def canonical
    (F : PhysicalSectorFactorization K) :
    ActivePhysicalCompressionWitness F where
  factorSupport := F.activeFactorSupportData

/-- The canonical physical-support restriction carried by the witness. -/
noncomputable def restrictionData
    (W : ActivePhysicalCompressionWitness F)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    PhysicalSupportRestrictionData (physicalSupportProj K) K :=
  F.activePhysicalSupportRestrictionData W.factorSupport hK hpos

/-- The restricted factorization carried by the witness. -/
noncomputable abbrev factorization
    (W : ActivePhysicalCompressionWitness F) :
    PhysicalSectorFactorization
      (F.activePhysicalSupportRestriction W.factorSupport) :=
  F.activeRestrictedPhysicalSectorFactorization W.factorSupport

/-- The restricted factorization has exactly the tensor obtained from the
canonical restriction datum. -/
noncomputable abbrev factorizationForRestrictionData
    (W : ActivePhysicalCompressionWitness F)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    PhysicalSectorFactorization
      (changePhysicalBasis (W.restrictionData hK hpos).inclusionᴴ K) :=
  W.factorization

/-- Sectors of the restricted factorization correspond bijectively to the
active ambient sectors. -/
noncomputable def sectorCorrespondence
    (W : ActivePhysicalCompressionWitness F) :
    Fin W.factorization.sectorCount ≃ FactorActiveSector F :=
  F.activeSectorFinEquiv

/-- The witness exposes the exact neighboring congruence for every pair of
its active sectors.

Source: arXiv:1606.00608, Appendix C.2, equations `Appetakhetc` and
`etarl`, lines 1435--1450. -/
theorem neighboringOperator_eq_congruence
    (W : ActivePhysicalCompressionWitness F)
    (j l : Fin W.factorization.sectorCount) :
    W.factorization.neighboringOperator j l =
      (F.neighboringSupportInclusion W.factorSupport
          (W.sectorCorrespondence j).1 (W.sectorCorrespondence l).1)ᴴ *
        F.neighboringOperator
          (W.sectorCorrespondence j).1 (W.sectorCorrespondence l).1 *
        F.neighboringSupportInclusion W.factorSupport
          (W.sectorCorrespondence j).1
          (W.sectorCorrespondence l).1 :=
  F.activeRestrictedPhysicalSectorFactorization_neighboringOperator_eq_congruence
    W.factorSupport j l

/-- The witness exposes positive semidefiniteness of every restricted
neighboring operator, obtained by the explicit congruence.

Source: arXiv:1606.00608, Appendix C.2, equation `Appetakhetc`, lines
1435--1450. -/
theorem neighboringOperator_posSemidef
    (W : ActivePhysicalCompressionWitness F)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (j l : Fin W.factorization.sectorCount) :
    (W.factorization.neighboringOperator j l).PosSemidef :=
  F.activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef
    W.factorSupport hpos j l

end ActivePhysicalCompressionWitness

end MPOTensor.PhysicalSectorFactorization
