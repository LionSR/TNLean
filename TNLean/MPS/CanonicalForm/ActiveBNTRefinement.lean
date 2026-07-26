/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTExistence
import TNLean.MPS.SharedInfra.BlockGauge

/-!
# Structured active BNT refinements of CPSV canonical form

This module retains the data discarded by the existential BNT construction.  Starting from
literal `CPSVCanonicalFormData`, it enumerates the nonzero-weight blocks, quotients them by
MPV phase equivalence, and records the dimension, phase, and invertible gauge of every copy
relative to its chosen representative.

Zero-weight displayed blocks are not deleted.  They remain as literal zero-weight summands in
the exact direct sum.  Consequently the original ambient coisometry is retained unchanged,
with orientation `U * Uᴴ = 1`.  The active summands are replaced letterwise by gauged phase
copies of their representatives, while inactive summands are left untouched.  A block-diagonal
gauge then gives an exact letterwise regrouping and an exact ambient reconstruction.

This is the preparatory active-refinement step in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1863--1921.  It does not assert the retained-coordinate Lemma L or the
vertical canonical-form conclusion of that proposition.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- Indices of the displayed CPSV canonical-form blocks whose weights are nonzero.

Source: arXiv:1606.00608, eq. `II_CF1` and Proposition 4.13, lines 1863--1898. -/
abbrev Active (data : CPSVCanonicalFormData A) :=
  {k : Fin data.r // data.weights k ≠ 0}

/-- A finite enumeration of the nonzero-weight displayed blocks. -/
noncomputable def activeEquiv (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) ≃ data.Active :=
  (Fintype.equivFin data.Active).symm

/-- Bond dimensions of the enumerated active blocks. -/
noncomputable def activeDim (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℕ :=
  fun k => data.dim (data.activeEquiv k)

/-- Weights of the enumerated active blocks. -/
noncomputable def activeWeight (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℂ :=
  fun k => data.weights (data.activeEquiv k)

/-- Normal tensors of the enumerated active blocks. -/
noncomputable def activeBlocks (data : CPSVCanonicalFormData A) :
    (k : Fin (Fintype.card data.Active)) → MPSTensor d (data.activeDim k) :=
  fun k => data.blocks (data.activeEquiv k)

/-- MPV phase classes of the active canonical-form blocks. -/
noncomputable def activePhaseClasses (data : CPSVCanonicalFormData A) :
    MPVPhaseClassData data.activeBlocks :=
  mpvPhaseClassData data.activeBlocks

/-- Equivalence between phase-class copies and the original nonzero-weight displayed blocks.

This is the explicit retained-index identification used in the copy enumeration at
arXiv:1606.00608, lines 1894--1901. -/
noncomputable def activeClassCopyEquiv (data : CPSVCanonicalFormData A) :
    (Σ j : Fin data.activePhaseClasses.g,
      Fin (data.activePhaseClasses.copies j)) ≃ data.Active :=
  data.activePhaseClasses.enumEquiv.trans data.activeEquiv

@[simp]
theorem activeClassCopyEquiv_apply (data : CPSVCanonicalFormData A)
    (j : Fin data.activePhaseClasses.g)
    (q : Fin (data.activePhaseClasses.copies j)) :
    data.activeClassCopyEquiv ⟨j, q⟩ =
      data.activeEquiv (data.activePhaseClasses.enum j q) :=
  rfl

/-- The original displayed index of the representative of an active phase class. -/
noncomputable def activeRepresentativeIndex (data : CPSVCanonicalFormData A)
    (j : Fin data.activePhaseClasses.g) : data.Active :=
  data.activeEquiv (data.activePhaseClasses.repr j)

/-- The phase-class copy coordinate of an original active displayed index. -/
noncomputable def activeClassCopy (data : CPSVCanonicalFormData A) (k : data.Active) :
    Σ j : Fin data.activePhaseClasses.g, Fin (data.activePhaseClasses.copies j) :=
  data.activeClassCopyEquiv.symm k

@[simp]
theorem activeClassCopy_activeClassCopyEquiv (data : CPSVCanonicalFormData A)
    (j : Fin data.activePhaseClasses.g)
    (q : Fin (data.activePhaseClasses.copies j)) :
    data.activeClassCopy (data.activeClassCopyEquiv ⟨j, q⟩) = ⟨j, q⟩ :=
  data.activeClassCopyEquiv.symm_apply_apply ⟨j, q⟩

/-- Structured active BNT-refinement data for a literal CPSV canonical form.

For every active displayed index, `activeClassCopy` gives its phase class and copy label.  The
record stores the original weight, the equality of bond dimensions, a unit phase, and an actual
invertible gauge realizing that copy as a gauged phase multiple of the chosen representative.
The representative family is a CPSV basis of normal tensors.

The displayed zero-weight coordinates are retained as literal zero summands.  The fields
`regroup_letterwise` and `reconstruct_regrouped` are therefore exact matrix identities at every
letter, not merely positive-length MPV equalities.  The ambient rectangular map keeps the
coisometry orientation `U * Uᴴ = 1`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921, especially the copy enumeration
and gauges at lines 1894--1905. -/
structure ActiveBNTRefinement (data : CPSVCanonicalFormData A) where
  /-- Equality between the chosen representative's bond dimension and this copy's dimension. -/
  copy_dim_eq : ∀ k : data.Active,
    data.dim (data.activeRepresentativeIndex (data.activeClassCopy k).1) = data.dim k
  /-- The unit phase multiplying this active copy of its representative. -/
  copy_phase : data.Active → ℂ
  /-- The phase of every active copy has unit modulus. -/
  copy_phase_norm : ∀ k : data.Active, ‖copy_phase k‖ = 1
  /-- The invertible gauge from the representative coordinates to this copy's coordinates. -/
  copy_gauge : ∀ k : data.Active, GL (Fin (data.dim k)) ℂ
  /-- Exact letterwise gauge-phase relation for every active copy. -/
  copy_relation : ∀ (k : data.Active) i,
    data.blocks k i = copy_phase k •
      ((copy_gauge k : Matrix _ _ ℂ) *
        (cast (congr_arg (MPSTensor d) (copy_dim_eq k))
          (data.blocks (data.activeRepresentativeIndex (data.activeClassCopy k).1))) i *
        (↑((copy_gauge k)⁻¹) : Matrix _ _ ℂ))
  /-- The original scalar weight of each active copy. -/
  copy_weight : data.Active → ℂ
  /-- The copy weight is exactly the weight at its original displayed index. -/
  copy_weight_eq : ∀ k : data.Active, copy_weight k = data.weights k
  /-- Every chosen representative is a normal tensor. -/
  representative_normal : ∀ j,
    IsNormalTensor (data.blocks (data.activeRepresentativeIndex j))
  /-- Distinct chosen representatives are not gauge-phase equivalent. -/
  representatives_not_equiv :
    BlocksNotGaugePhaseEquiv (d := d)
      (fun j => data.blocks (data.activeRepresentativeIndex j))
  /-- The representative family is a basis of normal tensors for the original tensor. -/
  representatives_bnt :
    IsCPSVBasisOfNormalTensors A
      (fun j => ⟨data.dim (data.activeRepresentativeIndex j),
        data.blocks (data.activeRepresentativeIndex j)⟩)
  /-- One same-dimensional representative copy at every displayed index.  Inactive indices are
  left unchanged because their displayed scalar weight is zero. -/
  regrouped_blocks : (k : Fin data.r) → MPSTensor d (data.dim k)
  /-- The block gauge at every displayed index. -/
  listed_gauge : (k : Fin data.r) → GL (Fin (data.dim k)) ℂ
  /-- Active entries of `regrouped_blocks` are phase multiples of their class representatives. -/
  regrouped_blocks_active : ∀ k : data.Active,
    regrouped_blocks k = fun i => copy_phase k •
      (cast (congr_arg (MPSTensor d) (copy_dim_eq k))
        (data.blocks (data.activeRepresentativeIndex (data.activeClassCopy k).1))) i
  /-- Inactive displayed entries remain the original blocks and continue to carry zero weight. -/
  regrouped_blocks_inactive : ∀ k, data.weights k = 0 →
    regrouped_blocks k = data.blocks k
  /-- Every original displayed block is the conjugate of its regrouped block. -/
  blocks_eq_listed_gauge_conj : ∀ k i,
    data.blocks k i =
      (listed_gauge k : Matrix _ _ ℂ) * regrouped_blocks k i *
        (↑((listed_gauge k)⁻¹) : Matrix _ _ ℂ)
  /-- Exact letterwise regrouping of the displayed direct sum. -/
  regroup_letterwise : ∀ i,
    toTensorFromBlocks (d := d) data.weights data.blocks i =
      (globalGaugeOfBlocks listed_gauge : Matrix _ _ ℂ) *
        toTensorFromBlocks (d := d) data.weights regrouped_blocks i *
        (↑((globalGaugeOfBlocks listed_gauge)⁻¹) : Matrix _ _ ℂ)
  /-- The original ambient coisometry from literal CPSV canonical form. -/
  ambient_coisometry : Matrix (Fin (∑ k : Fin data.r, data.dim k)) (Fin D) ℂ
  /-- The retained rectangular map is exactly the original ambient coisometry in the literal
  canonical-form witness. -/
  ambient_coisometry_eq : ambient_coisometry = data.ambient_coisometry
  /-- The ambient rectangular map is a coisometry, in the orientation `U * Uᴴ = 1`. -/
  ambient_coisometric : ambient_coisometry * ambient_coisometryᴴ = 1
  /-- Exact ambient reconstruction through the regrouped direct sum and its block gauge. -/
  reconstruct_regrouped : ∀ i,
    A i = ambient_coisometryᴴ *
      ((globalGaugeOfBlocks listed_gauge : Matrix _ _ ℂ) *
        toTensorFromBlocks (d := d) data.weights regrouped_blocks i *
        (↑((globalGaugeOfBlocks listed_gauge)⁻¹) : Matrix _ _ ℂ)) *
      ambient_coisometry

/-- Every literal CPSV canonical-form decomposition has a structured active BNT refinement.

Zero-weight listed blocks remain as literal zero-weight summands; no false equality deleting
their coordinates is asserted.  Active indices are equivalently enumerated by phase class and
copy, and every copy carries its original weight and a unit-phase gauge witness.  The final two
identities are exact at each physical letter.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem exists_activeBNTRefinement (data : CPSVCanonicalFormData A) :
    Nonempty data.ActiveBNTRefinement := by
  classical
  let classes := data.activePhaseClasses
  let repIndex : Fin classes.g → data.Active := data.activeRepresentativeIndex
  let classCopy : data.Active → (Σ j : Fin classes.g, Fin (classes.copies j)) :=
    data.activeClassCopy
  letI : ∀ k, NeZero (data.dim k) :=
    fun k => ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  have hPhase : ∀ k : data.Active,
      MPVBlockPhaseEquiv (data.blocks (repIndex (classCopy k).1)) (data.blocks k) := by
    intro k
    let jq := classCopy k
    have henum : data.activeEquiv (classes.enum jq.1 jq.2) = k := by
      exact data.activeClassCopyEquiv.apply_symm_apply k
    have h := classes.enum_phase jq.1 jq.2
    change MPVBlockPhaseEquiv
      (data.blocks (data.activeEquiv (classes.repr jq.1)))
      (data.blocks (data.activeEquiv (classes.enum jq.1 jq.2))) at h
    rw [henum] at h
    exact h
  have hWitness : ∀ k : data.Active,
      ∃ hdim : data.dim (repIndex (classCopy k).1) = data.dim k,
      ∃ X : GL (Fin (data.dim k)) ℂ,
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        ∀ i, data.blocks k i = ζ •
          ((X : Matrix _ _ ℂ) *
            (cast (congr_arg (MPSTensor d) hdim)
              (data.blocks (repIndex (classCopy k).1))) i *
            (↑(X⁻¹) : Matrix _ _ ℂ)) := by
    intro k
    obtain ⟨hdim, X, ζ, _hζ, hrel⟩ :=
      (hPhase k).dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (data.blocks_normal (repIndex (classCopy k).1)) (data.blocks_normal k)
    refine ⟨hdim, X, ζ, ?_, hrel⟩
    exact norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
      (data.blocks_normal (repIndex (classCopy k).1)) (data.blocks_normal k) hdim hrel
  choose copyDimEq copyGauge copyPhase copyPhaseNorm copyRelation using hWitness
  let copyWeight : data.Active → ℂ := fun k => data.weights k
  have hRepresentativeNormal : ∀ j,
      IsNormalTensor (data.blocks (repIndex j)) := by
    intro j
    exact data.blocks_normal (repIndex j)
  have hRepresentativesNotEquiv :
      BlocksNotGaugePhaseEquiv (d := d) (fun j => data.blocks (repIndex j)) := by
    simpa [classes, repIndex, activeRepresentativeIndex, activePhaseClasses,
      activeBlocks, activeDim] using classes.blocks_not_equiv
  have hRepresentativesBNT :
      IsCPSVBasisOfNormalTensors A
        (fun j => ⟨data.dim (repIndex j), data.blocks (repIndex j)⟩) := by
    apply (data.isCPSVBasisOfNormalTensors_iff_covered_and_minimal
      (fun j => data.blocks (repIndex j))).2
    refine ⟨hRepresentativeNormal, ?_, ?_⟩
    · intro k hk
      let ka : data.Active := ⟨k, hk⟩
      refine ⟨(classCopy ka).1, copyDimEq ka, copyGauge ka,
        copyPhase ka, copyPhaseNorm ka, copyRelation ka⟩
    · intro j k hjk hdim hUnit
      obtain ⟨X, ζ, hζnorm, hrel⟩ := hUnit
      exact hRepresentativesNotEquiv j k hjk hdim
        ⟨X, ζ, Complex.ne_zero_of_norm_eq_one hζnorm, hrel⟩
  let regroupedBlocks : (k : Fin data.r) → MPSTensor d (data.dim k) := fun k =>
    if hk : data.weights k ≠ 0 then
      let ka : data.Active := ⟨k, hk⟩
      fun i => copyPhase ka •
        (cast (congr_arg (MPSTensor d) (copyDimEq ka))
          (data.blocks (repIndex (classCopy ka).1))) i
    else data.blocks k
  let listedGauge : (k : Fin data.r) → GL (Fin (data.dim k)) ℂ := fun k =>
    if hk : data.weights k ≠ 0 then
      copyGauge ⟨k, hk⟩
    else 1
  have hRegroupedActive : ∀ k : data.Active,
      regroupedBlocks k = fun i => copyPhase k •
        (cast (congr_arg (MPSTensor d) (copyDimEq k))
          (data.blocks (repIndex (classCopy k).1))) i := by
    intro k
    simp only [regroupedBlocks, dif_pos k.property]
  have hRegroupedInactive : ∀ k, data.weights k = 0 →
      regroupedBlocks k = data.blocks k := by
    intro k hk
    simp [regroupedBlocks, hk]
  have hBlocksGauge : ∀ k i,
      data.blocks k i =
        (listedGauge k : Matrix _ _ ℂ) * regroupedBlocks k i *
          (↑((listedGauge k)⁻¹) : Matrix _ _ ℂ) := by
    intro k i
    by_cases hk : data.weights k ≠ 0
    · let ka : data.Active := ⟨k, hk⟩
      have hrel := copyRelation ka i
      simp only [listedGauge, regroupedBlocks, dif_pos hk]
      simpa [Matrix.mul_smul, Matrix.smul_mul] using hrel
    · simp only [listedGauge, regroupedBlocks, dif_neg hk]
      simp
  have hRegroup :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj data.weights
      regroupedBlocks data.blocks listedGauge hBlocksGauge
  refine ⟨{
    copy_dim_eq := copyDimEq
    copy_phase := copyPhase
    copy_phase_norm := copyPhaseNorm
    copy_gauge := copyGauge
    copy_relation := copyRelation
    copy_weight := copyWeight
    copy_weight_eq := fun _ => rfl
    representative_normal := hRepresentativeNormal
    representatives_not_equiv := hRepresentativesNotEquiv
    representatives_bnt := hRepresentativesBNT
    regrouped_blocks := regroupedBlocks
    listed_gauge := listedGauge
    regrouped_blocks_active := hRegroupedActive
    regrouped_blocks_inactive := hRegroupedInactive
    blocks_eq_listed_gauge_conj := hBlocksGauge
    regroup_letterwise := hRegroup
    ambient_coisometry := data.ambient_coisometry
    ambient_coisometry_eq := rfl
    ambient_coisometric := data.coisometric
    reconstruct_regrouped := ?_
  }⟩
  intro i
  rw [data.reconstruct i, hRegroup i]

/-- Choose the structured active BNT refinement canonically supplied by
`exists_activeBNTRefinement`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
noncomputable def activeBNTRefinement (data : CPSVCanonicalFormData A) :
    data.ActiveBNTRefinement :=
  Classical.choice data.exists_activeBNTRefinement

end CPSVCanonicalFormData

end MPSTensor
