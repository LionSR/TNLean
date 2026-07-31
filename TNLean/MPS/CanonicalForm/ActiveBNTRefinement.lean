/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization
import TNLean.MPS.SharedInfra.BlockGauge

/-!
# Active BNT refinements of CPSV canonical form

A literal CPSV canonical form is restricted to its nonzero-weight blocks and partitioned into
MPV phase classes.  Each active copy retains its original weight, unit phase, dimension
identity, and invertible gauge relative to a chosen normal representative.  The inactive
listed blocks remain as zero-weight summands.

**Local fix (zero-weight listed blocks):** Literal Lean `CPSVCanonicalFormData` permits
syntactically listed zero-weight blocks, whereas the source canonical-form construction lists
nonzero blocks.  Retaining them as zero-weight inactive coordinates preserves the exact ambient
dimensions without treating them as physical BNT copies.  See
`docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`.

The grouped order is the sum of the phase-class copy coordinates and the inactive complement.
An explicit equivalence identifies this order with the original listed blocks, and its induced
flattened-coordinate permutation gives exact letterwise direct-sum and ambient-reconstruction
identities.

The phase classes follow arXiv:1606.00608, lines 265--301 and 1135--1146; the gauge witnesses
follow lines 1080--1117.  Proposition 4.13, lines 1863--1921, uses these data downstream.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

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
arXiv:1606.00608, lines 265--301 and 1135--1146. -/
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
`regroupLetterwise` and `reconstructRegrouped` are therefore exact matrix identities at every
letter, not merely positive-length MPV equalities.  The ambient rectangular map keeps the
coisometry orientation `U * Uᴴ = 1`.

**Local fix (zero-weight listed blocks):** Literal Lean `CPSVCanonicalFormData` permits
syntactically listed zero-weight blocks, while the source construction lists nonzero blocks.
The inactive coordinates retain zero weight to preserve exact ambient dimensions and are not
asserted to be physical BNT copies.  See
`docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146.
Proposition 4.13, lines 1863--1921, uses this refinement downstream. -/
structure ActiveBNTRefinement (data : CPSVCanonicalFormData A) where
  /-- Equality between the chosen representative's bond dimension and this copy's dimension.

  Source: arXiv:1606.00608, lines 265--301 and the normal-tensor gauge theorem at
  lines 1080--1117. -/
  copyDimEq : ∀ k : data.Active,
    data.dim (data.activeRepresentativeIndex (data.activeClassCopy k).1) = data.dim k
  /-- The unit phase multiplying this active copy of its representative.

  Source: arXiv:1606.00608, lines 265--301 and 1080--1117. -/
  copyPhase : data.Active → ℂ
  /-- The phase of every active copy has unit modulus.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyPhaseNorm : ∀ k : data.Active, ‖copyPhase k‖ = 1
  /-- The invertible gauge from the representative coordinates to this copy's coordinates.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyGauge : ∀ k : data.Active, GL (Fin (data.dim k)) ℂ
  /-- Exact letterwise gauge-phase relation for every active copy.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyRelation : ∀ (k : data.Active) i,
    data.blocks k i = copyPhase k •
      ((copyGauge k : Matrix _ _ ℂ) *
        (cast (congr_arg (MPSTensor d) (copyDimEq k))
          (data.blocks (data.activeRepresentativeIndex (data.activeClassCopy k).1))) i *
        (↑((copyGauge k)⁻¹) : Matrix _ _ ℂ))
  /-- The original scalar weight of each active copy.

  Source: arXiv:1606.00608, lines 265--301. -/
  copyWeight : data.Active → ℂ
  /-- The copy weight is exactly the weight at its original displayed index.

  Source: the weighted normal-block expansion in arXiv:1606.00608, lines 265--301. -/
  copyWeightEq : ∀ k : data.Active, copyWeight k = data.weights k
  /-- Every chosen representative is a normal tensor.

  Source: arXiv:1606.00608, lines 265--280 and 1135--1146. -/
  representativeNormal : ∀ j,
    IsNormalTensor (data.blocks (data.activeRepresentativeIndex j))
  /-- Distinct chosen representatives are not gauge-phase equivalent.

  Source: the BNT minimality argument in arXiv:1606.00608, lines 1135--1146. -/
  representativesNotEquiv :
    BlocksNotGaugePhaseEquiv (d := d)
      (fun j => data.blocks (data.activeRepresentativeIndex j))
  /-- The representative family is a basis of normal tensors for the original tensor.

  Source: arXiv:1606.00608, lines 265--280 and 1135--1146. -/
  representativesBNT :
    IsCPSVBasisOfNormalTensors A
      (fun j => ⟨data.dim (data.activeRepresentativeIndex j),
        data.blocks (data.activeRepresentativeIndex j)⟩)
  /-- One same-dimensional representative copy at every displayed index.  Inactive indices are
  left unchanged because their displayed scalar weight is zero.

  Source: active copies follow arXiv:1606.00608, lines 265--301 and 1080--1117; retaining the
  inactive complement is the formal preparation used downstream in Proposition 4.13,
  lines 1863--1921. -/
  regroupedBlocks : (k : Fin data.r) → MPSTensor d (data.dim k)
  /-- The block gauge at every displayed index.

  Source: active gauges follow arXiv:1606.00608, lines 1080--1117; identity gauges on inactive
  zero-weight coordinates are the formal preparation used downstream in Proposition 4.13,
  lines 1863--1921. -/
  listedGauge : (k : Fin data.r) → GL (Fin (data.dim k)) ℂ
  /-- Active entries of `regroupedBlocks` are phase multiples of their class representatives.

  Source: arXiv:1606.00608, lines 265--301 and the gauge theorem at lines 1080--1117. -/
  regroupedBlocksActive : ∀ k : data.Active,
    regroupedBlocks k = fun i => copyPhase k •
      (cast (congr_arg (MPSTensor d) (copyDimEq k))
        (data.blocks (data.activeRepresentativeIndex (data.activeClassCopy k).1))) i
  /-- Inactive displayed entries remain the original blocks and continue to carry zero weight.

  Source: the literal listed direct sum is arXiv:1606.00608, Section II.A, lines 214--245 and
  eq. `II_CF1`; retaining syntactic zero-weight entries is the local fix described above. -/
  regroupedBlocksInactive : ∀ k, data.weights k = 0 →
    regroupedBlocks k = data.blocks k
  /-- Every original displayed block is the conjugate of its regrouped block.

  Source: arXiv:1606.00608, lines 1080--1117, applied to the Section II.A listed blocks. -/
  blocksEqListedGaugeConj : ∀ k i,
    data.blocks k i =
      (listedGauge k : Matrix _ _ ℂ) * regroupedBlocks k i *
        (↑((listedGauge k)⁻¹) : Matrix _ _ ℂ)
  /-- Exact letterwise regrouping of the displayed direct sum.

  Source: the listed direct sum is arXiv:1606.00608, Section II.A, lines 214--245 and
  eq. `II_CF1`; this exact coordinate identity is formal preparation used downstream in
  Proposition 4.13, lines 1863--1921. -/
  regroupLetterwise : ∀ i,
    toTensorFromBlocks (d := d) data.weights data.blocks i =
      (globalGaugeOfBlocks listedGauge : Matrix _ _ ℂ) *
        toTensorFromBlocks (d := d) data.weights regroupedBlocks i *
        (↑((globalGaugeOfBlocks listedGauge)⁻¹) : Matrix _ _ ℂ)
  /-- The original ambient coisometry from literal CPSV canonical form.

  Source: arXiv:1606.00608, Section II.A, lines 214--245 and eq. `II_CF1`. -/
  ambientCoisometry : Matrix (Fin (∑ k : Fin data.r, data.dim k)) (Fin D) ℂ
  /-- The retained rectangular map is exactly the original ambient coisometry in the literal
  canonical-form witness.

  Source: arXiv:1606.00608, Section II.A, lines 214--245 and eq. `II_CF1`. -/
  ambientCoisometryEq : ambientCoisometry = data.ambient_coisometry
  /-- The ambient rectangular map is a coisometry, in the orientation `U * Uᴴ = 1`.

  Source: arXiv:1606.00608, Section II.A, lines 214--245 and eq. `II_CF1`. -/
  ambientCoisometric : ambientCoisometry * ambientCoisometryᴴ = 1
  /-- Exact ambient reconstruction through the regrouped direct sum and its block gauge.

  Source: the ambient reconstruction is arXiv:1606.00608, Section II.A, lines 214--245 and
  eq. `II_CF1`; the grouped-coordinate form is formal preparation used downstream in
  Proposition 4.13, lines 1863--1921. -/
  reconstructRegrouped : ∀ i,
    A i = ambientCoisometryᴴ *
      ((globalGaugeOfBlocks listedGauge : Matrix _ _ ℂ) *
        toTensorFromBlocks (d := d) data.weights regroupedBlocks i *
        (↑((globalGaugeOfBlocks listedGauge)⁻¹) : Matrix _ _ ℂ)) *
      ambientCoisometry

/-- Inactive displayed blocks, retained as the complement of the nonzero-weight blocks. -/
abbrev Inactive (data : CPSVCanonicalFormData A) :=
  {k : Fin data.r // ¬ data.weights k ≠ 0}

/-- The grouped block order: phase class and copy for every active block, followed by the
inactive complement. -/
abbrev GroupedIndex (data : CPSVCanonicalFormData A) :=
  (Σ j : Fin data.activePhaseClasses.g, Fin (data.activePhaseClasses.copies j)) ⊕
    data.Inactive

/-- Equivalence from the grouped class/copy-plus-inactive order to the original listed blocks. -/
noncomputable def groupedIndexEquiv (data : CPSVCanonicalFormData A) :
    data.GroupedIndex ≃ Fin data.r :=
  (Equiv.sumCongr data.activeClassCopyEquiv (Equiv.refl data.Inactive)).trans
    (Equiv.sumCompl fun k : Fin data.r => data.weights k ≠ 0)

/-- Number of blocks in the grouped order, including the inactive complement. -/
noncomputable def groupedCount (data : CPSVCanonicalFormData A) : ℕ :=
  Fintype.card data.GroupedIndex

/-- Enumeration of the grouped class/copy-plus-inactive order. -/
noncomputable def groupedEnum (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount ≃ data.GroupedIndex :=
  (Fintype.equivFin data.GroupedIndex).symm

/-- Equivalence from the finite grouped enumeration to the original listed block indices. -/
noncomputable def groupedListedEquiv (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount ≃ Fin data.r :=
  data.groupedEnum.trans data.groupedIndexEquiv

/-- Position of a class/copy or inactive block in the finite grouped enumeration. -/
noncomputable def groupedPosition (data : CPSVCanonicalFormData A)
    (x : data.GroupedIndex) : Fin data.groupedCount :=
  data.groupedEnum.symm x

/-- Bond dimension at a grouped block position. -/
noncomputable def groupedDim (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount → ℕ :=
  fun l => data.dim (data.groupedListedEquiv l)

/-- Original scalar weight at a grouped block position. -/
noncomputable def ActiveBNTRefinement.groupedWeight
    {data : CPSVCanonicalFormData A} (_ref : data.ActiveBNTRefinement) :
    Fin data.groupedCount → ℂ :=
  fun l => data.weights (data.groupedListedEquiv l)

/-- Representative copy, or unchanged inactive block, at a grouped block position. -/
noncomputable def ActiveBNTRefinement.groupedBlocks
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) :
    (l : Fin data.groupedCount) → MPSTensor d (data.groupedDim l) :=
  fun l => ref.regroupedBlocks (data.groupedListedEquiv l)

/-- The flattened coordinate permutation from grouped block coordinates to the original
listed direct-sum coordinates. -/
noncomputable def groupedCoordinateEquiv (data : CPSVCanonicalFormData A) :
    (Σ l : Fin data.groupedCount, Fin (data.groupedDim l)) ≃
      Fin (∑ k : Fin data.r, data.dim k) :=
  blockIndexCoordinateEquiv data.dim data.groupedListedEquiv

/-- The grouped class/copy-plus-inactive order has exactly the original retained dimension. -/
theorem groupedTotalDim_eq (data : CPSVCanonicalFormData A) :
    (∑ l : Fin data.groupedCount, data.groupedDim l) =
      ∑ k : Fin data.r, data.dim k := by
  simpa only [Fintype.card_fin, Fintype.card_sigma] using
    Fintype.card_congr data.groupedCoordinateEquiv

/-- Exact grouped tensor in the original flattened retained-coordinate space.

The raw block diagonal is ordered by phase class and copy, followed by the inactive complement;
`groupedCoordinateEquiv` is the explicit permutation into the original retained coordinates.

Source: arXiv:1606.00608, lines 265--301 and 1135--1146; this coordinate form is used
in Proposition 4.13, lines 1863--1921. -/
noncomputable def ActiveBNTRefinement.groupedTensor
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) :
    MPSTensor d (∑ k : Fin data.r, data.dim k) := fun i =>
  Matrix.reindex data.groupedCoordinateEquiv data.groupedCoordinateEquiv
    (Matrix.blockDiagonal' fun l : Fin data.groupedCount =>
      ref.groupedWeight l • ref.groupedBlocks l i)

/-- A grouped class/copy coordinate maps to its original active displayed block. -/
theorem groupedIndexEquiv_inl (data : CPSVCanonicalFormData A)
    (jq : Σ j : Fin data.activePhaseClasses.g,
      Fin (data.activePhaseClasses.copies j)) :
    data.groupedIndexEquiv (Sum.inl jq) = data.activeClassCopyEquiv jq := by
  rfl

/-- A grouped inactive coordinate maps to its original displayed block. -/
theorem groupedIndexEquiv_inr (data : CPSVCanonicalFormData A) (k : data.Inactive) :
    data.groupedIndexEquiv (Sum.inr k) = k := by
  rfl

/-- The finite position of a grouped coordinate maps to the same original listed block. -/
theorem groupedListedEquiv_groupedPosition (data : CPSVCanonicalFormData A)
    (x : data.GroupedIndex) :
    data.groupedListedEquiv (data.groupedPosition x) = data.groupedIndexEquiv x := by
  simp [groupedListedEquiv, groupedPosition, groupedEnum]

/-- Locate an active phase-class copy in the original listed block family. -/
theorem groupedListedEquiv_activeCopy (data : CPSVCanonicalFormData A)
    (jq : Σ j : Fin data.activePhaseClasses.g,
      Fin (data.activePhaseClasses.copies j)) :
    data.groupedListedEquiv (data.groupedPosition (Sum.inl jq)) =
      data.activeClassCopyEquiv jq := by
  rw [data.groupedListedEquiv_groupedPosition, data.groupedIndexEquiv_inl]

/-- Locate an inactive complement block in the original listed block family. -/
theorem groupedListedEquiv_inactive (data : CPSVCanonicalFormData A) (k : data.Inactive) :
    data.groupedListedEquiv (data.groupedPosition (Sum.inr k)) = k := by
  rw [data.groupedListedEquiv_groupedPosition, data.groupedIndexEquiv_inr]

/-- The grouped weight at a phase-class copy is its original displayed weight. -/
theorem ActiveBNTRefinement.groupedWeight_activeCopy
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement)
    (jq : Σ j : Fin data.activePhaseClasses.g,
      Fin (data.activePhaseClasses.copies j)) :
    ref.groupedWeight (data.groupedPosition (Sum.inl jq)) =
      data.weights (data.activeClassCopyEquiv jq) := by
  simp only [ActiveBNTRefinement.groupedWeight]
  rw [data.groupedListedEquiv_activeCopy]

/-- Inactive grouped weights vanish exactly. -/
theorem ActiveBNTRefinement.groupedWeight_inactive
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) (k : data.Inactive) :
    ref.groupedWeight (data.groupedPosition (Sum.inr k)) = 0 := by
  simp only [ActiveBNTRefinement.groupedWeight]
  rw [data.groupedListedEquiv_inactive]
  exact not_ne_iff.mp k.property

/-- Exact permutation identity between the in-place regrouped direct sum and the explicit
class/copy-plus-inactive grouped tensor. -/
theorem ActiveBNTRefinement.regroupedTensor_eq_groupedTensor
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) (i : Fin d) :
    toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks i = ref.groupedTensor i := by
  change toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks i =
    Matrix.reindex (blockIndexCoordinateEquiv data.dim data.groupedListedEquiv)
      (blockIndexCoordinateEquiv data.dim data.groupedListedEquiv)
      (Matrix.blockDiagonal' fun l : Fin data.groupedCount =>
        data.weights (data.groupedListedEquiv l) •
          ref.regroupedBlocks (data.groupedListedEquiv l) i)
  exact toTensorFromBlocks_eq_reindex_blockDiagonal_equiv data.weights ref.regroupedBlocks
    data.groupedListedEquiv i

/-- Exact letterwise class/copy-plus-inactive regrouping. The equation displays both the
flattened coordinate permutation and the block-diagonal copy gauges.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146. This is
the structured input used downstream in Proposition 4.13, lines 1863--1921. -/
theorem ActiveBNTRefinement.groupedRegroupLetterwise
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) (i : Fin d) :
    toTensorFromBlocks (d := d) data.weights data.blocks i =
      (globalGaugeOfBlocks ref.listedGauge : Matrix _ _ ℂ) *
        Matrix.reindex data.groupedCoordinateEquiv data.groupedCoordinateEquiv
          (Matrix.blockDiagonal' fun l : Fin data.groupedCount =>
            ref.groupedWeight l • ref.groupedBlocks l i) *
        (↑((globalGaugeOfBlocks ref.listedGauge)⁻¹) : Matrix _ _ ℂ) := by
  rw [ref.regroupLetterwise i, ref.regroupedTensor_eq_groupedTensor i]
  rfl

/-- Exact ambient reconstruction from the explicitly grouped tensor. The rectangular map is
the original CPSV coisometry, with orientation `U * Uᴴ = 1`.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244; the grouped coordinates follow
lines 265--301, 1080--1117, and 1135--1146 and are used in Proposition 4.13. -/
theorem ActiveBNTRefinement.reconstructGrouped
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement) (i : Fin d) :
    A i = ref.ambientCoisometryᴴ *
      ((globalGaugeOfBlocks ref.listedGauge : Matrix _ _ ℂ) * ref.groupedTensor i *
        (↑((globalGaugeOfBlocks ref.listedGauge)⁻¹) : Matrix _ _ ℂ)) *
      ref.ambientCoisometry := by
  rw [ref.reconstructRegrouped i, ref.regroupedTensor_eq_groupedTensor i]

/-- Every literal CPSV canonical-form decomposition has a structured active BNT refinement.

Zero-weight listed blocks remain as literal zero-weight summands; no false equality deleting
their coordinates is asserted.  Active indices are equivalently enumerated by phase class and
copy, and every copy carries its original weight and a unit-phase gauge witness.  The final two
identities are exact at each physical letter.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146;
Proposition 4.13, lines 1863--1921, is the downstream application. -/
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
    copyDimEq := copyDimEq
    copyPhase := copyPhase
    copyPhaseNorm := copyPhaseNorm
    copyGauge := copyGauge
    copyRelation := copyRelation
    copyWeight := copyWeight
    copyWeightEq := fun _ => rfl
    representativeNormal := hRepresentativeNormal
    representativesNotEquiv := hRepresentativesNotEquiv
    representativesBNT := hRepresentativesBNT
    regroupedBlocks := regroupedBlocks
    listedGauge := listedGauge
    regroupedBlocksActive := hRegroupedActive
    regroupedBlocksInactive := hRegroupedInactive
    blocksEqListedGaugeConj := hBlocksGauge
    regroupLetterwise := hRegroup
    ambientCoisometry := data.ambient_coisometry
    ambientCoisometryEq := rfl
    ambientCoisometric := data.coisometric
    reconstructRegrouped := ?_
  }⟩
  intro i
  rw [data.reconstruct i, hRegroup i]

/-- Choose the structured active BNT refinement canonically supplied by
`exists_activeBNTRefinement`.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146;
Proposition 4.13, lines 1863--1921, is the downstream application. -/
noncomputable def activeBNTRefinement (data : CPSVCanonicalFormData A) :
    data.ActiveBNTRefinement :=
  Classical.choice data.exists_activeBNTRefinement

end CPSVCanonicalFormData

end MPSTensor
