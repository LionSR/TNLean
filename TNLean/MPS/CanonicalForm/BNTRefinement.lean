/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization
import TNLean.MPS.SharedInfra.BlockGauge
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.SharedInfra.Scaling

/-!
# BNT refinements of CPSV canonical form

A literal CPSV canonical form is partitioned into MPV phase classes.  Each copy retains its
original weight, unit phase, dimension identity, and invertible gauge relative to a chosen
normal representative.

The grouped order is the sum of the phase-class copy coordinates.  An explicit equivalence
identifies this order with the original listed blocks, and its induced flattened-coordinate
permutation gives exact letterwise direct-sum and ambient-reconstruction identities.

The phase classes follow arXiv:1606.00608, lines 265--301 and 1135--1146; the gauge witnesses
follow lines 1080--1117.  Proposition 4.13, lines 1863--1921, uses these data downstream.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- A presentation by a basis of normal tensors with sector data.

The tensor is represented at every positive length by a nonempty sector decomposition.  Every
representative is normal, the representative matrix-product vectors are eventually linearly
independent, every representative has a positive number of copies, and every displayed copy
has nonzero weight by the definition of `SectorDecomposition`.

This records the canonical-form construction in which only nonzero summands are retained.  It
does not impose the separate modulus normalization of line 246.

Source: arXiv:1606.00608, lines 217--246, 265--301, and 1135--1148. -/
structure IsBNTSectorPresentation {D' : ℕ} (A : MPSTensor d D')
    (P : SectorDecomposition d) : Prop where
  /-- At least one normal representative occurs.

  **Boundary condition (nonzero family):** This retains only the nonemptiness implied by the
  paper's convention that at least one canonical weight has modulus one; no modulus
  normalization is imposed here.

  Source: arXiv:1606.00608, lines 217--246. -/
  basisCount_pos : 0 < P.basisCount
  /-- The sector presentation gives the same positive-length matrix-product vectors.

  Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244, and lines 265--301. -/
  sameMPV₂Pos : SameMPV₂Pos A P.toTensor
  /-- Every representative is a normal tensor.

  Source: arXiv:1606.00608, lines 224--235 and 271--274. -/
  basis_normal : ∀ j, IsNormalTensor (P.basis j)
  /-- The representative matrix-product vectors are eventually linearly independent.

  Source: arXiv:1606.00608, lines 271--274 and 1135--1148. -/
  eventually_li : HasBNTSectorData P

namespace IsBNTSectorPresentation

variable {D' : ℕ} {P : SectorDecomposition d}

/-- Forgetting the sector data gives the literal CPSV basis-of-normal-tensors predicate.

Source: arXiv:1606.00608, lines 271--274. -/
theorem isCPSVBasisOfNormalTensors (h : IsBNTSectorPresentation A P) :
    IsCPSVBasisOfNormalTensors A (fun j => ⟨P.basisDim j, P.basis j⟩) := by
  refine ⟨h.basis_normal, ?_, h.eventually_li⟩
  intro N hN
  refine ⟨P.coeff N, fun σ => ?_⟩
  exact (h.sameMPV₂Pos N hN σ).trans (P.mpv_toTensor_eq_sum_coeff σ)

/-- Distinct representatives in a presentation are not gauge-phase equivalent.

Source: arXiv:1606.00608, Proposition 2.7, lines 1135--1148. -/
theorem blocks_not_gaugePhaseEquiv (h : IsBNTSectorPresentation A P) :
    BlocksNotGaugePhaseEquiv (d := d) P.basis :=
  h.isCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv

/-- Transport a presentation along equality of all positive-length matrix-product vectors.

Source: arXiv:1606.00608, lines 217--246 and 271--274. -/
theorem of_sameMPV₂Pos {D₂ : ℕ} {B : MPSTensor d D₂}
    (h : IsBNTSectorPresentation A P) (hBA : SameMPV₂Pos B A) :
    IsBNTSectorPresentation B P :=
  ⟨h.basisCount_pos, hBA.trans h.sameMPV₂Pos, h.basis_normal, h.eventually_li⟩

/-- A presentation has a nonzero matrix-product vector at some positive length.

Nonzero copy weights make each sector power sum non-eventually-zero, while eventual linear
independence prevents a nonzero sector coefficient from cancelling against the other
representatives.

Source: arXiv:1606.00608, lines 217--246 and Appendix A, lines 1182--1188. -/
theorem exists_pos_mpvState_ne_zero (h : IsBNTSectorPresentation A P) :
    ∃ N : ℕ, 0 < N ∧ mpvState A N ≠ 0 := by
  classical
  obtain ⟨N₀, hLI⟩ := h.eventually_li
  let j : Fin P.basisCount := ⟨0, h.basisCount_pos⟩
  have hCoeff : ∃ N : ℕ, N₀ < N ∧ P.coeff N j ≠ 0 := by
    by_contra hEventuallyZero
    push Not at hEventuallyZero
    apply P.coeff_not_eventually_zero j
    rw [Filter.eventually_atTop]
    exact ⟨N₀ + 1, fun N hN => hEventuallyZero N (by omega)⟩
  obtain ⟨N, hN, hCoeffN⟩ := hCoeff
  have hStateExpansion :
      mpvState A N =
        ∑ k : Fin P.basisCount, P.coeff N k • mpvState (P.basis k) N := by
    refine mpvState_eq_sum_of_decomp A P.basis (P.coeff N) ?_
    intro σ
    calc
      mpv A σ = mpv P.toTensor σ := h.sameMPV₂Pos N (by omega) σ
      _ = ∑ k : Fin P.basisCount, P.coeff N k * mpv (P.basis k) σ :=
        P.mpv_toTensor_eq_sum_coeff σ
  refine ⟨N, by omega, ?_⟩
  rw [hStateExpansion]
  intro hZero
  exact hCoeffN ((Fintype.linearIndependent_iff.mp (hLI N hN)) _ hZero j)

/-- Multiplying every tensor letter and every copy weight by the same nonzero scalar
preserves a basis-of-normal-tensors presentation.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
theorem smul_left (h : IsBNTSectorPresentation A P) (c : ℂ) (hc : c ≠ 0) :
    IsBNTSectorPresentation (c • A) (P.scaleWeights c hc) := by
  refine ⟨h.basisCount_pos, ?_, h.basis_normal, h.eventually_li⟩
  intro N hN σ
  calc
    mpv (c • A) σ = c ^ N * mpv A σ := mpv_smul c A σ
    _ = c ^ N * mpv P.toTensor σ :=
      congrArg (fun z : ℂ => c ^ N * z) (h.sameMPV₂Pos N hN σ)
    _ = mpv (P.scaleWeights c hc).toTensor σ := by
      change c ^ N * mpv P.toTensor σ =
        mpv (toTensorFromBlocks (fun k => c * P.flatWeight k) P.flatBasis) σ
      exact (mpv_toTensorFromBlocks_weight_mul_left c P.flatWeight P.flatBasis σ).symm

/-- Presentations for the same positive-length matrix-product vectors have the same normal
representatives up to a bijection and gauge phases.

This is the uniqueness sentence following CPSV16 Proposition 2.7, read with every
coefficient nonzero.

Source: arXiv:1606.00608, Proposition 2.7 and Appendix A, lines 1135--1148 and 1182. -/
theorem equiv_of_sameMPV₂Pos
    {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {P Q : SectorDecomposition d}
    (hP : IsBNTSectorPresentation A P)
    (hQ : IsBNTSectorPresentation B Q)
    (hAB : SameMPV₂Pos A B) :
    ∃ e : Fin P.basisCount ≃ Fin Q.basisCount, ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (e j),
        UnitGaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j)) (Q.basis (e j)) := by
  classical
  have hPNeZero : ∀ j, NeZero (P.basisDim j) := fun j =>
    ⟨(hP.basis_normal j).bondDim_ne_zero⟩
  have hQNeZero : ∀ j, NeZero (Q.basisDim j) := fun j =>
    ⟨(hQ.basis_normal j).bondDim_ne_zero⟩
  have hQBNTOnP :
      IsCPSVBasisOfNormalTensors P.toTensor
        (fun j => ⟨Q.basisDim j, Q.basis j⟩) := by
    refine ⟨hQ.basis_normal, ?_, hQ.eventually_li⟩
    intro N hN
    refine ⟨Q.coeff N, fun σ => ?_⟩
    calc
      mpv P.toTensor σ = mpv A σ := hP.sameMPV₂Pos N hN σ |>.symm
      _ = mpv B σ := hAB N hN σ
      _ = mpv Q.toTensor σ := hQ.sameMPV₂Pos N hN σ
      _ = ∑ j : Fin Q.basisCount, Q.coeff N j * mpv (Q.basis j) σ :=
        Q.mpv_toTensor_eq_sum_coeff σ
  have hPBNTOnQ :
      IsCPSVBasisOfNormalTensors Q.toTensor
        (fun j => ⟨P.basisDim j, P.basis j⟩) := by
    refine ⟨hP.basis_normal, ?_, hP.eventually_li⟩
    intro N hN
    refine ⟨P.coeff N, fun σ => ?_⟩
    calc
      mpv Q.toTensor σ = mpv B σ := hQ.sameMPV₂Pos N hN σ |>.symm
      _ = mpv A σ := hAB N hN σ |>.symm
      _ = mpv P.toTensor σ := hP.sameMPV₂Pos N hN σ
      _ = ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ :=
        P.mpv_toTensor_eq_sum_coeff σ
  have hForwardMatch : ∀ j : Fin P.basisCount,
      ∃ k : Fin Q.basisCount, MPVBlockPhaseEquiv (P.basis j) (Q.basis k) := by
    intro j
    exact P.exists_phase_match_of_isCPSVBasisOfNormalTensors Q.basis
      hP.basis_normal hP.blocks_not_gaugePhaseEquiv hQ.basis_normal hQBNTOnP j
  have hReverseMatch : ∀ k : Fin Q.basisCount,
      ∃ j : Fin P.basisCount, MPVBlockPhaseEquiv (Q.basis k) (P.basis j) := by
    intro k
    exact Q.exists_phase_match_of_isCPSVBasisOfNormalTensors P.basis
      hQ.basis_normal hQ.blocks_not_gaugePhaseEquiv hP.basis_normal hPBNTOnQ k
  choose f hfPhase using hForwardMatch
  choose q hqPhase using hReverseMatch
  have hfInjective : Function.Injective f := by
    intro j₁ j₂ hEq
    by_contra hNe
    have h₂ : MPVBlockPhaseEquiv (P.basis j₂) (Q.basis (f j₁)) := by
      rw [hEq]
      exact hfPhase j₂
    have hPhase := (hfPhase j₁).trans h₂.symm
    obtain ⟨hDim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (hP.basis_normal j₁) (hP.basis_normal j₂)
    exact hP.blocks_not_gaugePhaseEquiv j₁ j₂ hNe hDim hGauge
  have hqInjective : Function.Injective q := by
    intro k₁ k₂ hEq
    by_contra hNe
    have h₂ : MPVBlockPhaseEquiv (Q.basis k₂) (P.basis (q k₁)) := by
      rw [hEq]
      exact hqPhase k₂
    have hPhase := (hqPhase k₁).trans h₂.symm
    obtain ⟨hDim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (hQ.basis_normal k₁) (hQ.basis_normal k₂)
    exact hQ.blocks_not_gaugePhaseEquiv k₁ k₂ hNe hDim hGauge
  have hCard : Fintype.card (Fin P.basisCount) = Fintype.card (Fin Q.basisCount) :=
    Nat.le_antisymm (Fintype.card_le_of_injective f hfInjective)
      (Fintype.card_le_of_injective q hqInjective)
  have hfBijective : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfInjective, hCard⟩
  let e : Fin P.basisCount ≃ Fin Q.basisCount := Equiv.ofBijective f hfBijective
  refine ⟨e, fun j => ?_⟩
  obtain ⟨hdim, X, ζ, _, hrel⟩ :=
    (hfPhase j).dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
      (hP.basis_normal j) (hQ.basis_normal (e j))
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
      (hP.basis_normal j) (hQ.basis_normal (e j)) hdim hrel
  have hζunit : ζ * star ζ = 1 := by
    have hNormSq : ζ * star ζ = ↑(Complex.normSq ζ) := Complex.mul_conj ζ
    rw [Complex.normSq_eq_norm_sq, hζnorm] at hNormSq
    simpa using hNormSq
  exact ⟨hdim, X, ζ, hζunit, hrel⟩

end IsBNTSectorPresentation

namespace CPSVCanonicalFormData

/-- MPV phase classes of the canonical-form blocks. -/
noncomputable def phaseClasses (data : CPSVCanonicalFormData A) :
    MPVPhaseClassData data.blocks :=
  mpvPhaseClassData data.blocks

/-- Equivalence between phase-class copies and the original displayed blocks.

This is the explicit retained-index identification used in the copy enumeration at
arXiv:1606.00608, lines 265--301 and 1135--1146. -/
noncomputable def classCopyEquiv (data : CPSVCanonicalFormData A) :
    (Σ j : Fin data.phaseClasses.g, Fin (data.phaseClasses.copies j)) ≃ Fin data.r :=
  data.phaseClasses.enumEquiv

@[simp]
theorem classCopyEquiv_apply (data : CPSVCanonicalFormData A)
    (j : Fin data.phaseClasses.g) (q : Fin (data.phaseClasses.copies j)) :
    data.classCopyEquiv ⟨j, q⟩ = data.phaseClasses.enum j q :=
  rfl

/-- The original displayed index of the representative of a phase class. -/
noncomputable def representativeIndex (data : CPSVCanonicalFormData A)
    (j : Fin data.phaseClasses.g) : Fin data.r :=
  data.phaseClasses.repr j

/-- The phase-class copy coordinate of an original displayed index. -/
noncomputable def classCopy (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Σ j : Fin data.phaseClasses.g, Fin (data.phaseClasses.copies j) :=
  data.classCopyEquiv.symm k

theorem classCopy_classCopyEquiv (data : CPSVCanonicalFormData A)
    (j : Fin data.phaseClasses.g) (q : Fin (data.phaseClasses.copies j)) :
    data.classCopy (data.classCopyEquiv ⟨j, q⟩) = ⟨j, q⟩ :=
  data.classCopyEquiv.symm_apply_apply ⟨j, q⟩

/-- Structured BNT-refinement data for a literal CPSV canonical form.

For every displayed index, `classCopy` gives its phase class and copy label.  The record
stores the original weight, the equality of bond dimensions, a unit phase, and an actual
invertible gauge realizing that copy as a gauged phase multiple of the chosen representative.
The representative family is a CPSV basis of normal tensors.

The fields `regroupLetterwise` and `reconstructRegrouped` are exact matrix identities at every
letter, not merely positive-length MPV equalities.  The ambient rectangular map keeps the
coisometry orientation `U * Uᴴ = 1`.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146.
Proposition 4.13, lines 1863--1921, uses this refinement downstream. -/
structure BNTRefinement (data : CPSVCanonicalFormData A) where
  /-- Equality between the chosen representative's bond dimension and this copy's dimension.

  Source: arXiv:1606.00608, lines 265--301 and the normal-tensor gauge theorem at
  lines 1080--1117. -/
  copyDimEq : ∀ k : Fin data.r,
    data.dim (data.representativeIndex (data.classCopy k).1) = data.dim k
  /-- The unit phase multiplying this copy of its representative.

  Source: arXiv:1606.00608, lines 265--301 and 1080--1117. -/
  copyPhase : Fin data.r → ℂ
  /-- The phase of every copy has unit modulus.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyPhaseNorm : ∀ k : Fin data.r, ‖copyPhase k‖ = 1
  /-- The invertible gauge from the representative coordinates to this copy's coordinates.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyGauge : ∀ k : Fin data.r, GL (Fin (data.dim k)) ℂ
  /-- Exact letterwise gauge-phase relation for every copy.

  Source: the normal-tensor gauge theorem in arXiv:1606.00608, lines 1080--1117. -/
  copyRelation : ∀ (k : Fin data.r) i,
    data.blocks k i = copyPhase k •
      ((copyGauge k : Matrix _ _ ℂ) *
        (cast (congr_arg (MPSTensor d) (copyDimEq k))
          (data.blocks (data.representativeIndex (data.classCopy k).1))) i *
        (↑((copyGauge k)⁻¹) : Matrix _ _ ℂ))
  /-- The original scalar weight of each copy.

  Source: arXiv:1606.00608, lines 265--301. -/
  copyWeight : Fin data.r → ℂ
  /-- The copy weight is exactly the weight at its original displayed index.

  Source: the weighted normal-block expansion in arXiv:1606.00608, lines 265--301. -/
  copyWeightEq : ∀ k : Fin data.r, copyWeight k = data.weights k
  /-- Every chosen representative is a normal tensor.

  Source: arXiv:1606.00608, lines 265--280 and 1135--1146. -/
  representativeNormal : ∀ j,
    IsNormalTensor (data.blocks (data.representativeIndex j))
  /-- Distinct chosen representatives are not gauge-phase equivalent.

  Source: the BNT minimality argument in arXiv:1606.00608, lines 1135--1146. -/
  representativesNotEquiv :
    BlocksNotGaugePhaseEquiv (d := d)
      (fun j => data.blocks (data.representativeIndex j))
  /-- The representative family is a basis of normal tensors for the original tensor.

  Source: arXiv:1606.00608, lines 265--280 and 1135--1146. -/
  representativesBNT :
    IsCPSVBasisOfNormalTensors A
      (fun j => ⟨data.dim (data.representativeIndex j),
        data.blocks (data.representativeIndex j)⟩)
  /-- One same-dimensional representative copy at every displayed index.

  Source: arXiv:1606.00608, lines 265--301 and 1080--1117. -/
  regroupedBlocks : (k : Fin data.r) → MPSTensor d (data.dim k)
  /-- The block gauge at every displayed index.

  Source: arXiv:1606.00608, lines 1080--1117. -/
  listedGauge : (k : Fin data.r) → GL (Fin (data.dim k)) ℂ
  /-- Every entry of `regroupedBlocks` is a phase multiple of its class representative.

  Source: arXiv:1606.00608, lines 265--301 and the gauge theorem at lines 1080--1117. -/
  regroupedBlocksEq : ∀ k : Fin data.r,
    regroupedBlocks k = fun i => copyPhase k •
      (cast (congr_arg (MPSTensor d) (copyDimEq k))
        (data.blocks (data.representativeIndex (data.classCopy k).1))) i
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

/-- The grouped block order: phase class and copy for every block. -/
abbrev GroupedIndex (data : CPSVCanonicalFormData A) :=
  Σ j : Fin data.phaseClasses.g, Fin (data.phaseClasses.copies j)

/-- Number of blocks in the grouped order. -/
noncomputable def groupedCount (data : CPSVCanonicalFormData A) : ℕ :=
  Fintype.card data.GroupedIndex

/-- Enumeration of the grouped class/copy order. -/
noncomputable def groupedEnum (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount ≃ data.GroupedIndex :=
  (Fintype.equivFin data.GroupedIndex).symm

/-- Equivalence from the finite grouped enumeration to the original listed block indices. -/
noncomputable def groupedListedEquiv (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount ≃ Fin data.r :=
  data.groupedEnum.trans data.classCopyEquiv

/-- Position of a class/copy block in the finite grouped enumeration. -/
noncomputable def groupedPosition (data : CPSVCanonicalFormData A)
    (x : data.GroupedIndex) : Fin data.groupedCount :=
  data.groupedEnum.symm x

/-- Bond dimension at a grouped block position. -/
noncomputable def groupedDim (data : CPSVCanonicalFormData A) :
    Fin data.groupedCount → ℕ :=
  fun l => data.dim (data.groupedListedEquiv l)

/-- Original scalar weight at a grouped block position. -/
noncomputable def BNTRefinement.groupedWeight
    {data : CPSVCanonicalFormData A} (_ref : data.BNTRefinement) :
    Fin data.groupedCount → ℂ :=
  fun l => data.weights (data.groupedListedEquiv l)

/-- Representative copy at a grouped block position. -/
noncomputable def BNTRefinement.groupedBlocks
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement) :
    (l : Fin data.groupedCount) → MPSTensor d (data.groupedDim l) :=
  fun l => ref.regroupedBlocks (data.groupedListedEquiv l)

/-- The flattened coordinate permutation from grouped block coordinates to the original
listed direct-sum coordinates. -/
noncomputable def groupedCoordinateEquiv (data : CPSVCanonicalFormData A) :
    (Σ l : Fin data.groupedCount, Fin (data.groupedDim l)) ≃
      Fin (∑ k : Fin data.r, data.dim k) :=
  blockIndexCoordinateEquiv data.dim data.groupedListedEquiv

/-- The grouped class/copy order has exactly the original retained dimension. -/
theorem groupedTotalDim_eq (data : CPSVCanonicalFormData A) :
    (∑ l : Fin data.groupedCount, data.groupedDim l) =
      ∑ k : Fin data.r, data.dim k := by
  simpa only [Fintype.card_fin, Fintype.card_sigma] using
    Fintype.card_congr data.groupedCoordinateEquiv

/-- Exact grouped tensor in the original flattened retained-coordinate space.

The raw block diagonal is ordered by phase class and copy; `groupedCoordinateEquiv` is the
explicit permutation into the original retained coordinates.

Source: arXiv:1606.00608, lines 265--301 and 1135--1146; this coordinate form is used
in Proposition 4.13, lines 1863--1921. -/
noncomputable def BNTRefinement.groupedTensor
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement) :
    MPSTensor d (∑ k : Fin data.r, data.dim k) := fun i =>
  Matrix.reindex data.groupedCoordinateEquiv data.groupedCoordinateEquiv
    (Matrix.blockDiagonal' fun l : Fin data.groupedCount =>
      ref.groupedWeight l • ref.groupedBlocks l i)

/-- The finite position of a grouped coordinate maps to the same original listed block. -/
theorem groupedListedEquiv_groupedPosition (data : CPSVCanonicalFormData A)
    (x : data.GroupedIndex) :
    data.groupedListedEquiv (data.groupedPosition x) = data.classCopyEquiv x := by
  change data.classCopyEquiv (data.groupedEnum (data.groupedEnum.symm x)) =
    data.classCopyEquiv x
  rw [data.groupedEnum.apply_symm_apply]

/-- The grouped weight at a phase-class copy is its original displayed weight. -/
theorem BNTRefinement.groupedWeight_copy
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement)
    (jq : data.GroupedIndex) :
    ref.groupedWeight (data.groupedPosition jq) = data.weights (data.classCopyEquiv jq) := by
  simp only [BNTRefinement.groupedWeight]
  rw [data.groupedListedEquiv_groupedPosition]

/-- Exact permutation identity between the in-place regrouped direct sum and the explicit
class/copy grouped tensor. -/
theorem BNTRefinement.regroupedTensor_eq_groupedTensor
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement) (i : Fin d) :
    toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks i = ref.groupedTensor i := by
  change toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks i =
    Matrix.reindex (blockIndexCoordinateEquiv data.dim data.groupedListedEquiv)
      (blockIndexCoordinateEquiv data.dim data.groupedListedEquiv)
      (Matrix.blockDiagonal' fun l : Fin data.groupedCount =>
        data.weights (data.groupedListedEquiv l) •
          ref.regroupedBlocks (data.groupedListedEquiv l) i)
  exact toTensorFromBlocks_eq_reindex_blockDiagonal_equiv data.weights ref.regroupedBlocks
    data.groupedListedEquiv i

/-- Exact letterwise class/copy regrouping. The equation displays both the flattened
coordinate permutation and the block-diagonal copy gauges.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146. This is
the structured input used downstream in Proposition 4.13, lines 1863--1921. -/
theorem BNTRefinement.groupedRegroupLetterwise
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement) (i : Fin d) :
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
theorem BNTRefinement.reconstructGrouped
    {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement) (i : Fin d) :
    A i = ref.ambientCoisometryᴴ *
      ((globalGaugeOfBlocks ref.listedGauge : Matrix _ _ ℂ) * ref.groupedTensor i *
        (↑((globalGaugeOfBlocks ref.listedGauge)⁻¹) : Matrix _ _ ℂ)) *
      ref.ambientCoisometry := by
  rw [ref.reconstructRegrouped i, ref.regroupedTensor_eq_groupedTensor i]

/-- Every literal CPSV canonical-form decomposition has a structured BNT refinement.

The displayed indices are equivalently enumerated by phase class and copy, and every copy
carries its original weight and a unit-phase gauge witness.  The final two identities are
exact at each physical letter.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146;
Proposition 4.13, lines 1863--1921, is the downstream application. -/
theorem exists_bntRefinement (data : CPSVCanonicalFormData A) :
    Nonempty data.BNTRefinement := by
  classical
  let classes := data.phaseClasses
  let repIndex : Fin classes.g → Fin data.r := data.representativeIndex
  let classCopy : Fin data.r → (Σ j : Fin classes.g, Fin (classes.copies j)) :=
    data.classCopy
  let : ∀ k, NeZero (data.dim k) :=
    fun k => ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  have hPhase : ∀ k : Fin data.r,
      MPVBlockPhaseEquiv (data.blocks (repIndex (classCopy k).1)) (data.blocks k) := by
    intro k
    let jq := classCopy k
    have henum : classes.enum jq.1 jq.2 = k := data.classCopyEquiv.apply_symm_apply k
    have h := classes.enum_phase jq.1 jq.2
    rw [henum] at h
    exact h
  have hWitness : ∀ k : Fin data.r,
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
  have hRepresentativeNormal : ∀ j,
      IsNormalTensor (data.blocks (repIndex j)) := by
    intro j
    exact data.blocks_normal (repIndex j)
  have hRepresentativesNotEquiv :
      BlocksNotGaugePhaseEquiv (d := d) (fun j => data.blocks (repIndex j)) :=
    classes.blocks_not_equiv
  have hRepresentativesBNT :
      IsCPSVBasisOfNormalTensors A
        (fun j => ⟨data.dim (repIndex j), data.blocks (repIndex j)⟩) := by
    apply (data.isCPSVBasisOfNormalTensors_iff_covered_and_minimal
      (fun j => data.blocks (repIndex j))).2
    refine ⟨hRepresentativeNormal, ?_, ?_⟩
    · intro k
      exact ⟨(classCopy k).1, copyDimEq k, copyGauge k,
        copyPhase k, copyPhaseNorm k, copyRelation k⟩
    · intro j k hjk hdim hUnit
      obtain ⟨X, ζ, hζnorm, hrel⟩ := hUnit
      exact hRepresentativesNotEquiv j k hjk hdim
        ⟨X, ζ, Complex.ne_zero_of_norm_eq_one hζnorm, hrel⟩
  let regroupedBlocks : (k : Fin data.r) → MPSTensor d (data.dim k) := fun k i =>
    copyPhase k •
      (cast (congr_arg (MPSTensor d) (copyDimEq k))
        (data.blocks (repIndex (classCopy k).1))) i
  have hBlocksGauge : ∀ k i,
      data.blocks k i =
        (copyGauge k : Matrix _ _ ℂ) * regroupedBlocks k i *
          (↑((copyGauge k)⁻¹) : Matrix _ _ ℂ) := by
    intro k i
    simpa [regroupedBlocks, Matrix.mul_smul, Matrix.smul_mul] using copyRelation k i
  have hRegroup :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj data.weights
      regroupedBlocks data.blocks copyGauge hBlocksGauge
  refine ⟨{
    copyDimEq := copyDimEq
    copyPhase := copyPhase
    copyPhaseNorm := copyPhaseNorm
    copyGauge := copyGauge
    copyRelation := copyRelation
    copyWeight := data.weights
    copyWeightEq := fun _ => rfl
    representativeNormal := hRepresentativeNormal
    representativesNotEquiv := hRepresentativesNotEquiv
    representativesBNT := hRepresentativesBNT
    regroupedBlocks := regroupedBlocks
    listedGauge := copyGauge
    regroupedBlocksEq := fun _ => rfl
    blocksEqListedGaugeConj := hBlocksGauge
    regroupLetterwise := hRegroup
    ambientCoisometry := data.ambient_coisometry
    ambientCoisometryEq := rfl
    ambientCoisometric := data.coisometric
    reconstructRegrouped := ?_
  }⟩
  intro i
  rw [data.reconstruct i, hRegroup i]

/-- Choose the structured BNT refinement canonically supplied by `exists_bntRefinement`.

Source: arXiv:1606.00608, lines 265--301, 1080--1117, and 1135--1146;
Proposition 4.13, lines 1863--1921, is the downstream application. -/
noncomputable def bntRefinement (data : CPSVCanonicalFormData A) :
    data.BNTRefinement :=
  Classical.choice data.exists_bntRefinement

namespace BNTRefinement

variable {data : CPSVCanonicalFormData A} (ref : data.BNTRefinement)

/-- The original displayed block at a phase-class copy coordinate.

Source: arXiv:1606.00608, lines 265--301 and 1135--1148. -/
noncomputable def copy
    (j : Fin data.phaseClasses.g)
    (q : Fin (data.phaseClasses.copies j)) : Fin data.r :=
  data.classCopyEquiv ⟨j, q⟩

/-- The sector decomposition consisting exactly of the normal representatives.

The weight of a copy is its original canonical-form weight multiplied by the phase relating
that copy to its representative.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
noncomputable def representativeSectorDecomposition : SectorDecomposition d where
  basisCount := data.phaseClasses.g
  basisDim := fun j => data.dim (data.representativeIndex j)
  basis := fun j => data.blocks (data.representativeIndex j)
  sectors := {
    copies := data.phaseClasses.copies
    copies_pos := data.phaseClasses.copies_pos
    weight := fun j q =>
      ref.copyWeight (copy (data := data) j q) *
        ref.copyPhase (copy (data := data) j q)
    weight_ne_zero := fun j q => mul_ne_zero
      (by
        rw [ref.copyWeightEq]
        exact data.weights_ne_zero (copy (data := data) j q))
      (Complex.ne_zero_of_norm_eq_one
        (ref.copyPhaseNorm (copy (data := data) j q)))
  }

/-- The sector decomposition has one basis block for each phase-class representative.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
@[simp]
theorem representativeSectorDecomposition_basisCount :
    ref.representativeSectorDecomposition.basisCount = data.phaseClasses.g :=
  rfl

/-- A representative sector retains the chosen normal block's bond dimension.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
@[simp]
theorem representativeSectorDecomposition_basisDim
    (j : Fin data.phaseClasses.g) :
    ref.representativeSectorDecomposition.basisDim j =
      data.dim (data.representativeIndex j) :=
  rfl

/-- The basis tensor of a representative sector is its chosen normal block.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
@[simp]
theorem representativeSectorDecomposition_basis
    (j : Fin data.phaseClasses.g) :
    ref.representativeSectorDecomposition.basis j =
      data.blocks (data.representativeIndex j) :=
  rfl

/-- Sector multiplicities are the multiplicities of the phase classes.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
@[simp]
theorem representativeSectorDecomposition_copies
    (j : Fin data.phaseClasses.g) :
    ref.representativeSectorDecomposition.copies j =
      data.phaseClasses.copies j :=
  rfl

/-- Each copy has weight equal to its raw listed weight times its phase.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
@[simp]
theorem representativeSectorDecomposition_weight
    (j : Fin data.phaseClasses.g)
    (q : Fin (data.phaseClasses.copies j)) :
    ref.representativeSectorDecomposition.weight j q =
      ref.copyWeight (data.classCopyEquiv ⟨j, q⟩) *
        ref.copyPhase (data.classCopyEquiv ⟨j, q⟩) :=
  rfl

/-- The full grouped tensor and the representative sector tensor have equal closed-chain
coefficients at every positive length.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
theorem groupedTensor_sameMPV₂Pos_representativeSectorDecomposition :
    SameMPV₂Pos ref.groupedTensor ref.representativeSectorDecomposition.toTensor := by
  classical
  intro N hN σ
  let P := ref.representativeSectorDecomposition
  have hGrouped : ref.groupedTensor =
      toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks := by
    funext i
    exact (ref.regroupedTensor_eq_groupedTensor i).symm
  rw [hGrouped, mpv_toTensorFromBlocks_eq_sum]
  rw [P.mpv_toTensor_eq_sum_sectors]
  simp only [smul_eq_mul]
  let f : Fin data.r → ℂ := fun k =>
    data.weights k ^ N * mpv (ref.regroupedBlocks k) σ
  change (∑ k : Fin data.r, f k) =
    ∑ j : Fin data.phaseClasses.g,
      ∑ q : Fin (data.phaseClasses.copies j),
        (ref.copyWeight (copy (data := data) j q) *
          ref.copyPhase (copy (data := data) j q)) ^ N *
          mpv (data.blocks (data.representativeIndex j)) σ
  rw [← data.classCopyEquiv.sum_comp]
  rw [← Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro jq _
  rcases jq with ⟨j, q⟩
  let k := copy (data := data) j q
  change f k = (ref.copyWeight k * ref.copyPhase k) ^ N *
    mpv (data.blocks (data.representativeIndex j)) σ
  rw [ref.copyWeightEq]
  have hkclass : data.classCopy k = ⟨j, q⟩ := by
    simpa [k, copy] using data.classCopy_classCopyEquiv j q
  have hkfst : (data.classCopy k).1 = j := congrArg Sigma.fst hkclass
  have hRepresentativeMpv :
      mpv (data.blocks (data.representativeIndex (data.classCopy k).1)) σ =
        mpv (data.blocks (data.representativeIndex j)) σ := by
    rw [hkfst]
  change data.weights k ^ N * mpv (ref.regroupedBlocks k) σ = _
  rw [ref.regroupedBlocksEq k, mpv_smul]
  rw [mpv_cast_dim (ref.copyDimEq k), hRepresentativeMpv]
  ring

/-- A nonempty family of displayed blocks yields a presentation of the grouped tensor by the
chosen normal representatives.

Source: arXiv:1606.00608, lines 217--225, 265--301, and 1135--1148. -/
theorem groupedTensor_isBNTSectorPresentation (hr : 0 < data.r) :
    IsBNTSectorPresentation ref.groupedTensor
      ref.representativeSectorDecomposition := by
  refine ⟨?_, ref.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition,
    ref.representativeNormal, ref.representativesBNT.eventually_li⟩
  exact data.phaseClasses.g_pos_of_r_pos hr

/-- The original tensor and its explicitly grouped refinement have the same positive-length
matrix-product vectors.

The original CPSV coisometry first reconstructs the simultaneous gauge conjugate of the
grouped tensor; cyclicity of trace then removes that gauge.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244, and lines 1080--1117. -/
theorem source_sameMPV₂Pos_groupedTensor : SameMPV₂Pos A ref.groupedTensor := by
  let X := globalGaugeOfBlocks ref.listedGauge
  let B : MPSTensor d (∑ k : Fin data.r, data.dim k) := fun i ↦
    (X : Matrix _ _ ℂ) * ref.groupedTensor i *
      (↑(X⁻¹) : Matrix _ _ ℂ)
  have hCoisometry : SameMPV₂Pos A B :=
    sameMPV₂Pos_of_coisometry_reconstruction A B ref.ambientCoisometry
      ref.ambientCoisometric (fun i ↦ ref.reconstructGrouped i)
  have hGauge : GaugeEquiv ref.groupedTensor B :=
    ⟨X, fun _ ↦ rfl⟩
  exact hCoisometry.trans (SameMPV₂.toSameMPV₂Pos hGauge.sameMPV).symm

/-- A nonempty family of displayed blocks yields a BNT presentation of the original tensor.

Source: arXiv:1606.00608, lines 217--246, 265--301, and 1135--1148. -/
theorem isBNTSectorPresentation (hr : 0 < data.r) :
    IsBNTSectorPresentation A ref.representativeSectorDecomposition :=
  (ref.groupedTensor_isBNTSectorPresentation hr).of_sameMPV₂Pos
    ref.source_sameMPV₂Pos_groupedTensor

end BNTRefinement

end CPSVCanonicalFormData

end MPSTensor
