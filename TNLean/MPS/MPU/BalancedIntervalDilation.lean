/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.NormalizedBondDilation
import TNLean.MPS.MPU.ExactUniformMerging
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Exact merging of adjacent balanced MPU intervals

The tensor product of two weighted child intervals is regrouped so that the
joining bond pair is exposed. The normalized bond reset acts on this pair,
leaves all other outputs unchanged, and records the contracted parent interval
with the joining pair in a specified basis state. Its explicit unitary dilation
uses one binary flag.

If the two children and the weighted parent are isometries, the dilated child
map is an isometry whose first flag branch has constant success probability
`r⁻²`, where `r` is the joining bond dimension. The prescribed attenuation and
exact reflection rounds therefore recover the parent interval with both flags
zero and the joining pair reset. These are matrix identities, including all
phases, and the success probability and dilation are derived from the actual
interval maps.

Source: the finite-dimensional merging argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The three interval isometry
identities are the conclusions of the separate affine balancing argument; this
file assumes those identities and proves the exact merging operation.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace Matrix

variable {a b c : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- A matrix of output columns with an additional register in a basis state. -/
def basisResetOutput (V : Matrix a c ℂ) (z : b) : Matrix (a × b) c ℂ :=
  fun p j ↦ V p.1 j * (Pi.single z (1 : ℂ) : b → ℂ) p.2

omit [DecidableEq a] in
/-- Attaching a basis state preserves all inner products. -/
theorem basisResetOutput_gram (V : Matrix a c ℂ) (z : b) :
    (basisResetOutput V z)ᴴ * basisResetOutput V z = Vᴴ * V := by
  ext i j
  simp [mul_apply, basisResetOutput, Fintype.sum_prod_type, Pi.single_apply]

omit [DecidableEq a] [DecidableEq b] in
/-- Gram matrices are invariant under a reordering of output coordinates. -/
theorem reindex_rows_gram (V : Matrix a c ℂ) (e : a ≃ b) :
    (reindexLinearEquiv ℂ ℂ e (Equiv.refl c) V)ᴴ *
        reindexLinearEquiv ℂ ℂ e (Equiv.refl c) V = Vᴴ * V := by
  exact reindexLinearEquiv_mul ℂ ℂ (Equiv.refl c) e (Equiv.refl c) Vᴴ V

/-- A dilation on one tensor factor leaves the other factor unchanged. -/
theorem partialIsometryDilation_one_kronecker (A : Matrix b b ℂ) :
    partialIsometryDilation ((1 : Matrix a a ℂ) ⊗ₖ A) =
      reindexLinearEquiv ℂ ℂ (Equiv.prodSumDistrib a b b) (Equiv.prodSumDistrib a b b)
        ((1 : Matrix a a ℂ) ⊗ₖ partialIsometryDilation A) := by
  simp only [partialIsometryDilation, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  ext (⟨p, x⟩ | ⟨p, x⟩) (⟨q, y⟩ | ⟨q, y⟩)
  all_goals simp [reindexLinearEquiv, Matrix.reindex, kroneckerMap_apply, one_apply, mul_sub]
  all_goals split_ifs <;> simp_all

end Matrix

namespace MPUCircuit

open Matrix
variable {o i o' i' l n ι : Type*}
  [Fintype o] [Fintype o'] [Fintype l] [Fintype n] [Fintype ι]
  [DecidableEq o] [DecidableEq o'] [DecidableEq l] [DecidableEq n] [DecidableEq ι]

set_option maxSynthPendingDepth 8 in
local instance : DecidableEq (((o × o') × (n × l)) × (ι × ι)) := inferInstance

/-- The physical and outer bond outputs, followed by the joining bond pair. -/
def intervalChildrenRegrouping :
    ((o × (ι × l)) × (o' × (n × ι))) ≃ (((o × o') × (n × l)) × (ι × ι)) where
  toFun p := (((p.1.1, p.2.1), (p.2.2.1, p.1.2.2)), (p.2.2.2, p.1.2.1))
  invFun p := ((p.1.1.1, (p.2.2, p.1.2.2)), (p.1.1.2, (p.1.2.1, p.2.1)))
  left_inv := by rintro ⟨⟨a, x, l⟩, ⟨b, n, y⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, n, l⟩, y, x⟩; rfl

/-- The physical and virtual output columns of an unweighted interval. -/
def vectorizedIntervalColumns (X : o → i → Matrix l ι ℂ) : Matrix (o × (ι × l)) i ℂ :=
  fun p b ↦ vec (X p.1 b) p.2

/-- The two child maps with the joining pair exposed. -/
noncomputable def regroupedIntervalChildren
    (X : o → i → Matrix l ι ℂ) (Y : o' → i' → Matrix ι n ℂ) :
    Matrix (((o × o') × (n × l)) × (ι × ι)) (i × i') ℂ :=
  fun p b ↦ X p.1.1.1 b.1 p.1.2.2 p.2.2 * Y p.1.1.2 b.2 p.2.1 p.1.2.1

omit [Fintype o] [Fintype o'] [Fintype l] [Fintype n] [Fintype ι]
  [DecidableEq o] [DecidableEq o'] [DecidableEq l] [DecidableEq n] [DecidableEq ι] in
/-- Reordering the outputs of the tensor product gives the exposed child map. -/
theorem regroupedIntervalChildren_eq_reindex
    (X : o → i → Matrix l ι ℂ) (Y : o' → i' → Matrix ι n ℂ) :
    regroupedIntervalChildren X Y =
      reindexLinearEquiv ℂ ℂ intervalChildrenRegrouping (Equiv.refl (i × i'))
        (vectorizedIntervalColumns X ⊗ₖ vectorizedIntervalColumns Y) := by
  rfl

omit [DecidableEq o] [DecidableEq o'] [DecidableEq l] [DecidableEq n] [DecidableEq ι] in
/-- Tensor-product child Gram matrices survive the output regrouping. -/
theorem regroupedIntervalChildren_gram
    (X : o → i → Matrix l ι ℂ) (Y : o' → i' → Matrix ι n ℂ) :
    (regroupedIntervalChildren X Y)ᴴ * regroupedIntervalChildren X Y =
      ((vectorizedIntervalColumns X)ᴴ * vectorizedIntervalColumns X) ⊗ₖ
      ((vectorizedIntervalColumns Y)ᴴ * vectorizedIntervalColumns Y) := by
  rw [regroupedIntervalChildren_eq_reindex, reindex_rows_gram,
    conjTranspose_kronecker, ← mul_kronecker_mul]

/-- The joining bond reset leaves every other output unchanged. -/
noncomputable def liftedNormalizedBondReset (P : Matrix ι ι ℂ) (z : ι × ι) :
    Matrix (((o × o') × (n × l)) × (ι × ι)) (((o × o') × (n × l)) × (ι × ι)) ℂ :=
  (1 : Matrix ((o × o') × (n × l)) ((o × o') × (n × l)) ℂ) ⊗ₖ
    normalizedBondReset P z

/-- The exposed bond reset contracts exactly the two adjacent interval maps. -/
theorem liftedNormalizedBondReset_mul_children
    (X : o → i → Matrix l ι ℂ) (Y : o' → i' → Matrix ι n ℂ)
    (P : Matrix ι ι ℂ) (z : ι × ι) :
    liftedNormalizedBondReset P z * regroupedIntervalChildren X Y =
      basisResetOutput
        (contractedWeightedIntervals X Y (normalizedBalancedGramContraction P)) z := by
  ext ⟨p, t⟩ b
  rw [mul_apply, Fintype.sum_prod_type]
  simp only [liftedNormalizedBondReset, kronecker_apply, one_apply, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [normalizedBondReset, vecMulVec_apply, regroupedIntervalChildren,
    basisResetOutput, contractedWeightedIntervals, mul_assoc, ← Finset.mul_sum]
  rw [mul_comm (vec (X p.1.1 b.1 * normalizedBalancedGramContraction P * Y p.1.2 b.2) p.2)]
  congr 1
  simpa only [mulVec, dotProduct, kroneckerMap_apply, transpose_apply,
    transpose_transpose, mul_comm, mul_left_comm, mul_assoc] using
    congrFun (kronecker_mulVec_vec (X p.1.1 b.1)
      (normalizedBalancedGramContraction P) (Y p.1.2 b.2)ᵀ) p.2

/-- The one-flag dilation on the joining pair, in sum-flag coordinates. -/
noncomputable def balancedIntervalDilation (P : Matrix ι ι ℂ) (z : ι × ι) :
    Matrix
      ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι)))
      ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι))) ℂ :=
  partialIsometryDilation (liftedNormalizedBondReset P z)

/-- The interval dilation is the identity tensored with the actual local bond dilation. -/
theorem balancedIntervalDilation_eq_local (P : Matrix ι ι ℂ) (z : ι × ι) :
    balancedIntervalDilation (o := o) (o' := o') (l := l) (n := n) P z =
      reindexLinearEquiv ℂ ℂ
        (Equiv.prodSumDistrib ((o × o') × (n × l)) (ι × ι) (ι × ι))
        (Equiv.prodSumDistrib ((o × o') × (n × l)) (ι × ι) (ι × ι))
        ((1 : Matrix ((o × o') × (n × l)) ((o × o') × (n × l)) ℂ) ⊗ₖ
          normalizedBondDilation P z) := by
  exact partialIsometryDilation_one_kronecker _

/-- The weighted child intervals in exposed joining-pair coordinates. -/
noncomputable def balancedIntervalChildren
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ) (P : Matrix ι ι ℂ) :
    Matrix (((o × o') × (n × l)) × (ι × ι)) (i × i') ℂ :=
  regroupedIntervalChildren (fun a b ↦ L * A a b * CFC.sqrt (dualGramMetric P))
    (fun a b ↦ CFC.sqrt P * B a b * R)

/-- Prepare the child intervals and apply the explicit local joining-pair dilation. -/
noncomputable def dilatedBalancedIntervalChildren
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ) (P : Matrix ι ι ℂ) (z : ι × ι) :
    Matrix
      ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι)))
      (i × i') ℂ :=
  balancedIntervalDilation P z * fromRows (balancedIntervalChildren A B L R P) 0

variable [Nonempty ι]

/-- The lifted joining bond reset is a partial isometry. -/
theorem liftedNormalizedBondReset_mul_conjTranspose_mul
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι) :
    liftedNormalizedBondReset (o := o) (o' := o') (l := l) (n := n) P z *
      (liftedNormalizedBondReset P z)ᴴ * liftedNormalizedBondReset P z =
      liftedNormalizedBondReset P z := by
  simp only [liftedNormalizedBondReset, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [normalizedBondReset_mul_conjTranspose_mul hP z]

/-- The local interval dilation is unitary. -/
theorem balancedIntervalDilation_mem_unitaryGroup
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι) :
    balancedIntervalDilation (o := o) (o' := o') (l := l) (n := n) P z ∈
      unitaryGroup
        ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι))) ℂ := by
  exact partialIsometryDilation_mem_unitaryGroup _
    (liftedNormalizedBondReset_mul_conjTranspose_mul hP z)

variable [DecidableEq i] [DecidableEq i']

/-- Preparing isometric children and applying the dilation gives an isometry. -/
theorem dilatedBalancedIntervalChildren_gram
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι)
    (hA : (vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P)))ᴴ *
      vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P)) = 1)
    (hB : (vectorizedWeightedInterval B (CFC.sqrt P) R)ᴴ *
      vectorizedWeightedInterval B (CFC.sqrt P) R = 1) :
    (dilatedBalancedIntervalChildren A B L R P z)ᴴ *
      dilatedBalancedIntervalChildren A B L R P z = 1 := by
  rw [dilatedBalancedIntervalChildren, balancedIntervalDilation,
    partialIsometryDilation_initial_gram _
      (liftedNormalizedBondReset_mul_conjTranspose_mul hP z),
    balancedIntervalChildren, regroupedIntervalChildren_gram]
  change ((vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P)))ᴴ *
      vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P))) ⊗ₖ
    ((vectorizedWeightedInterval B (CFC.sqrt P) R)ᴴ *
      vectorizedWeightedInterval B (CFC.sqrt P) R) = 1
  rw [hA, hB, one_kronecker_one]

/-- The actual interval dilation has uniform success probability equal to inverse
squared joining-bond dimension. -/
theorem dilatedBalancedIntervalChildren_success_gram
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι)
    (hV :
      (vectorizedWeightedInterval
        (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R)ᴴ *
      vectorizedWeightedInterval
        (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R = 1) :
    (dilatedBalancedIntervalChildren A B L R P z)ᴴ *
      attenuatedSuccessProjection (1 : Matrix
        (((o × o') × (n × l)) × (ι × ι)) (((o × o') × (n × l)) × (ι × ι)) ℂ) *
      dilatedBalancedIntervalChildren A B L R P z =
      ((Fintype.card ι : ℂ)⁻¹) ^ 2 • (1 : Matrix (i × i') (i × i') ℂ) := by
  rw [dilatedBalancedIntervalChildren, balancedIntervalDilation]
  change (partialIsometryDilation (liftedNormalizedBondReset P z) *
      fromRows (balancedIntervalChildren A B L R P) 0)ᴴ *
    fromBlocks (1 : Matrix
      (((o × o') × (n × l)) × (ι × ι)) (((o × o') × (n × l)) × (ι × ι)) ℂ) 0 0 0 *
    (partialIsometryDilation (liftedNormalizedBondReset P z) *
      fromRows (balancedIntervalChildren A B L R P) 0) = _
  rw [partialIsometryDilation_success_gram, balancedIntervalChildren,
    liftedNormalizedBondReset_mul_children, basisResetOutput_gram]
  rw [contractedWeightedIntervals_balanced A B L R hP]
  simp [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV, pow_two]

omit [DecidableEq i] [DecidableEq i'] in
/-- The normalized successful branch is the actual weighted parent interval,
with joining pair reset and dilation flag zero. -/
theorem dilatedBalancedIntervalChildren_normalized_success
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι) :
    (Fintype.card ι : ℂ) •
      (attenuatedSuccessProjection (1 : Matrix
        (((o × o') × (n × l)) × (ι × ι)) (((o × o') × (n × l)) × (ι × ι)) ℂ) *
        dilatedBalancedIntervalChildren A B L R P z) =
      fromRows (basisResetOutput
        (vectorizedWeightedInterval
          (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R) z) 0 := by
  simp only [dilatedBalancedIntervalChildren, balancedIntervalDilation,
    attenuatedSuccessProjection, partialIsometryDilation_mul_fromRows,
    fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
  rw [balancedIntervalChildren, liftedNormalizedBondReset_mul_children,
    contractedWeightedIntervals_balanced A B L R hP]
  ext (p | p) b
  all_goals simp [basisResetOutput, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]

variable [Fintype i] [Fintype i']

set_option maxSynthPendingDepth 8 in
local instance : Fintype
    ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι))) :=
  inferInstance

set_option maxSynthPendingDepth 8 in
local instance : DecidableEq
    ((((o × o') × (n × l)) × (ι × ι)) ⊕ (((o × o') × (n × l)) × (ι × ι))) :=
  inferInstance

/-- The explicit joining-pair dilation followed by the prescribed exact rounds
produces the weighted parent interval, with both binary flags zero and joining
pair in the prescribed basis state. All success data are derived from the three
actual interval isometries. -/
theorem balancedInterval_merging_exact
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι)
    (hA : (vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P)))ᴴ *
      vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P)) = 1)
    (hB : (vectorizedWeightedInterval B (CFC.sqrt P) R)ᴴ *
      vectorizedWeightedInterval B (CFC.sqrt P) R = 1)
    (hV :
      (vectorizedWeightedInterval
        (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R)ᴴ *
      vectorizedWeightedInterval
        (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R = 1) :
    let W := dilatedBalancedIntervalChildren A B L R P z
    let S := attenuatedSuccessProjection (1 : Matrix
      (((o × o') × (n × l)) × (ι × ι)) (((o × o') × (n × l)) × (ι × ι)) ℂ)
    postselectionAmplificationStep
        (attenuatedIsometry W (mergingAttenuation (Fintype.card ι)))
        (attenuatedSuccessProjection S) ^ amplificationRounds (Fintype.card ι) *
        attenuatedIsometry W (mergingAttenuation (Fintype.card ι)) =
      fromRows (fromRows (basisResetOutput
        (vectorizedWeightedInterval
          (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R) z) 0) 0 := by
  dsimp only
  rw [postselectionAmplificationStep_pow_eq_first_branch _ _
    (dilatedBalancedIntervalChildren_gram A B L R hP z hA hB)
    (attenuatedSuccessProjection_isStarProjection _ (IsStarProjection.one _))
    (Fintype.card ι) Fintype.card_pos
    (dilatedBalancedIntervalChildren_success_gram A B L R hP z hV)]
  rw [dilatedBalancedIntervalChildren_normalized_success A B L R hP z]

end MPUCircuit
