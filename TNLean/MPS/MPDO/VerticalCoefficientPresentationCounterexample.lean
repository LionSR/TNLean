/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.LengthIndependentCoefficients
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.MPDO.VerticalSectorCoordinates
import TNLean.MPS.SharedInfra.Scaling

/-!
# Horizontal equivalence does not determine vertical BNT coefficients

This file gives two one-letter MPO tensors whose positive-length periodic
matrix-product-vector families agree, but whose tensor-attached vertical BNT
algebra clauses have different structure coefficients.  The example uses
\[
  P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
  Q=\begin{pmatrix}1&3/4\\0&0\end{pmatrix}.
\]
Here \(Q=XPX^{-1}\) for the nonunitary horizontal gauge
\(X=\left(\begin{smallmatrix}1&-3/4\\0&1\end{smallmatrix}\right)\).
Both matrices are idempotent and have trace one.  Thus their positive-length
periodic families agree.  Vertically, however, the normalized representative
of \(P\) is \(P\), whereas the normalized representative of \(Q\) is
\((4/5)Q\), with the remaining factor \(5/4\) carried by the multiplicity
weight.  The resulting one-label structure coefficients are respectively
\(1\) and \((4/5)^L\).

The construction is project-derived and is not an example stated in the
source paper.  It refutes the additional cross-presentation assertion, not
CPSV16, Proposition 4.13 or Theorem 4.14.  Those source statements are made
under horizontal canonical-form hypotheses, and this file does not assert
literal horizontal CPSV canonical form for `rightMPO`.

## Main results

* `leftMPO_gaugeEquiv_rightMPO`: the two horizontal tensors are related by
  the displayed nonunitary gauge.
* `leftMPO_sameMPV₂Pos_rightMPO`: the horizontal positive-length periodic
  families agree.
* `leftMPO_isMPDO` and `rightMPO_isMPDO`: both tensors satisfy the standing
  global positivity hypothesis.
* `leftClause_coeff` and `rightClause_coeff`: the two coefficient families are
  respectively `1` and `(4 / 5) ^ L`.
* `sameMPV₂Pos_and_no_relabelled_coefficient_equality`: the horizontal
  equality does not imply the proposed relabelled coefficient equality.
* `sameMPV₂Pos_and_lengthIndependent_mismatch`: the same horizontal family
  admits these two clauses with different length-independence behavior.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  horizontal gauges at lines 187--195; Proposition 4.13, lines 943--951;
  Theorem 4.14(ii), lines 972--985; and the retained scale ratio in
  Appendix C.4, lines 1997--2008
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor.VerticalCoefficientPresentationCounterexample

private abbrev I := Fin 2

private def leftMatrix : Matrix I I ℂ :=
  !![1, 0; 0, 0]

private def rightMatrix : Matrix I I ℂ :=
  !![1, 3 / 4; 0, 0]

/-- The one-letter MPO whose only matrix is the rank-one projection
\(\operatorname{diag}(1,0)\).

This project-derived tensor belongs to the counterexample to the added
cross-presentation assertion, formulated using the algebraic form in
CPSV16, Proposition 4.13 and Theorem 4.14(ii), lines 943--985. -/
def leftMPO : MPOTensor 1 2 :=
  fun _ _ ↦ leftMatrix

/-- The one-letter MPO whose only matrix is the horizontal gauge image
\(\left(\begin{smallmatrix}1&3/4\\0&0\end{smallmatrix}\right)\).

This project-derived tensor belongs to the counterexample to the added
cross-presentation assertion, formulated using the algebraic form in
CPSV16, Proposition 4.13 and Theorem 4.14(ii), lines 943--985.  No literal
horizontal CPSV canonical-form assertion is made for this tensor. -/
def rightMPO : MPOTensor 1 2 :=
  fun _ _ ↦ rightMatrix

private def horizontalGauge : GL I ℂ where
  val := !![1, -3 / 4; 0, 1]
  inv := !![1, 3 / 4; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] private theorem horizontalGauge_val :
    (horizontalGauge : Matrix I I ℂ) = !![1, -3 / 4; 0, 1] := rfl

@[simp] private theorem horizontalGauge_inv_val :
    ((horizontalGauge⁻¹ : GL I ℂ) : Matrix I I ℂ) =
      !![1, 3 / 4; 0, 1] := rfl

/-- The two horizontal tensors are related by the displayed nonunitary gauge.

This project-derived identity uses the gauge relation of CPSV16, lines
187--195, in the proposed cross-presentation comparison.  It does not assert
literal horizontal CPSV canonical form for `rightMPO`, as assumed in CPSV16,
Proposition 4.13 and Theorem 4.14, lines 943--985. -/
theorem leftMPO_gaugeEquiv_rightMPO :
    MPSTensor.GaugeEquiv leftMPO.toMPSTensor rightMPO.toMPSTensor := by
  refine ⟨horizontalGauge, fun _ ↦ ?_⟩
  change rightMatrix =
    (horizontalGauge : Matrix I I ℂ) * leftMatrix *
      ((horizontalGauge⁻¹ : GL I ℂ) : Matrix I I ℂ)
  rw [horizontalGauge_val, horizontalGauge_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftMatrix, rightMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem leftMatrix_isIdempotent : IsIdempotentElem leftMatrix := by
  rw [IsIdempotentElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rightMatrix_isIdempotent : IsIdempotentElem rightMatrix := by
  rw [IsIdempotentElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two one-letter horizontal tensors have the same positive-length
periodic matrix-product-vector family.

This project-derived comparison is the horizontal premise in the proposed
cross-presentation assertion.  It uses the gauge mechanism of CPSV16, lines
187--195, and does not by itself identify the vertical normalizations appearing
in Proposition 4.13 and Theorem 4.14(ii), lines 943--985. -/
theorem leftMPO_sameMPV₂Pos_rightMPO :
    MPSTensor.SameMPV₂Pos leftMPO.toMPSTensor rightMPO.toMPSTensor := by
  intro L hL σ
  have hσ : σ = fun _ ↦ (0 : Fin (1 * 1)) := by
    funext n
    exact Fin.eq_zero (σ n)
  subst σ
  rw [MPSTensor.mpv_const_eq_trace_pow, MPSTensor.mpv_const_eq_trace_pow]
  change Matrix.trace (leftMatrix ^ L) = Matrix.trace (rightMatrix ^ L)
  rw [leftMatrix_isIdempotent.pow_eq (Nat.ne_of_gt hL),
    rightMatrix_isIdempotent.pow_eq (Nat.ne_of_gt hL)]
  norm_num [leftMatrix, rightMatrix, Matrix.trace, Fin.sum_univ_two]

private theorem leftMPO_mpo_eq_one (N : ℕ) (hN : 0 < N) :
    mpo leftMPO N = 1 := by
  ext σ τ
  have hστ : σ = τ := Subsingleton.elim _ _
  subst τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
  have hconfig :
      (fun n ↦ finProdFinEquiv (σ n, σ n)) =
        (fun _ ↦ (0 : Fin (1 * 1))) := by
    funext n
    exact Fin.eq_zero _
  rw [hconfig, MPSTensor.mpv_const_eq_trace_pow]
  have hOne :
      (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) σ σ = 1 := by
    simp
  rw [hOne]
  change Matrix.trace (leftMatrix ^ N) = 1
  rw [leftMatrix_isIdempotent.pow_eq (Nat.ne_of_gt hN)]
  norm_num [leftMatrix, Matrix.trace, Fin.sum_univ_two]

private theorem rightMPO_mpo_eq_one (N : ℕ) (hN : 0 < N) :
    mpo rightMPO N = 1 := by
  ext σ τ
  have hστ : σ = τ := Subsingleton.elim _ _
  subst τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
  have hconfig :
      (fun n ↦ finProdFinEquiv (σ n, σ n)) =
        (fun _ ↦ (0 : Fin (1 * 1))) := by
    funext n
    exact Fin.eq_zero _
  rw [hconfig, MPSTensor.mpv_const_eq_trace_pow]
  have hOne :
      (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) σ σ = 1 := by
    simp
  rw [hOne]
  change Matrix.trace (rightMatrix ^ N) = 1
  rw [rightMatrix_isIdempotent.pow_eq (Nat.ne_of_gt hN)]
  norm_num [rightMatrix, Matrix.trace, Fin.sum_univ_two]

/-- The projection tensor generates the identity operator at every positive
length and is therefore an MPDO.

This project-derived fact verifies the standing MPDO hypothesis of CPSV16,
Proposition 4.13 and Theorem 4.14, lines 943--985. -/
theorem leftMPO_isMPDO : IsMPDO leftMPO := by
  intro N hN
  rw [leftMPO_mpo_eq_one N hN]
  exact Matrix.PosSemidef.one

/-- The horizontally gauged tensor generates the identity operator at every
positive length and is therefore an MPDO.

This project-derived fact verifies only the standing MPDO hypothesis of
CPSV16, Proposition 4.13 and Theorem 4.14, lines 943--985; it does not assert
that `rightMPO` is in literal horizontal CPSV canonical form. -/
theorem rightMPO_isMPDO : IsMPDO rightMPO := by
  intro N hN
  rw [rightMPO_mpo_eq_one N hN]
  exact Matrix.PosSemidef.one

private abbrev oneBondDim : Fin 1 → ℕ :=
  fun _ ↦ 1

private abbrev oneMultiplicity : Fin 1 → ℕ :=
  fun _ ↦ 1

private abbrev RetainedCoordinate :=
  Fin (∑ q : Fin (∑ α : Fin 1, oneMultiplicity α),
    verticalCopyDim oneBondDim oneMultiplicity q)

private def oneRetainedCoordinateEquiv : RetainedCoordinate ≃ Fin 1 :=
  finCongr (by simp [oneBondDim, oneMultiplicity, verticalCopyDim])

private instance : Unique RetainedCoordinate where
  default := oneRetainedCoordinateEquiv.symm 0
  uniq x := by
    apply oneRetainedCoordinateEquiv.injective
    exact Subsingleton.elim (oneRetainedCoordinateEquiv x)
      (oneRetainedCoordinateEquiv (oneRetainedCoordinateEquiv.symm 0))

private def oneVerticalCoisometry : Matrix RetainedCoordinate (Fin 1) ℂ :=
  Matrix.reindex oneRetainedCoordinateEquiv.symm (Equiv.refl (Fin 1))
    (1 : Matrix (Fin 1) (Fin 1) ℂ)

private theorem oneVerticalCoisometry_apply
    (x : RetainedCoordinate) (i : Fin 1) :
    oneVerticalCoisometry x i = 1 := by
  have hxi : oneRetainedCoordinateEquiv x = i := Subsingleton.elim _ _
  simp [oneVerticalCoisometry, Matrix.reindex_apply, Matrix.one_apply, hxi]

private theorem oneVerticalCoisometry_coisometry :
    oneVerticalCoisometry * oneVerticalCoisometryᴴ =
      (1 : Matrix RetainedCoordinate RetainedCoordinate ℂ) := by
  ext x y
  have hxy : x = y := oneRetainedCoordinateEquiv.injective
    (Subsingleton.elim _ _)
  subst y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneVerticalCoisometry_apply]

private theorem oneLabel_verticalAssembledTensor_apply
    (w : ℂ) (A : MPSTensor (2 * 2) 1) (v : Fin (2 * 2))
    (x y : RetainedCoordinate) :
    verticalAssembledTensor oneBondDim oneMultiplicity
        (fun _ _ ↦ w) (fun _ ↦ A) v x y =
      w * A v 0 0 := by
  let z : RetainedCoordinate :=
    verticalSectorFinEquiv oneBondDim oneMultiplicity
      ⟨(0 : Fin 1), ((0 : Fin 1), (0 : Fin 1))⟩
  have hx : x = z := oneRetainedCoordinateEquiv.injective
    (Subsingleton.elim _ _)
  have hy : y = z := oneRetainedCoordinateEquiv.injective
    (Subsingleton.elim _ _)
  subst x
  subst y
  simpa [z, oneBondDim, oneMultiplicity] using
    (verticalAssembledTensor_apply_copy_same oneBondDim oneMultiplicity
      (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ w)
      (fun _ : Fin 1 ↦ A) (0 : Fin 1) (0 : Fin 1) v
      (0 : Fin 1) (0 : Fin 1))

private def leftVerticalRepresentative : MPSTensor (2 * 2) 1 :=
  verticalTensor leftMPO

private def rightVerticalRepresentative : MPSTensor (2 * 2) 1 :=
  (4 / 5 : ℂ) • verticalTensor rightMPO

private theorem verticalTensor_leftMPO_eq :
    verticalTensor leftMPO = (1 : ℂ) • leftVerticalRepresentative := by
  simp [leftVerticalRepresentative]

private theorem verticalTensor_rightMPO_eq :
    verticalTensor rightMPO = (5 / 4 : ℂ) • rightVerticalRepresentative := by
  rw [rightVerticalRepresentative, smul_smul]
  norm_num

private theorem leftVerticalRepresentative_transferMap :
    Kraus.transferMap leftVerticalRepresentative = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext i j
  fin_cases i
  fin_cases j
  simp only [Kraus.transferMap_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  norm_num [leftVerticalRepresentative,
    MPOTensor.verticalTensor_finProdFinEquiv, leftMPO, leftMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Fin.sum_univ_one]

private theorem rightVerticalRepresentative_transferMap :
    Kraus.transferMap rightVerticalRepresentative = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext i j
  fin_cases i
  fin_cases j
  simp only [Kraus.transferMap_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  norm_num [rightVerticalRepresentative,
    MPOTensor.verticalTensor_finProdFinEquiv, rightMPO, rightMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Fin.sum_univ_two, Fin.sum_univ_one];
    ring_nf

private theorem leftVerticalRepresentative_isNormalTensor :
    MPSTensor.IsNormalTensor leftVerticalRepresentative :=
  MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    leftVerticalRepresentative leftVerticalRepresentative_transferMap

private theorem rightVerticalRepresentative_isNormalTensor :
    MPSTensor.IsNormalTensor rightVerticalRepresentative :=
  MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    rightVerticalRepresentative rightVerticalRepresentative_transferMap

private theorem leftVerticalRepresentative_mpv_zero
    (L : ℕ) :
    MPSTensor.mpv leftVerticalRepresentative
      (fun _ : Fin L ↦ (0 : Fin (2 * 2))) = 1 := by
  rw [MPSTensor.mpv_const_eq_trace_pow]
  have hzero :
      (0 : Fin (2 * 2)) =
        finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) := rfl
  have hletter : leftVerticalRepresentative (0 : Fin (2 * 2)) = 1 := by
    rw [leftVerticalRepresentative, hzero]
    ext i j
    fin_cases i
    fin_cases j
    rw [MPOTensor.verticalTensor_finProdFinEquiv]
    norm_num [leftMPO, leftMatrix, Matrix.one_apply]
  rw [hletter]
  simp [Matrix.trace]

private theorem rightVerticalRepresentative_mpv_zero
    (L : ℕ) :
    MPSTensor.mpv rightVerticalRepresentative
      (fun _ : Fin L ↦ (0 : Fin (2 * 2))) = (4 / 5 : ℂ) ^ L := by
  rw [MPSTensor.mpv_const_eq_trace_pow]
  have hzero :
      (0 : Fin (2 * 2)) =
        finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) := rfl
  have hletter : rightVerticalRepresentative (0 : Fin (2 * 2)) =
      (4 / 5 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [rightVerticalRepresentative, hzero]
    ext i j
    fin_cases i
    fin_cases j
    simp only [Pi.smul_apply, Matrix.smul_apply]
    rw [MPOTensor.verticalTensor_finProdFinEquiv]
    norm_num [rightMPO, rightMatrix, Matrix.one_apply,
      Matrix.smul_apply]
  rw [hletter, smul_pow]
  simp [Matrix.trace]

private theorem left_isCPSVBasis :
    MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor leftMPO)
      (fun _ : Fin 1 ↦ ⟨1, leftVerticalRepresentative⟩) := by
  refine {
    blocks_normal := fun _ ↦ leftVerticalRepresentative_isNormalTensor
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro L _hL
    refine ⟨fun _ ↦ 1, ?_⟩
    intro σ
    simp [leftVerticalRepresentative]
  · refine ⟨0, ?_⟩
    intro L hL
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hzero
    have hcomponent := congrArg
      (fun v : MPSTensor.MPVSpace (2 * 2) L ↦
        v (fun _ : Fin L ↦ (0 : Fin (2 * 2)))) hzero
    have hone : (1 : ℂ) = 0 := by
      simpa only [MPSTensor.mpvState_apply,
        leftVerticalRepresentative_mpv_zero L, PiLp.zero_apply] using hcomponent
    exact one_ne_zero hone

private theorem right_isCPSVBasis :
    MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor rightMPO)
      (fun _ : Fin 1 ↦ ⟨1, rightVerticalRepresentative⟩) := by
  refine {
    blocks_normal := fun _ ↦ rightVerticalRepresentative_isNormalTensor
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro L _hL
    refine ⟨fun _ ↦ (5 / 4 : ℂ) ^ L, ?_⟩
    intro σ
    rw [verticalTensor_rightMPO_eq]
    change MPSTensor.mpv
      (fun i ↦ (5 / 4 : ℂ) • rightVerticalRepresentative i) σ = _
    rw [MPSTensor.mpv_smul]
    simp
  · refine ⟨0, ?_⟩
    intro L hL
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hzero
    have hcomponent := congrArg
      (fun v : MPSTensor.MPVSpace (2 * 2) L ↦
        v (fun _ : Fin L ↦ (0 : Fin (2 * 2)))) hzero
    have hpow : (4 / 5 : ℂ) ^ L ≠ 0 := by norm_num
    apply hpow
    simpa only [MPSTensor.mpvState_apply,
      rightVerticalRepresentative_mpv_zero L, PiLp.zero_apply] using hcomponent

private theorem oneVertical_forward
    (M : MPOTensor 1 2) (w : ℂ) (A : MPSTensor (2 * 2) 1)
    (hM : verticalTensor M = w • A) (v : Fin (2 * 2)) :
    oneVerticalCoisometry * verticalTensor M v * oneVerticalCoisometryᴴ =
      verticalAssembledTensor oneBondDim oneMultiplicity
        (fun _ _ ↦ w) (fun _ ↦ A) v := by
  rw [hM]
  ext x y
  rw [oneLabel_verticalAssembledTensor_apply]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneVerticalCoisometry_apply, Matrix.smul_apply]

private theorem oneVertical_reconstruction
    (M : MPOTensor 1 2) (w : ℂ) (A : MPSTensor (2 * 2) 1)
    (hM : verticalTensor M = w • A) (v : Fin (2 * 2)) :
    verticalTensor M v = oneVerticalCoisometryᴴ *
      verticalAssembledTensor oneBondDim oneMultiplicity
        (fun _ _ ↦ w) (fun _ ↦ A) v * oneVerticalCoisometry := by
  rw [hM]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneVerticalCoisometry_apply, oneLabel_verticalAssembledTensor_apply,
    Matrix.smul_apply]

private def oneLabelChi (s : ℂ) : DiagonalChiFamily (Fin 1) where
  dim _ _ _ := 1
  entry _ _ _ _ := s

private noncomputable def oneLabelCoeffs (s : ℂ) :
    BNTLabelCoefficientFamily (Fin 1) :=
  BNTLabelCoefficientFamily.ofChi (oneLabelChi s)

private theorem oneLabelCoeffs_coeff
    (s : ℂ) (L : ℕ) (α β γ : Fin 1) :
    (oneLabelCoeffs s).coeff L α β γ = s ^ L := by
  change (∑ _k : Fin 1, s ^ L) = s ^ L
  rw [Fin.sum_univ_one]

private theorem mpo_verticalBNTMPO_smul
    (s : ℂ) (A : MPSTensor (2 * 2) 1) (L : ℕ) :
    mpo (verticalBNTMPO (s • A)) L =
      s ^ L • mpo (verticalBNTMPO A) L := by
  ext σ τ
  simp only [← MPSTensor.mpv_toMPSTensor_pairConfig,
    verticalBNTMPO_toMPSTensor, Matrix.smul_apply, smul_eq_mul]
  exact MPSTensor.mpv_smul s A
    (fun n ↦ finProdFinEquiv (σ n, τ n))

private theorem leftVerticalRepresentative_localProduct :
    mulTensor (verticalBNTMPO leftVerticalRepresentative)
        (verticalBNTMPO leftVerticalRepresentative) =
      verticalBNTMPO leftVerticalRepresentative := by
  funext i k
  ext x y
  fin_cases i <;> fin_cases k <;> fin_cases x <;> fin_cases y <;>
    norm_num [mulTensor, verticalBNTMPO, leftVerticalRepresentative,
      verticalTensor, leftMPO, leftMatrix, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply, Fin.sum_univ_two]

private theorem rightVerticalRepresentative_localProduct :
    mulTensor (verticalBNTMPO rightVerticalRepresentative)
        (verticalBNTMPO rightVerticalRepresentative) =
      (4 / 5 : ℂ) • verticalBNTMPO rightVerticalRepresentative := by
  funext i k
  ext x y
  fin_cases i <;> fin_cases k <;> fin_cases x <;> fin_cases y <;>
    norm_num [mulTensor, verticalBNTMPO, rightVerticalRepresentative,
      verticalTensor, rightMPO, rightMatrix, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply, Matrix.smul_apply, Fin.sum_univ_two]

private theorem leftVerticalRepresentative_operatorProduct (L : ℕ) :
    mpo (verticalBNTMPO leftVerticalRepresentative) L *
        mpo (verticalBNTMPO leftVerticalRepresentative) L =
      mpo (verticalBNTMPO leftVerticalRepresentative) L := by
  rw [← mpo_mulTensor, leftVerticalRepresentative_localProduct]

private theorem rightVerticalRepresentative_operatorProduct (L : ℕ) :
    mpo (verticalBNTMPO rightVerticalRepresentative) L *
        mpo (verticalBNTMPO rightVerticalRepresentative) L =
      (4 / 5 : ℂ) ^ L •
        mpo (verticalBNTMPO rightVerticalRepresentative) L := by
  rw [← mpo_mulTensor, rightVerticalRepresentative_localProduct]
  change mpo (verticalBNTMPO ((4 / 5 : ℂ) •
    rightVerticalRepresentative)) L = _
  exact mpo_verticalBNTMPO_smul (4 / 5 : ℂ)
    rightVerticalRepresentative L

private noncomputable def leftAlgebraClause :
    BNTAlgebraClause (oneLabelCoeffs 1)
      (verticalBNTOperatorFamily (fun _ : Fin 1 ↦ leftVerticalRepresentative))
      (verticalBNTTraceScalarFamily (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ 1)) := by
  refine {
    positiveChi := PositiveBNTLabelChiTracePowerForm.ofChi
      (oneLabelChi 1) ?_
    sameLengthProduct := ?_
    idempotent := ?_
  }
  · intro α β γ q
    change (0 : ℂ) < (1 : ℂ)
    exact Complex.zero_lt_real.mpr (by norm_num : (0 : ℝ) < 1)
  · intro L _hL α β
    fin_cases α
    fin_cases β
    simpa [oneLabelCoeffs_coeff] using
      leftVerticalRepresentative_operatorProduct L
  · intro γ
    fin_cases γ
    simp [oneLabelCoeffs_coeff]

private noncomputable def rightAlgebraClause :
    BNTAlgebraClause (oneLabelCoeffs (4 / 5))
      (verticalBNTOperatorFamily (fun _ : Fin 1 ↦ rightVerticalRepresentative))
      (verticalBNTTraceScalarFamily
        (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (5 / 4 : ℂ))) := by
  refine {
    positiveChi := PositiveBNTLabelChiTracePowerForm.ofChi
      (oneLabelChi (4 / 5)) ?_
    sameLengthProduct := ?_
    idempotent := ?_
  }
  · intro α β γ q
    unfold oneLabelChi
    have h : (0 : ℂ) < ((4 / 5 : ℝ) : ℂ) :=
      Complex.zero_lt_real.mpr (by norm_num)
    convert h using 1
    all_goals norm_num
  · intro L _hL α β
    fin_cases α
    fin_cases β
    simpa [oneLabelCoeffs_coeff] using
      rightVerticalRepresentative_operatorProduct L
  · intro γ
    fin_cases γ
    norm_num [oneLabelCoeffs_coeff]

/-- The projection tensor carries the one-label vertical BNT algebra clause
with unit multiplicity weight and unit structure coefficient.

This project-derived clause has the algebraic form appearing in CPSV16,
Proposition 4.13 and Theorem 4.14(ii), lines 943--985.  It is used only to
test the added cross-presentation assertion. -/
noncomputable def leftClause : BNTAlgebraTensorClause leftMPO where
  labelCount := 1
  bondDim := oneBondDim
  multiplicity := oneMultiplicity
  weight := fun _ _ ↦ 1
  tensor := fun _ ↦ leftVerticalRepresentative
  verticalCoisometry := oneVerticalCoisometry
  multiplicity_pos := by simp [oneMultiplicity]
  weight_pos := by
    intro α q
    exact Complex.zero_lt_real.mpr (by norm_num : (0 : ℝ) < 1)
  coisometry := oneVerticalCoisometry_coisometry
  isCPSVBNT := left_isCPSVBasis
  forward := oneVertical_forward leftMPO 1 leftVerticalRepresentative
    verticalTensor_leftMPO_eq
  reconstruction := oneVertical_reconstruction leftMPO 1
    leftVerticalRepresentative verticalTensor_leftMPO_eq
  coeffs := oneLabelCoeffs 1
  algebraClause := leftAlgebraClause

/-- The horizontally gauged tensor carries the one-label vertical BNT algebra
clause with normalized representative \((4/5)Q\), multiplicity weight
\(5/4\), and structure coefficient \((4/5)^L\).

This project-derived clause has the algebraic form appearing in CPSV16,
Proposition 4.13 and Theorem 4.14(ii), lines 943--985.  It is used only to
test the added cross-presentation assertion; no literal horizontal
CPSV canonical-form statement is asserted for `rightMPO`. -/
noncomputable def rightClause : BNTAlgebraTensorClause rightMPO where
  labelCount := 1
  bondDim := oneBondDim
  multiplicity := oneMultiplicity
  weight := fun _ _ ↦ (5 / 4 : ℂ)
  tensor := fun _ ↦ rightVerticalRepresentative
  verticalCoisometry := oneVerticalCoisometry
  multiplicity_pos := by simp [oneMultiplicity]
  weight_pos := by
    intro α q
    have h : (0 : ℂ) < ((5 / 4 : ℝ) : ℂ) :=
      Complex.zero_lt_real.mpr (by norm_num)
    convert h using 1
    all_goals norm_num
  coisometry := oneVerticalCoisometry_coisometry
  isCPSVBNT := right_isCPSVBasis
  forward := oneVertical_forward rightMPO (5 / 4) rightVerticalRepresentative
    verticalTensor_rightMPO_eq
  reconstruction := oneVertical_reconstruction rightMPO (5 / 4)
    rightVerticalRepresentative verticalTensor_rightMPO_eq
  coeffs := oneLabelCoeffs (4 / 5)
  algebraClause := rightAlgebraClause

/-- The structure coefficients of the projection presentation are exactly one
at every length.

This project-derived formula evaluates the explicit clause above, whose
algebraic form is the one in CPSV16, Theorem 4.14(ii), lines 972--985. -/
@[simp]
theorem leftClause_coeff (L : ℕ) (α β γ : Fin 1) :
    leftClause.coeffs.coeff L α β γ = 1 := by
  simpa [leftClause] using oneLabelCoeffs_coeff (1 : ℂ) L α β γ

/-- The structure coefficients of the horizontally gauged presentation are
exactly \((4/5)^L\).

This project-derived formula evaluates the explicit clause above, whose
algebraic form is the one in CPSV16, Theorem 4.14(ii), lines 972--985. -/
@[simp]
theorem rightClause_coeff (L : ℕ) (α β γ : Fin 1) :
    rightClause.coeffs.coeff L α β γ = (4 / 5 : ℂ) ^ L := by
  exact oneLabelCoeffs_coeff (4 / 5 : ℂ) L α β γ

/-- The projection presentation has length-independent BNT structure
coefficients.

This project-derived conclusion concerns the explicit vertical clause above,
whose algebraic form appears in CPSV16, Theorem 4.14(ii), lines 972--985. -/
theorem leftClause_lengthIndependent :
    leftClause.coeffs.LengthIndependent := by
  change ∀ L : ℕ, 0 < L → ∀ α β γ : Fin 1,
    (oneLabelCoeffs 1).coeff L α β γ =
      (oneLabelCoeffs 1).coeff 1 α β γ
  intro L _hL α β γ
  rw [oneLabelCoeffs_coeff, oneLabelCoeffs_coeff]
  simp

/-- The horizontally gauged presentation does not have length-independent BNT
structure coefficients.

This project-derived conclusion concerns the explicit vertical clause above,
whose algebraic form appears in CPSV16, Theorem 4.14(ii), lines 972--985. -/
theorem rightClause_not_lengthIndependent :
    ¬ rightClause.coeffs.LengthIndependent := by
  intro h
  have h12 := h.coeff_eq (L := 1) (L' := 2) one_pos (by norm_num)
    (0 : Fin 1) (0 : Fin 1) (0 : Fin 1)
  norm_num at h12

/-- Horizontal positive-length MPV equality does not imply equality of the
tensor-attached vertical BNT coefficients after any relabelling.

The first conjunct is the exact horizontal premise.  The second is the
negation of the proposed relabelled coefficient equality: the unique labels
already give coefficients \(1\) and \(4/5\) at length one.  This project-derived
counterexample refutes the extra assertion, not CPSV16,
Proposition 4.13 or Theorem 4.14(ii), lines 943--985. -/
theorem sameMPV₂Pos_and_no_relabelled_coefficient_equality :
    MPSTensor.SameMPV₂Pos leftMPO.toMPSTensor rightMPO.toMPSTensor ∧
      ¬ ∃ e : Fin rightClause.labelCount ≃ Fin leftClause.labelCount,
        ∀ L : ℕ, 0 < L → ∀ α β γ,
          rightClause.coeffs.coeff L α β γ =
            leftClause.coeffs.coeff L (e α) (e β) (e γ) := by
  refine ⟨leftMPO_sameMPV₂Pos_rightMPO, ?_⟩
  change ¬ ∃ e : Fin 1 ≃ Fin 1, ∀ L : ℕ, 0 < L → ∀ α β γ,
    (oneLabelCoeffs (4 / 5)).coeff L α β γ =
      (oneLabelCoeffs 1).coeff L (e α) (e β) (e γ)
  rintro ⟨e, he⟩
  have h := he 1 one_pos (0 : Fin 1) (0 : Fin 1) (0 : Fin 1)
  rw [oneLabelCoeffs_coeff, oneLabelCoeffs_coeff] at h
  norm_num at h

/-- Horizontal positive-length MPV equality does not preserve length
independence of tensor-attached vertical BNT coefficients.

The two explicit clauses have the same horizontal periodic family, while the
left coefficients are constant and the right coefficients equal \((4/5)^L\).
This project-derived counterexample refutes the extra assertion, not CPSV16,
Proposition 4.13 or Theorem 4.14(ii), lines 943--985. -/
theorem sameMPV₂Pos_and_lengthIndependent_mismatch :
    MPSTensor.SameMPV₂Pos leftMPO.toMPSTensor rightMPO.toMPSTensor ∧
      leftClause.coeffs.LengthIndependent ∧
        ¬ rightClause.coeffs.LengthIndependent :=
  ⟨leftMPO_sameMPV₂Pos_rightMPO, leftClause_lengthIndependent,
    rightClause_not_lengthIndependent⟩

end MPOTensor.VerticalCoefficientPresentationCounterexample
