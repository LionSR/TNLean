/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.SimpleTensor
import TNLean.MPS.MPDO.StackedLayers

/-!
# Unequal repeated-copy weights obstruct the printed fixed-point implication

This file gives the one-sector, two-copy example with raw canonical weights
$1$ and $1/2$. It satisfies the printed standing hypotheses and condition (iv)
of arXiv:1606.00608, Theorem 4.9, but its two-site block does not satisfy
Definition 4.1. Thus it refutes the literal implication (iv)$\Rightarrow$(v),
not the distinct coefficient-absorption normality inference in the Case-II
proof of (ii)$\Rightarrow$(iv).

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Theorem 4.9,
  lines 851--893, and Appendix C.2, lines 1381--1403.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

namespace MPOTensor.CaseIIAbsorptionCounterexample

/-! ### A counterexample to the literal implication (iv) implies (v) -/

/-- The sole BNT representative underlying `repeatedCopyTensor`.

This is the scalar normal tensor used in condition (iv) of arXiv:1606.00608,
Theorem 4.9 (lines 863--889). -/
noncomputable def scalarBNT : MPOTensor 1 1 := fun _ _ ↦ 1

/-- The one-sector, two-copy BNT presentation of `repeatedCopyTensor`.

The copy weights are exactly $\mu_{0,0}=1$ and $\mu_{0,1}=1/2$, allowed by
the global normalization of arXiv:1606.00608, line 246. -/
@[reducible] noncomputable def repeatedCopyDecomposition :
    MPSTensor.SectorDecomposition 1 where
  basisCount := 1
  basisDim := fun _ ↦ 1
  basis := fun _ ↦ scalarBNT.toMPSTensor
  sectors :=
    { copies := fun _ ↦ 2
      copies_pos := fun _ ↦ by omega
      weight := fun _ q ↦ if q = 0 then 1 else 1 / 2
      weight_ne_zero := by
        intro _ q
        split_ifs
        · exact one_ne_zero
        · norm_num }

/-- The scalar repeated-copy MPO with raw BNT weights $1$ and $1/2$.

Its doubled-index MPS tensor is literally the canonical assembly
`repeatedCopyDecomposition` from the line-246 normalization convention of
arXiv:1606.00608 (lines 237--246 and 271--301). -/
noncomputable def repeatedCopyTensor :
    MPOTensor 1 repeatedCopyDecomposition.totalDim :=
  fun _ _ ↦ repeatedCopyDecomposition.toTensor 0

/-- The concrete repeated-copy MPO is exactly the raw-weight BNT assembly,
not merely an MPO with the same periodic contractions.

Source: arXiv:1606.00608, canonical form at lines 237--246 and equation
`eq:II_ABasicTensors` at lines 271--301. -/
theorem repeatedCopyTensor_toMPSTensor :
    repeatedCopyTensor.toMPSTensor = repeatedCopyDecomposition.toTensor := by
  funext i
  fin_cases i
  rfl

private lemma scalarBNT_evalWord (w : List (Fin 1)) :
    Kraus.evalWord scalarBNT.toMPSTensor w = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ih]
      simp [scalarBNT, toMPSTensor]

/-- The raw repeated-copy presentation satisfies the source's BNT canonical
form, including the global unit-weight convention but no equal-modulus
condition on repeated copies.

Source: arXiv:1606.00608, canonical-form normalization at lines 237--246 and
the BNT display at lines 271--301. -/
theorem repeatedCopyDecomposition_isBNTCanonicalForm :
    MPSTensor.IsBNTCanonicalForm repeatedCopyDecomposition := by
  refine {
    basis_dim_pos := by simp [repeatedCopyDecomposition]
    basis_irreducible := fun _ ↦
      MPSTensor.isIrreducibleTensor_of_bondDim_one scalarBNT.toMPSTensor
    basis_left_canonical := by
      intro j
      simp [MPSTensor.IsLeftCanonical, repeatedCopyDecomposition,
        scalarBNT, toMPSTensor]
    basis_normalized_self_overlap := by
      intro j
      simp [MPSTensor.mpvOverlap, MPSTensor.mpv, scalarBNT_evalWord,
        Matrix.trace]
    bnt_data := by
      refine ⟨0, ?_⟩
      intro N hN
      apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
      intro hzero
      have h := congrArg
        (fun v : MPSTensor.MPVSpace 1 N ↦ v (fun _ ↦ (0 : Fin 1))) hzero
      simp [MPSTensor.mpvState_apply, MPSTensor.mpv, scalarBNT_evalWord,
        Matrix.trace] at h
    basis_distinct := by
      intro j k hjk
      exact absurd (Subsingleton.elim j k) hjk
    weight_norm_le_one := by
      intro j q
      change ‖(if q = 0 then (1 : ℂ) else 1 / 2)‖ ≤ 1
      split_ifs <;> norm_num
    weight_unit_exists := by
      refine ⟨0, 0, ?_⟩
      change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else 1 / 2)‖ = 1
      simp }

private lemma scalarBNT_mpv {N : ℕ} (σ : Fin N → Fin 1) :
    MPSTensor.mpv scalarBNT.toMPSTensor σ = 1 := by
  simp [MPSTensor.mpv, scalarBNT_evalWord, Matrix.trace]

/-- Every periodic contraction of the repeated-copy MPO is
$1+(1/2)^N$.

This is the scalar coefficient of the canonical display in
arXiv:1606.00608, equations `eq:II_ABasicTensors` and `Eq19`, lines
271--308. -/
theorem repeatedCopyTensor_mpo (N : ℕ) (σ τ : Fin N → Fin 1) :
    mpo repeatedCopyTensor N σ τ = 1 + (1 / 2 : ℂ) ^ N := by
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
  rw [repeatedCopyTensor_toMPSTensor]
  rw [repeatedCopyDecomposition.mpv_toTensor_eq_sum_sectors]
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  rw [scalarBNT_mpv]
  simp only [mul_one]
  change (if (0 : Fin 2) = 0 then 1 else (1 / 2 : ℂ)) ^ N +
      (if (1 : Fin 2) = 0 then 1 else (1 / 2 : ℂ)) ^ N =
        1 + (1 / 2 : ℂ) ^ N
  norm_num

/-- The repeated-copy tensor generates a positive semidefinite operator at
every positive length, as required by the standing MPDO hypothesis of
arXiv:1606.00608, Theorem 4.9 (lines 851--856). -/
theorem repeatedCopyTensor_isMPDO : IsMPDO repeatedCopyTensor := by
  intro N hN
  have hMpo : mpo repeatedCopyTensor N =
      (1 + (1 / 2 : ℂ) ^ N) •
        (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
    ext σ τ
    have hστ : σ = τ := Subsingleton.elim _ _
    subst τ
    rw [repeatedCopyTensor_mpo]
    simp
  rw [hMpo]
  exact Matrix.PosSemidef.one.smul (by positivity)

/-- The scalar BNT representative generates positive operators at every
positive length, as required explicitly in condition (iv) of
arXiv:1606.00608, Theorem 4.9 (lines 863--868). -/
theorem scalarBNT_isMPDO : IsMPDO scalarBNT := by
  intro N hN
  have hMpo : mpo scalarBNT N =
      (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
    ext σ τ
    have hστ : σ = τ := Subsingleton.elim _ _
    subst τ
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
    rw [scalarBNT_mpv]
    simp
  rw [hMpo]
  exact Matrix.PosSemidef.one

/-- The physical-trace transfer of the sole BNT representative is the
one-by-one identity. -/
theorem physTraceTransfer_scalarBNT : physTraceTransfer scalarBNT = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [physTraceTransfer, scalarBNT]

/-- The sole BNT representative is nonnilpotent, which is precisely the
simplicity clause of arXiv:1606.00608, Definition 4.7 (lines 815--822). -/
theorem scalarBNT_physTraceTransfer_not_nilpotent :
    ¬ IsNilpotent (physTraceTransfer scalarBNT) := by
  rw [physTraceTransfer_scalarBNT]
  exact not_isNilpotent_one

/-- The unique normal representative already has simultaneous one-letter
span. This is the biCF condition used in Appendix C.2 of
arXiv:1606.00608, lines 1628--1633, specialized to one BNT element. -/
theorem scalarBNT_wordTupleSpanTop :
    MPSTensor.WordTupleSpanTop (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 := by
  simp only [mps_eval]
  apply top_unique
  intro X hX
  let w : Fin 1 → Fin 1 := fun _ ↦ 0
  have hGenerator :
      MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 w ∈
        Submodule.span ℂ (Set.range
          (MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1)) :=
    Submodule.subset_span (Set.mem_range_self w)
  have hEq : X = X 0 0 0 •
      MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 w := by
    funext k
    ext a b
    fin_cases k
    fin_cases a
    fin_cases b
    simp [MPSTensor.wordTuple, w, scalarBNT, toMPSTensor]
  rw [hEq]
  exact Submodule.smul_mem _ _ hGenerator

/-- Distinct BNT layers vanish under ordinary vertical composition.  In the
one-representative example the distinct-label premise is empty, but this is
the literal equation `KxKy=0` of condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 863--868. -/
theorem scalarBNT_layer_orthogonal :
    ∀ x y : Fin 1, x ≠ y →
      layerMul ((fun _ : Fin 1 ↦ scalarBNT) y)
        ((fun _ : Fin 1 ↦ scalarBNT) x) = 0 := by
  intro x y hxy
  exact absurd (Subsingleton.elim x y) hxy

/-- The one-dimensional physical space as one sector with one-dimensional
left and right factors.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def scalarSectorEquiv :
    Fin 1 ≃ Sigma fun _k : Fin 1 ↦ Fin 1 × Fin 1 where
  toFun _ := ⟨0, (0, 0)⟩
  invFun _ := 0
  left_inv i := Subsingleton.elim _ _
  right_inv := by
    rintro ⟨k, x, y⟩
    fin_cases k
    fin_cases x
    fin_cases y
    rfl

/-- The scalar BNT representative has the one-sector physical
factorization asserted in condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 869--889, and Appendix C.2,
equation `AppUkU=rl`, lines 1381--1388. -/
noncomputable def scalarFactorization :
    PhysicalSectorFactorization scalarBNT where
  sectorCount := 1
  leftDim := fun _ ↦ 1
  rightDim := fun _ ↦ 1
  leftDim_pos := fun _ ↦ by omega
  rightDim_pos := fun _ ↦ by omega
  sectorEquiv := scalarSectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun _ _ ↦ 1
  rightTensor := fun _ _ ↦ 1
  factorization := by
    intro beta alpha
    ext q r
    obtain ⟨k, x, y⟩ := q
    obtain ⟨h, u, v⟩ := r
    fin_cases k
    fin_cases h
    fin_cases x
    fin_cases y
    fin_cases u
    fin_cases v
    fin_cases beta
    fin_cases alpha
    simp [Matrix.reindex_apply, scalarSectorEquiv, physicalSlice, scalarBNT,
      Matrix.blockDiagonal'_apply_eq]

/-- The sole neighboring operator of `scalarFactorization` is the identity
density matrix.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
theorem scalarFactorization_neighboringOperator (k h) :
    scalarFactorization.neighboringOperator k h = 1 := by
  ext x y
  obtain ⟨xR, xL⟩ := x
  obtain ⟨yR, yL⟩ := y
  fin_cases k
  fin_cases h
  fin_cases xR
  fin_cases xL
  fin_cases yR
  fin_cases yL
  simp [PhysicalSectorFactorization.neighboringOperator_apply,
    scalarFactorization]

/-- The scalar factorization has positive neighboring operators and the
rank-one trace factorization required in condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 869--889, and Appendix C.2,
lines 1389--1403. -/
noncomputable def scalarNeighboringTraceFactorization :
    PhysicalSectorFactorization.NeighboringTraceFactorization
      scalarFactorization where
  neighboringOperator_pos := by
    intro k h
    rw [scalarFactorization_neighboringOperator]
    exact Matrix.PosSemidef.one
  a := fun _ ↦ 1
  b := fun _ ↦ 1
  trace_neighboringOperator := by
    intro k h
    fin_cases k
    fin_cases h
    rw [scalarFactorization_neighboringOperator]
    simp only [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
    dsimp [scalarFactorization]
    norm_num
  sum_mul := by
    change ∑ _ : Fin 1, (1 : ℝ) * 1 = 1
    simp

private lemma evalWord_replicate_repeatedCopyTensor (N : ℕ) :
    evalWord repeatedCopyTensor (List.replicate N 0) (List.replicate N 0) =
      (repeatedCopyTensor 0 0) ^ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [List.replicate_succ, evalWord_cons, ih, pow_succ']

/-- The trace of the `N`-th power of the sole local matrix retains the two
raw copy weights as $1+2^{-N}$.

Source: arXiv:1606.00608, equations `eq:II_ABasicTensors` and `Eq19`, lines
271--308. -/
theorem trace_repeatedCopyTensor_pow (N : ℕ) :
    Matrix.trace ((repeatedCopyTensor 0 0) ^ N) =
      1 + (1 / 2 : ℂ) ^ N := by
  have h := repeatedCopyTensor_mpo N (fun _ ↦ 0) (fun _ ↦ 0)
  rw [mpo_apply, mpoMatrixEntry] at h
  simpa [List.ofFn_const, evalWord_replicate_repeatedCopyTensor] using h

/-- The physical-trace transfer after two-site blocking is the square of the
sole local matrix. -/
theorem physTraceTransfer_blockTwo_repeatedCopyTensor :
    physTraceTransfer (blockTwo repeatedCopyTensor) =
      (repeatedCopyTensor 0 0) ^ 2 := by
  rw [physTraceTransfer, Fin.sum_univ_one]
  change repeatedCopyTensor 0 0 * repeatedCopyTensor 0 0 =
    (repeatedCopyTensor 0 0) ^ 2
  rw [pow_two]

/-- The two-site-blocked repeated-copy tensor cannot satisfy the tp-CP-map
renormalization-fixed-point equations of Definition 4.1.

Indeed, Definition 4.1 would make its physical-trace transfer idempotent.  In
this example that would identify the traces $1+2^{-4}$ and $1+2^{-2}$.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and the claimed
conclusion (v) of Theorem 4.9 at lines 890--892. -/
theorem blockTwo_repeatedCopyTensor_not_isRFPViaTS :
    ¬ IsRFPViaTS (blockTwo repeatedCopyTensor) := by
  intro hRFP
  have hsq := physTraceTransfer_sq_of_isRFPViaTS
    (blockTwo repeatedCopyTensor) hRFP
  rw [physTraceTransfer_blockTwo_repeatedCopyTensor] at hsq
  have hpowers : (repeatedCopyTensor 0 0) ^ 4 =
      (repeatedCopyTensor 0 0) ^ 2 := by
    calc
      (repeatedCopyTensor 0 0) ^ 4 =
          (repeatedCopyTensor 0 0) ^ 2 *
            (repeatedCopyTensor 0 0) ^ 2 := by noncomm_ring
      _ = (repeatedCopyTensor 0 0) ^ 2 := hsq
  have htrace := congrArg Matrix.trace hpowers
  rw [trace_repeatedCopyTensor_pow, trace_repeatedCopyTensor_pow] at htrace
  norm_num at htrace

/-- A counterexample to the literal implication (iv)$\Rightarrow$(v) printed
in arXiv:1606.00608, Theorem 4.9.

The tensor is exactly its raw BNT canonical assembly with weights $1$ and
$1/2$, generates MPDOs, and has a nonnilpotent sole normal representative.
That representative has simultaneous one-letter span, generates MPDOs,
satisfies the distinct-layer equation, and admits the full physical-sector
and neighboring-trace factorization of condition (iv).  Nevertheless the
two-site block, which still generates MPDOs, fails Definition 4.1.

Thus the literal implication (iv)$\Rightarrow$(v) is a refuted, unfaithful
statement.  The source proof has proof-path drift: lines 1646--1665 first use
condition (ii), zero correlation length, to make repeated-copy weights equal
and absorb their common value before invoking Proposition C.7.  That stronger
(ii)$\Rightarrow$(v) route is not contradicted by this example.

Source: arXiv:1606.00608, Theorem 4.9 at lines 851--892; canonical-form
normalization at lines 237--246; Appendix C.2 at lines 1381--1403 and
1646--1665; Definition 4.1 at lines 638--660. -/
theorem printed_theorem49_iv_to_v_is_false :
    repeatedCopyDecomposition.weight 0 0 = 1 ∧
      repeatedCopyDecomposition.weight 0 1 = (1 / 2 : ℂ) ∧
      repeatedCopyTensor.toMPSTensor = repeatedCopyDecomposition.toTensor ∧
      MPSTensor.IsBNTCanonicalForm repeatedCopyDecomposition ∧
      IsMPDO repeatedCopyTensor ∧
      ¬ IsNilpotent (physTraceTransfer scalarBNT) ∧
      MPSTensor.WordTupleSpanTop
        (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 ∧
      IsMPDO scalarBNT ∧
      (∀ x y : Fin 1, x ≠ y →
        layerMul ((fun _ : Fin 1 ↦ scalarBNT) y)
          ((fun _ : Fin 1 ↦ scalarBNT) x) = 0) ∧
      Nonempty (PhysicalSectorFactorization.NeighboringTraceFactorization
        scalarFactorization) ∧
      IsMPDO (blockTwo repeatedCopyTensor) ∧
      ¬ IsRFPViaTS (blockTwo repeatedCopyTensor) := by
  exact ⟨rfl, rfl, repeatedCopyTensor_toMPSTensor,
    repeatedCopyDecomposition_isBNTCanonicalForm, repeatedCopyTensor_isMPDO,
    scalarBNT_physTraceTransfer_not_nilpotent, scalarBNT_wordTupleSpanTop,
    scalarBNT_isMPDO, scalarBNT_layer_orthogonal,
    ⟨scalarNeighboringTraceFactorization⟩,
    repeatedCopyTensor_isMPDO.blockTwo,
    blockTwo_repeatedCopyTensor_not_isRFPViaTS⟩

end MPOTensor.CaseIIAbsorptionCounterexample
