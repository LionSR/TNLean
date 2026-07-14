/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Examples
import TNLean.MPS.RFP.PhaseMultiplicityCounterexample
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Raw BNT weights obstruct the unrestricted pure ZCL equivalence

The proof of arXiv:1606.00608, Theorem `TheoremZCLPure`, passes at lines
1248--1251 from non-idempotence of the full transfer operator to
non-idempotence of one normal basis tensor.  This implication fails for the
two-layer BNT display: raw copy weights can make the assembled transfer
non-idempotent even when the unique normal basis tensor has idempotent transfer.

The concrete example below uses one physical letter, the scalar normal basis
tensor `scalarUnitTensor`, and the two raw copy weights `1` and `1/2` from
`SectorBNT.Examples.halvedDecomp`.  Its physical Hilbert space is
one-dimensional, so all physical correlations are independent of separation;
there are no distinct BNT sectors, so local orthogonality is automatic.  The
assembled transfer is nevertheless not idempotent.

See `docs/paper-gaps/cpsv16_pure_zcl_raw_weight_counterexample.tex`.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

/-- The canonical assembly of the one-letter tensor with raw BNT copy weights
`1` and `1/2`.

This is the two-layer tensor associated with `halvedDecomp scalarUnitTensor`
from CPSV16 equation `eq:II_ABasicTensors` (lines 271--301). -/
noncomputable def halvedWeightTensor : MPSTensor 1
    (SectorBNT.Examples.halvedDecomp scalarUnitTensor).totalDim :=
  (SectorBNT.Examples.halvedDecomp scalarUnitTensor).toTensor

/-- The counterexample tensor is literally the canonical assembly of its
raw-weight BNT decomposition, not merely an equivalent MPV family.

This records the canonical-form premise of CPSV16, Theorem 3.8. -/
theorem halvedWeightTensor_eq_halvedDecomp_toTensor :
    halvedWeightTensor =
      (SectorBNT.Examples.halvedDecomp scalarUnitTensor).toTensor := rfl

private lemma scalarUnitTensor_isIrreducibleTensor :
    IsIrreducibleTensor scalarUnitTensor := by
  rintro ⟨P, ⟨_, hIdem⟩, hP0, hP1, _⟩
  have h00 := congrFun (congrFun hIdem (0 : Fin 1)) (0 : Fin 1)
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton] at h00
  have hfactor : P 0 0 * (P 0 0 - 1) = 0 := by
    linear_combination h00
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · apply hP0
    ext a b
    fin_cases a
    fin_cases b
    simpa using hzero
  · apply hP1
    ext a b
    fin_cases a
    fin_cases b
    simpa using sub_eq_zero.mp hone

private lemma scalarUnitTensor_evalWord (w : List (Fin 1)) :
    evalWord scalarUnitTensor w = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [evalWord_cons, ih]
      simp [scalarUnitTensor]

private lemma scalarUnitTensor_mpv {N : ℕ} (σ : Fin N → Fin 1) :
    mpv scalarUnitTensor σ = 1 := by
  simp [mpv, scalarUnitTensor_evalWord, Matrix.trace]

/-- The matrix-product-vector coefficient of the raw-weight canonical assembly.

This is the length-`N` coefficient of the example testing the unrestricted
implication in CPSV16, Theorem `TheoremZCLPure` (lines 1248--1251). -/
theorem halvedWeightTensor_mpv {N : ℕ} (σ : Fin N → Fin 1) :
    mpv halvedWeightTensor σ = 1 + (1 / 2 : ℂ) ^ N := by
  rw [halvedWeightTensor]
  rw [(SectorBNT.Examples.halvedDecomp scalarUnitTensor).mpv_toTensor_eq_sum_sectors]
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  rw [scalarUnitTensor_mpv]
  simp only [mul_one]
  change (if (0 : Fin 2) = 0 then 1 else 1 / 2) ^ N +
      (if (1 : Fin 2) = 0 then 1 else 1 / 2) ^ N =
    1 + (1 / 2 : ℂ) ^ N
  norm_num

private theorem physicalObservableTransfer_one
    {D : ℕ} (A : MPSTensor 1 D) (L : ℕ)
    (O : Matrix (Fin L → Fin 1) (Fin L → Fin 1) ℂ) :
    physicalObservableTransfer A L O =
      O (0 : Fin L → Fin 1) (0 : Fin L → Fin 1) • (transferMap A) ^ L := by
  apply LinearMap.ext
  intro X
  change physicalObservableTransfer A L O X =
    O (0 : Fin L → Fin 1) (0 : Fin L → Fin 1) • ((transferMap A) ^ L) X
  rw [transferMap_pow_apply']
  simp only [physicalObservableTransfer, Finset.univ_unique, Pi.default_def,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, List.ofFn_const]
  rw [Matrix.mul_assoc]
  congr 1

private theorem isPhysicalCID_one {D : ℕ} (A : MPSTensor 1 D) :
    IsPhysicalCID A := by
  intro L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ hL₁ hL₂ hsum
  simp only [physicalTwoPointExpectation, physicalObservableTransfer_one]
  congr 1
  simp only [← Module.End.mul_eq_comp]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp only [← pow_add]
  congr 1
  omega

private theorem scalarUnitTensor_transferMap :
    transferMap scalarUnitTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [transferMap_apply, scalarUnitTensor]

private theorem scalarUnitTensor_isNormalTensor :
    IsNormalTensor scalarUnitTensor := by
  refine ⟨scalarUnitTensor_isIrreducibleTensor, ?_, ?_⟩
  · rw [scalarUnitTensor_transferMap]
    change spectralRadius ℂ
      (1 : Matrix (Fin 1) (Fin 1) ℂ →L[ℂ] Matrix (Fin 1) (Fin 1) ℂ) = 1
    exact spectrum.spectralRadius_one
  · rw [scalarUnitTensor_transferMap]
    apply isPrimitive_of_unique_norm_one LinearMap.id
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
    · rfl
    · exact one_ne_zero
    · intro μ hμ hμnorm
      obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
      have hEq := hX.apply_eq_smul
      have hX00 : X 0 0 ≠ 0 := by
        intro hzero
        apply hX.2
        ext a b
        fin_cases a
        fin_cases b
        simpa using hzero
      have hEq00 := congrFun (congrFun hEq (0 : Fin 1)) (0 : Fin 1)
      simp only [LinearMap.id_apply, Matrix.smul_apply] at hEq00
      simp only [smul_eq_mul] at hEq00
      apply mul_right_cancel₀ hX00
      simpa using hEq00.symm

/-- The raw-weight decomposition of `halvedWeightTensor` is a BNT canonical
form in the line-246 normalization of arXiv:1606.00608. -/
theorem halvedWeightTensor_isBNTCanonicalForm :
    IsBNTCanonicalForm (SectorBNT.Examples.halvedDecomp scalarUnitTensor) := by
  refine {
    basis_dim_pos := by
      intro j
      simp
    basis_irreducible := by
      intro j
      exact scalarUnitTensor_isIrreducibleTensor
    basis_left_canonical := by
      intro j
      simp [IsLeftCanonical, scalarUnitTensor]
    basis_normalized_self_overlap := by
      intro j
      simp [mpvOverlap, mpv, scalarUnitTensor_evalWord, Matrix.trace]
    bnt_data := by
      refine ⟨0, ?_⟩
      intro N hN
      apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
      intro hzero
      have h := congrArg
        (fun v : MPVSpace 1 N => v (fun _ : Fin N => (0 : Fin 1))) hzero
      have : (1 : ℂ) = 0 := by
        simp [mpvState_apply, mpv, scalarUnitTensor_evalWord, Matrix.trace] at h
      exact one_ne_zero this
    basis_distinct := by
      intro j k hjk
      exact absurd (Subsingleton.elim j k) hjk
    weight_norm_le_one := by
      intro j q
      change ‖(if q = 0 then (1 : ℂ) else (1 / 2 : ℂ))‖ ≤ 1
      split_ifs
      · simp
      · simp
        norm_num
    weight_unit_exists := by
      refine ⟨0, 0, ?_⟩
      change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else (1 / 2 : ℂ))‖ = 1
      simp }

/-- `halvedWeightTensor` realizes the MPV family of the raw-weight
decomposition `halvedDecomp scalarUnitTensor` at every length. -/
theorem halvedWeightTensor_sameMPV₂_halvedDecomp :
    SameMPV₂ halvedWeightTensor
      (SectorBNT.Examples.halvedDecomp scalarUnitTensor).toTensor := by
  intro N σ
  rfl

private theorem halvedWeightTensor_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors halvedWeightTensor
      (fun _ : Fin 1 => ⟨1, scalarUnitTensor⟩) := by
  refine {
    blocks_normal := fun _ => scalarUnitTensor_isNormalTensor
    spans_mpv := by
      intro N
      refine ⟨fun _ => 1 + (1 / 2 : ℂ) ^ N, ?_⟩
      intro σ
      rw [halvedWeightTensor_mpv σ]
      simp [mpv, scalarUnitTensor_evalWord, Matrix.trace]
    eventually_li := by
      exact halvedWeightTensor_isBNTCanonicalForm.bnt_data }

/-- The concrete raw-weight tensor satisfies the source-facing pure-state ZCL
premises of arXiv:1606.00608, Definitions 3.3, 3.5, and 3.6. -/
theorem halvedWeightTensor_isPhysicalBNTZCL :
    IsPhysicalBNTZCL halvedWeightTensor (fun _ : Fin 1 => scalarUnitTensor) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using halvedWeightTensor_isCPSVBasisOfNormalTensors
  · exact isPhysicalCID_one halvedWeightTensor
  · intro j k hjk
    exact absurd (Subsingleton.elim j k) hjk

/-- The raw weights `1` and `1/2` obstruct the one-letter blocking equation:
the two diagonal blocks would force the same scalar to be both `1` and `1/2`.
This is the failure missed at arXiv:1606.00608, lines 1248--1251. -/
private theorem halvedWeightTensor_no_blocking_coefficient :
    ¬ ∃ v : ℂ,
      halvedWeightTensor 0 * halvedWeightTensor 0 = v • halvedWeightTensor 0 := by
  rintro ⟨v, hv⟩
  let P := SectorBNT.Examples.halvedDecomp scalarUnitTensor
  let B : (s : Fin P.totalCopies) →
      Matrix (Fin (P.flatDim s)) (Fin (P.flatDim s)) ℂ :=
    fun s => (P.flatWeight s) • (P.flatBasis s 0)
  let e : ((s : Fin P.totalCopies) × Fin (P.flatDim s)) ≃ Fin P.totalDim :=
    finSigmaFinEquiv
  change (Matrix.reindex e e (Matrix.blockDiagonal' B)) *
      (Matrix.reindex e e (Matrix.blockDiagonal' B)) =
        v • Matrix.reindex e e (Matrix.blockDiagonal' B) at hv
  change (Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.blockDiagonal' B)) *
      (Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.blockDiagonal' B)) =
        v • Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.blockDiagonal' B) at hv
  rw [← map_mul, ← map_smul] at hv
  have hbase : Matrix.blockDiagonal' B * Matrix.blockDiagonal' B =
      v • Matrix.blockDiagonal' B :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).injective hv
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_smul] at hbase
  let s0 : Fin P.totalCopies := P.flatIndexEquiv ⟨0, 0⟩
  let s1 : Fin P.totalCopies := P.flatIndexEquiv ⟨0, 1⟩
  let z0 : Fin (P.flatDim s0) :=
    ⟨0, by simp [P, SectorDecomposition.flatDim]⟩
  let z1 : Fin (P.flatDim s1) :=
    ⟨0, by simp [P, SectorDecomposition.flatDim]⟩
  have h0 := congrFun (congrFun hbase ⟨s0, z0⟩) ⟨s0, z0⟩
  have h1 := congrFun (congrFun hbase ⟨s1, z1⟩) ⟨s1, z1⟩
  have hdim0 : P.flatDim s0 = 1 := by
    simp [P, SectorDecomposition.flatDim]
  have hdim1 : P.flatDim s1 = 1 := by
    simp [P, SectorDecomposition.flatDim]
  have hsub0 (x : Fin (P.flatDim s0)) : x = z0 := by
    apply Fin.ext
    have hx := x.isLt
    omega
  have hsub1 (x : Fin (P.flatDim s1)) : x = z1 := by
    apply Fin.ext
    have hx := x.isLt
    omega
  have hone0 :
      (1 : Matrix (Fin (P.flatDim s0)) (Fin (P.flatDim s0)) ℂ) z0 z0 = 1 := by
    rw [Matrix.one_apply]
    simp
  have hone1 :
      (1 : Matrix (Fin (P.flatDim s1)) (Fin (P.flatDim s1)) ℂ) z1 z1 = 1 := by
    rw [Matrix.one_apply]
    simp
  simp only [Matrix.blockDiagonal'_apply_eq] at h0 h1
  dsimp [B] at h0 h1
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h0 h1
  simp_rw [hsub0] at h0
  simp_rw [hsub1] at h1
  dsimp [P, s0, s1, z0, z1] at h0 h1
  simp only [SectorDecomposition.flatWeight, SectorDecomposition.flatBasis] at h0 h1
  rw [Equiv.symm_apply_apply] at h0 h1
  dsimp [SectorBNT.Examples.halvedDecomp, scalarUnitTensor] at h0 h1
  dsimp [SectorDecomposition.weight, SectorWeightData.weight] at h0 h1
  norm_num [SectorDecomposition.flatDim] at h0 h1
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · have hv1 : v = 1 := h0.symm.trans hone0
      have hvhalf : (1 / 2 : ℂ) = v := by
        calc
          (1 / 2 : ℂ) = (1 / 2) * 1 := by ring
          _ = (1 / 2) * (1 : Matrix (Fin (P.flatDim s1))
              (Fin (P.flatDim s1)) ℂ) z1 z1 :=
            congrArg (fun x : ℂ => (1 / 2) * x) hone1.symm
          _ = v := h1
      rw [hv1] at hvhalf
      norm_num at hvhalf
    · exact one_ne_zero (hone1.symm.trans h1)
  · exact one_ne_zero (hone0.symm.trans h0)

/-- The concrete raw-weight tensor is not a renormalization fixed point.

The Kraus-isometry characterization of arXiv:1606.00608, Theorem 3.1,
would give a scalar one-letter blocking coefficient, contradicting
`halvedWeightTensor_no_blocking_coefficient`. -/
theorem halvedWeightTensor_not_isRFP : ¬ IsRFP halvedWeightTensor := by
  intro hRFP
  apply halvedWeightTensor_no_blocking_coefficient
  obtain ⟨V, _, hprod⟩ := (isRFP_iff_kraus_isometry halvedWeightTensor).mp hRFP
  refine ⟨V ((0 : Fin 1), (0 : Fin 1)) (0 : Fin 1), ?_⟩
  simpa using hprod (0 : Fin 1) (0 : Fin 1)

/-- The tensor `halvedWeightTensor` is a counterexample to the unrestricted
pure-state zero-correlation-length equivalence asserted in arXiv:1606.00608,
Theorem `TheoremZCLPure`.  It is exactly the tensor assembled from its BNT
canonical form and satisfies the source-facing physical zero-correlation-length
conditions, but it is not a renormalization fixed point.  The source proof's
inference at lines 1248--1251 misses the eigenvalues introduced by raw copy
weights. -/
theorem halvedWeightTensor_counterexample_to_unrestricted_zcl_iff_rfp :
    IsBNTCanonicalForm (SectorBNT.Examples.halvedDecomp scalarUnitTensor) ∧
      halvedWeightTensor =
        (SectorBNT.Examples.halvedDecomp scalarUnitTensor).toTensor ∧
      SameMPV₂ halvedWeightTensor
        (SectorBNT.Examples.halvedDecomp scalarUnitTensor).toTensor ∧
      IsPhysicalBNTZCL halvedWeightTensor (fun _ : Fin 1 => scalarUnitTensor) ∧
      ¬ IsRFP halvedWeightTensor := by
  exact ⟨halvedWeightTensor_isBNTCanonicalForm,
    halvedWeightTensor_eq_halvedDecomp_toTensor,
    halvedWeightTensor_sameMPV₂_halvedDecomp,
    halvedWeightTensor_isPhysicalBNTZCL,
    halvedWeightTensor_not_isRFP⟩

end MPSTensor
