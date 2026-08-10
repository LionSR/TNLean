/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.MPS.Core.Blocking
import TNLean.MPS.RFP.PhaseOscillation

/-!
# A counterexample to blocking up to virtual gauge implying an RFP

Appendix D, equation `RFP-gauge`, of arXiv:1606.00608 asserts that in the pure case,
blocking up to a virtual gauge is equivalent to the ordinary renormalization fixed-point
condition. The one-letter tensor `cubePhaseTensor`, whose matrix is
$\operatorname{diag}(1,\omega)$ for a primitive cube root $\omega$, refutes this assertion.
If `cubeSwapGauge` exchanges the two virtual coordinates, then
$$
  A=\omega S A^2S^{-1}.
$$
Thus the two-site blocking is gauge-phase equivalent to the original tensor with the
orientation printed in `APPE_Fig1.png`, while the transfer map is not idempotent.

See `docs/paper-gaps/cpsv16_rfp_gauge_pure_equivalence_false.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private noncomputable def cubeSigmaSwap :
    ((k : Fin 2) × Fin (cubePhaseBondDim k)) ≃
      ((k : Fin 2) × Fin (cubePhaseBondDim k)) where
  toFun x := ⟨Equiv.swap 0 1 x.1, x.2⟩
  invFun x := ⟨Equiv.swap 0 1 x.1, x.2⟩
  left_inv x := by
    rcases x with ⟨k, a⟩
    simp
  right_inv x := by
    rcases x with ⟨k, a⟩
    simp

/-- The virtual-coordinate permutation exchanging the $1$ and $\omega$ blocks of
`cubePhaseTensor`. -/
noncomputable def cubeCoordinateSwap :
    Equiv.Perm (Fin (∑ k : Fin 2, cubePhaseBondDim k)) :=
  finSigmaFinEquiv.symm.trans (cubeSigmaSwap.trans finSigmaFinEquiv)

/-- The permutation matrix of `cubeCoordinateSwap`, regarded as an invertible virtual gauge. -/
noncomputable def cubeSwapGauge :
    GL (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ :=
  ⟨Equiv.Perm.permMatrix ℂ cubeCoordinateSwap,
    Equiv.Perm.permMatrix ℂ cubeCoordinateSwap.symm,
    by
      rw [← Matrix.permMatrix_mul]
      change Equiv.Perm.permMatrix ℂ (cubeCoordinateSwap⁻¹ * cubeCoordinateSwap) = 1
      rw [inv_mul_cancel]
      exact Matrix.permMatrix_one,
    by
      rw [← Matrix.permMatrix_mul]
      change Equiv.Perm.permMatrix ℂ (cubeCoordinateSwap * cubeCoordinateSwap⁻¹) = 1
      rw [mul_inv_cancel]
      exact Matrix.permMatrix_one⟩

private lemma permMatrix_apply' {n : Type*} [DecidableEq n] (σ : Equiv.Perm n)
    (i j : n) :
    Equiv.Perm.permMatrix ℂ σ i j = if j = σ i then (1 : ℂ) else 0 := by
  rw [Equiv.Perm.permMatrix]
  by_cases h : j = σ i
  · subst h
    rw [if_pos rfl, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp
  · rw [if_neg h, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq, ite_eq_right_iff,
      one_ne_zero, imp_false]
    exact fun heq => h heq.symm

private lemma permMatrix_mul_eq_submatrix {n : Type*}
    [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M = M.submatrix σ id := by
  ext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id]
  simp_rw [permMatrix_apply', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (σ i)]
  simp

private lemma mul_permMatrix_eq_submatrix {n : Type*}
    [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    M * Equiv.Perm.permMatrix ℂ σ = M.submatrix id σ.symm := by
  ext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id]
  simp_rw [permMatrix_apply', mul_ite, mul_one, mul_zero]
  have hcond : ∀ x : n, (j = σ x) ↔ (σ.symm j = x) := by
    intro x
    constructor
    · intro h; rw [h]; exact σ.symm_apply_apply x
    · intro h; rw [← h]; exact (σ.apply_symm_apply j).symm
  simp_rw [hcond]
  rw [Finset.sum_ite_eq Finset.univ (σ.symm j)]
  simp

private lemma permMatrix_conj_eq_submatrix {n : Type*}
    [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M * Equiv.Perm.permMatrix ℂ σ.symm =
      M.submatrix σ σ := by
  rw [permMatrix_mul_eq_submatrix, mul_permMatrix_eq_submatrix,
    Matrix.submatrix_submatrix]
  simp

private theorem primitiveCubeRoot_isPrimitiveRoot' :
    IsPrimitiveRoot primitiveCubeRoot 3 := by
  simpa [primitiveCubeRoot, mul_assoc] using
    Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The chosen primitive cube root has cube equal to one. -/
lemma primitiveCubeRoot_pow_three : primitiveCubeRoot ^ 3 = 1 :=
  primitiveCubeRoot_isPrimitiveRoot'.pow_eq_one

/-- The chosen primitive cube root is nonzero. -/
lemma primitiveCubeRoot_ne_zero : primitiveCubeRoot ≠ 0 :=
  primitiveCubeRoot_isPrimitiveRoot'.ne_zero (by norm_num)

/-- The chosen primitive cube root is nontrivial. -/
lemma primitiveCubeRoot_ne_one : primitiveCubeRoot ≠ 1 :=
  primitiveCubeRoot_isPrimitiveRoot'.ne_one (by norm_num)

/-- The chosen primitive cube root is a unit phase. -/
lemma norm_primitiveCubeRoot : ‖primitiveCubeRoot‖ = 1 := by
  simp [primitiveCubeRoot, Complex.norm_exp, Complex.mul_re]

/-- The canonical-form data of the cube-phase tensor satisfy the normalization at
arXiv:1606.00608, line 246. -/
theorem cubePhaseCanonicalData_isWeightNormalized :
    cubePhaseCanonicalData.IsWeightNormalized := by
  refine {
    weight_norm_le_one := ?_
    weight_unit_exists := ?_ }
  · change ∀ k : Fin 2, ‖cubePhaseWeight k‖ ≤ 1
    intro k
    fin_cases k
    · simp [cubePhaseWeight]
    · simp [cubePhaseWeight, norm_primitiveCubeRoot]
  · change cubePhaseTensor ≠ 0 → ∃ k : Fin 2, ‖cubePhaseWeight k‖ = 1
    intro _
    exact ⟨0, by simp [cubePhaseWeight]⟩

private lemma blockTensor_cubePhaseTensor_two (i : Fin 1) :
    blockTensor cubePhaseTensor 2 i =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k =>
          (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
            (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change cubePhaseTensor 0 * (cubePhaseTensor 0 * 1) = _
  rw [Matrix.mul_one]
  change Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k =>
        cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k =>
        cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = _
  let B := Matrix.blockDiagonal' fun k =>
    cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  calc
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv B *
        Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv B =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (B * B) :=
        Matrix.reindexLinearEquiv_mul ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
          finSigmaFinEquiv B B
    _ = Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k =>
          (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
            (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
      apply congrArg (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
      exact (Matrix.blockDiagonal'_mul _ _).symm

/-- The blocked gauge-phase identity with the orientation of equation `RFP-gauge` in
arXiv:1606.00608, lines 2100--2107:
$A=\omega S A^{[2]}S^{-1}$. -/
theorem cube_phase_blocked_gauge_identity (i : Fin 1) :
    cubePhaseTensor i = primitiveCubeRoot •
      ((cubeSwapGauge : Matrix _ _ ℂ) * blockTensor cubePhaseTensor 2 i *
        ((cubeSwapGauge⁻¹ : GL (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ) :
          Matrix _ _ ℂ)) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [blockTensor_cubePhaseTensor_two]
  ext a b
  rw [show (cubeSwapGauge : Matrix _ _ ℂ) =
      Equiv.Perm.permMatrix ℂ cubeCoordinateSwap from rfl,
    show ((cubeSwapGauge⁻¹ : GL (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ) :
      Matrix _ _ ℂ) = Equiv.Perm.permMatrix ℂ cubeCoordinateSwap.symm from rfl]
  rw [permMatrix_conj_eq_submatrix]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]
  rcases ha : finSigmaFinEquiv.symm a with ⟨ka, aa⟩
  rcases hb : finSigmaFinEquiv.symm b with ⟨kb, bb⟩
  have hcube : primitiveCubeRoot * (primitiveCubeRoot * primitiveCubeRoot) = 1 := by
    calc
      primitiveCubeRoot * (primitiveCubeRoot * primitiveCubeRoot) =
          primitiveCubeRoot ^ 3 := by ring
      _ = 1 := primitiveCubeRoot_pow_three
  fin_cases ka <;> fin_cases aa <;> fin_cases kb <;> fin_cases bb <;>
    simp [cubeCoordinateSwap, cubeSigmaSwap, cubePhaseTensor, toTensorFromBlocks,
      Matrix.reindex_apply, Matrix.blockDiagonal'_apply, cubePhaseWeight, cubePhaseBondDim,
      scalarUnitTensor, ha, hb, hcube]


/-- The one-physical-letter MPS lift of the blocking-up-to-virtual-gauge diagram
`RFP-gauge` in arXiv:1606.00608, lines 2100--2107.

For one physical letter, both the original and two-site blocked physical spaces are
singletons. The physical unitary in the pure-state source diagram is therefore a scalar
of unit norm. This predicate states precisely the resulting MPS identity, with the
orientation printed in the diagram. It is sufficient for the counterexample below; no
equivalence with the full doubled-MPDO $T/S$ diagram is claimed. -/
def IsBlockedGaugePhaseFixedPoint (A : MPSTensor 1 D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧ ∀ i : Fin 1,
    A i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * blockTensor A 2 i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-- The cube-phase tensor satisfies equation `RFP-gauge` in arXiv:1606.00608,
lines 2100--2107, with a unit physical phase. -/
theorem cubePhaseTensor_isBlockedGaugePhaseFixedPoint :
    IsBlockedGaugePhaseFixedPoint cubePhaseTensor := by
  refine ⟨cubeSwapGauge, primitiveCubeRoot, norm_primitiveCubeRoot, ?_⟩
  exact cube_phase_blocked_gauge_identity

/-- The cube-phase tensor is not an ordinary pure-state renormalization fixed point.

If its transfer map were idempotent, every positive power would equal the transfer map,
so the dyadic transfer orbit would converge. This contradicts the explicit cube-phase
oscillation proved in `cubePhaseTensor_not_tendsto_dyadic_transferMap`. -/
theorem cubePhaseTensor_not_isTransferIdempotent :
    ¬ IsTransferIdempotent cubePhaseTensor := by
  intro hRFP
  have hIdem : IsIdempotentElem (transferMap cubePhaseTensor) := by
    rw [IsIdempotentElem]
    apply LinearMap.ext
    intro ρ
    simpa [Module.End.mul_apply, LinearMap.comp_apply, IsTransferIdempotent] using
      LinearMap.congr_fun hRFP ρ
  exact cubePhaseTensor_not_tendsto_dyadic_transferMap.2.2 ⟨
    transferMap cubePhaseTensor, fun ρ =>
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => by
        dsimp
        rw [hIdem.pow_eq (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))])⟩

/-- The cube-phase witness is in normalized CPSV canonical form, satisfies the
one-letter blocking-up-to-gauge diagram with a unit phase, and is not transfer-idempotent. -/
theorem cubePhaseTensor_normalized_canonical_gauge_not_rfp :
    IsCPSVCanonicalForm cubePhaseTensor ∧
      cubePhaseCanonicalData.IsWeightNormalized ∧
      IsBlockedGaugePhaseFixedPoint cubePhaseTensor ∧
      ¬ IsTransferIdempotent cubePhaseTensor :=
  ⟨cubePhaseTensor_not_tendsto_dyadic_transferMap.1,
    cubePhaseCanonicalData_isWeightNormalized,
    cubePhaseTensor_isBlockedGaugePhaseFixedPoint,
    cubePhaseTensor_not_isTransferIdempotent⟩

/-- The normalized canonical-form pure-state equivalence asserted after equation
`RFP-gauge` in arXiv:1606.00608, lines 2100--2107, is false, already for tensors with
one physical letter. -/
theorem cpsv16_pure_rfp_gauge_equivalence_false :
    ¬ ∀ (D : ℕ) (A : MPSTensor 1 D), IsCPSVCanonicalForm A →
      (∃ data : CPSVCanonicalFormData A, data.IsWeightNormalized) →
      (IsBlockedGaugePhaseFixedPoint A ↔ IsTransferIdempotent A) := by
  intro hEquiv
  exact cubePhaseTensor_not_isTransferIdempotent
    ((hEquiv _ cubePhaseTensor
      cubePhaseTensor_normalized_canonical_gauge_not_rfp.1
      ⟨cubePhaseCanonicalData,
        cubePhaseTensor_normalized_canonical_gauge_not_rfp.2.1⟩).mp
          cubePhaseTensor_isBlockedGaugePhaseFixedPoint)

end MPSTensor
