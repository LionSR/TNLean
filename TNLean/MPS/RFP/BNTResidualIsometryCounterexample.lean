/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.ResidualIsometry

/-!
# An unused BNT member obstructs the unrestricted CPSV residual isometry

The literal basis-of-normal-tensors definition in arXiv:1606.00608, lines 271--274, permits
normal tensors whose coefficient is zero at every length.  Corollary 3.12 (lines 583--590),
and its proof at line 1303, nevertheless applies the joint residual isometry to every listed
BNT member.

The bond-one example below takes $A^0=1$, $A^1=0$ and the unused normal tensor
$B^0=B^1=1/\sqrt{2}$.  The family $(A,B)$ is eventually linearly independent, so it is a
literal BNT for $A$ with coefficient zero on $B$.  Both tensors have identity transfer map,
but their physical vectors have nonzero inner product.  Hence they cannot satisfy the
cross-member clause of `IsResidualIsometryFamily`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The bond-one RFP tensor $A^0=1$, $A^1=0$. -/
noncomputable def corollary312Tensor : MPSTensor 2 1 :=
  fun i => if i = 0 then 1 else 0

/-- The unused bond-one normal tensor $B^0=B^1=1/\sqrt{2}$. -/
noncomputable def corollary312UnusedTensor : MPSTensor 2 1 :=
  fun _ => (Real.sqrt 2 : ℂ)⁻¹ • 1

private lemma corollary312Tensor_transferMap :
    transferMap corollary312Tensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext x y
  fin_cases x
  fin_cases y
  simp [transferMap_apply, corollary312Tensor]

private lemma invSqrtTwo_mul_self :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  have hs : (↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  field_simp
  simpa [pow_two] using hs.symm

private lemma corollary312UnusedTensor_transferMap :
    transferMap corollary312UnusedTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext x y
  fin_cases x
  fin_cases y
  simp [transferMap_apply, corollary312UnusedTensor]
  calc
    2 * ((↑(Real.sqrt 2) : ℂ)⁻¹ * ((↑(Real.sqrt 2) : ℂ)⁻¹ * X 0 0)) =
        2 * (((↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹) * X 0 0) := by ring
    _ = X 0 0 := by rw [invSqrtTwo_mul_self]; ring

private theorem corollary312Tensor_isNormalTensor :
    IsNormalTensor corollary312Tensor :=
  isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    corollary312Tensor corollary312Tensor_transferMap

private theorem corollary312UnusedTensor_isNormalTensor :
    IsNormalTensor corollary312UnusedTensor :=
  isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    corollary312UnusedTensor corollary312UnusedTensor_transferMap

/-- Both members of the counterexample BNT have bond dimension one. -/
@[reducible] def corollary312BondDim : Fin 2 → ℕ := fun _ => 1

/-- The candidate BNT consisting of the active tensor and the unused tensor. -/
noncomputable def corollary312CandidateFamily :
    (j : Fin 2) → MPSTensor 2 (corollary312BondDim j)
  | 0 => corollary312Tensor
  | 1 => corollary312UnusedTensor

private lemma corollary312Tensor_mpv_zero (N : ℕ) :
    mpv corollary312Tensor (fun _ : Fin N => (0 : Fin 2)) = 1 := by
  rw [mpv_const_eq_trace_pow]
  simp [corollary312Tensor, Matrix.trace]

private lemma corollary312Tensor_mpv_one (N : ℕ) (hN : 0 < N) :
    mpv corollary312Tensor (fun _ : Fin N => (1 : Fin 2)) = 0 := by
  rw [mpv_const_eq_trace_pow]
  simp [corollary312Tensor, Matrix.trace, Nat.ne_of_gt hN]

private lemma corollary312UnusedTensor_mpv_const (a : Fin 2) (N : ℕ) :
    mpv corollary312UnusedTensor (fun _ : Fin N => a) =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ N := by
  rw [mpv_const_eq_trace_pow]
  change Matrix.trace
    ((((Real.sqrt 2 : ℂ)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ N) = _
  rw [smul_pow]
  simp [Matrix.trace]

private lemma corollary312CandidateFamily_linearIndependent
    (N : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ (fun j : Fin 2 => mpvState (corollary312CandidateFamily j) N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum j
  have hsqrt : ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))))
  fin_cases j
  · have hone := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (1 : Fin 2))) hsum
    have hc1 : c (1 : Fin 2) = 0 := by
      simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, mpvState_apply,
        smul_eq_mul, corollary312CandidateFamily,
        corollary312Tensor_mpv_one N hN,
        corollary312UnusedTensor_mpv_const 1 N,
        mul_zero, zero_add, PiLp.zero_apply] at hone
      exact (mul_eq_zero.mp hone).resolve_right (pow_ne_zero N hsqrt)
    have hzero := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (0 : Fin 2))) hsum
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, mpvState_apply,
      smul_eq_mul, corollary312CandidateFamily,
      corollary312Tensor_mpv_zero N,
      corollary312UnusedTensor_mpv_const 0 N,
      mul_one, hc1, zero_mul, add_zero, PiLp.zero_apply] at hzero
    exact hzero
  · have hone := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (1 : Fin 2))) hsum
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, mpvState_apply,
      smul_eq_mul, corollary312CandidateFamily,
      corollary312Tensor_mpv_one N hN,
      corollary312UnusedTensor_mpv_const 1 N,
      mul_zero, zero_add, PiLp.zero_apply] at hone
    exact (mul_eq_zero.mp hone).resolve_right (pow_ne_zero N hsqrt)

private theorem corollary312Tensor_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors corollary312Tensor
      (fun j => ⟨corollary312BondDim j, corollary312CandidateFamily j⟩) := by
  refine {
    blocks_normal := ?_
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro j
    fin_cases j
    · exact corollary312Tensor_isNormalTensor
    · exact corollary312UnusedTensor_isNormalTensor
  · intro N _hN
    refine ⟨fun j => if j = 0 then 1 else 0, ?_⟩
    intro σ
    simp [corollary312CandidateFamily]
  · exact ⟨0, fun N hN => corollary312CandidateFamily_linearIndependent N (by omega)⟩

private theorem corollary312Tensor_isCPSVCanonicalForm :
    IsCPSVCanonicalForm corollary312Tensor := by
  have hEq : toTensorFromBlocks (d := 2) (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => corollary312Tensor) = corollary312Tensor := by
    ext i x y
    have hcard : (∑ _ : Fin 1, 1) = 1 := by simp
    have hx := x.isLt
    have hy := y.isLt
    have hx0 : x.val = 0 := by omega
    have hy0 : y.val = 0 := by omega
    have hxy : x = y := Fin.ext (hx0.trans hy0.symm)
    subst y
    simp only [toTensorFromBlocks, Matrix.reindex_apply]
    change Matrix.blockDiagonal' (fun k : Fin 1 => (1 : ℂ) • corollary312Tensor i)
      (finSigmaFinEquiv.symm x) (finSigmaFinEquiv.symm x) = corollary312Tensor i x x
    rcases h : finSigmaFinEquiv.symm x with ⟨k, z⟩
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases hi : i = 0
    · simp only [corollary312Tensor, hi, ↓reduceIte]
      simp only [Matrix.smul_apply, Matrix.one_apply]
      have hxone : (1 : Matrix (Fin (∑ _ : Fin 1, 1))
          (Fin (∑ _ : Fin 1, 1)) ℂ) x x = 1 := by
        rw [Matrix.one_apply]
        simp
      calc
        (1 : ℂ) • (if True then 1 else 0) = 1 := by simp
        _ = (1 : Matrix (Fin (∑ _ : Fin 1, 1))
          (Fin (∑ _ : Fin 1, 1)) ℂ) x x := hxone.symm
    · simp only [corollary312Tensor, hi, ↓reduceIte]
      have hzzero : ((1 : ℂ) • (0 : Matrix (Fin 1) (Fin 1) ℂ)) z z = 0 := by
        simp
      have hxzero : (0 : Matrix (Fin (∑ _ : Fin 1, 1))
          (Fin (∑ _ : Fin 1, 1)) ℂ) x x = 0 := by
        rfl
      rw [hzzero]
      exact hxzero.symm

  rw [← hEq]
  exact (CPSVCanonicalFormData.ofBlocks
    (fun _ : Fin 1 => by simp) (fun _ => (1 : ℂ)) (fun _ => corollary312Tensor)
    (fun _ => corollary312Tensor_isNormalTensor)).isCPSVCanonicalForm

private theorem corollary312Tensor_isTransferIdempotent :
    IsTransferIdempotent corollary312Tensor := by
  rw [IsTransferIdempotent, corollary312Tensor_transferMap]
  rfl

private theorem corollary312CandidateFamily_not_residual :
    ¬ IsResidualIsometryFamily corollary312CandidateFamily := by
  intro h
  have hcross := h.2 (0 : Fin 2) (1 : Fin 2) (by decide)
    (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) (0 : Fin 1)
  simp [corollary312CandidateFamily, corollary312Tensor, corollary312UnusedTensor] at hcross

private theorem corollary312CandidateFamily_no_residual_decomposition :
    ¬ ∃ (X : (j : Fin 2) → Matrix (Fin 1) (Fin 1) ℂ)
      (Λ : (j : Fin 2) → Fin 1 → ℝ)
      (U : (j : Fin 2) → MPSTensor 2 1),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, corollary312CandidateFamily j i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) *
          U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  rintro ⟨X, Λ, U, hXdet, _hΛpos, hΛsum, hdecomp, hU⟩
  have hΛone : ∀ j : Fin 2, Λ j 0 = 1 := by
    intro j
    simpa using hΛsum j
  have hUeq : ∀ (j : Fin 2) (i : Fin 2),
      U j i 0 0 = corollary312CandidateFamily j i 0 0 := by
    intro j i
    have h := congrFun (congrFun (hdecomp j i) (0 : Fin 1)) (0 : Fin 1)
    simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, Matrix.diagonal_apply_eq] at h
    rw [hΛone] at h
    simp only [Real.sqrt_one, Complex.ofReal_one, mul_one] at h
    have hmul := Matrix.mul_nonsing_inv (X j)
      (isUnit_iff_ne_zero.mpr (hXdet j))
    have hxx := congrFun (congrFun hmul (0 : Fin 1)) (0 : Fin 1)
    simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, Matrix.one_apply, if_pos] at hxx
    calc
      U j i 0 0 = (X j 0 0 * (X j)⁻¹ 0 0) * U j i 0 0 := by rw [hxx, one_mul]
      _ = X j 0 0 * U j i 0 0 * (X j)⁻¹ 0 0 := by ring
      _ = corollary312CandidateFamily j i 0 0 := h.symm
  have hcross := hU.2 (0 : Fin 2) (1 : Fin 2) (by decide)
    (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) (0 : Fin 1)
  simp only [Fin.sum_univ_two, hUeq] at hcross
  simp [corollary312CandidateFamily, corollary312Tensor, corollary312UnusedTensor] at hcross


/-- A literal CPSV canonical-form renormalization fixed point can have an arbitrary
basis of normal tensors for which the joint residual-isometry conclusion is impossible.

This is the source-defect half of arXiv:1606.00608, Corollary 3.12 (lines 583--590;
proof line 1303).  The displayed coefficient function is `1` on the active member
`corollary312Tensor` and `0` on `corollary312UnusedTensor`.  Thus the second normal member
is genuinely unused, rather than merely contributing a redundant nonzero term.

The final negation is the bond-one specialization of the decomposition supplied by the
positive residual-isometry theorem: invertible gauges, positive trace-normalized weights,
and a joint residual family.  Trace normalization forces every bond-one weight to be `1`,
and scalar gauge conjugation cancels, so any such residual family would equal the displayed
family.  Its cross inner product is $1/\sqrt{2} \neq 0$, contradicting the off-diagonal
clause of `IsResidualIsometryFamily`. -/
theorem cpsvCorollary312_arbitraryBNT_counterexample :
    IsCPSVCanonicalForm corollary312Tensor ∧
    IsTransferIdempotent corollary312Tensor ∧
    (∀ j : Fin 2, IsTransferIdempotent (corollary312CandidateFamily j)) ∧
    IsCPSVBasisOfNormalTensors corollary312Tensor
      (fun j => ⟨corollary312BondDim j, corollary312CandidateFamily j⟩) ∧
    (∀ (N : ℕ) (σ : Fin N → Fin 2),
      mpv corollary312Tensor σ = ∑ j : Fin 2,
        (if j = 0 then 1 else 0) * mpv (corollary312CandidateFamily j) σ) ∧
    ¬ IsResidualIsometryFamily corollary312CandidateFamily ∧
    ¬ ∃ (X : (j : Fin 2) → Matrix (Fin 1) (Fin 1) ℂ)
      (Λ : (j : Fin 2) → Fin 1 → ℝ)
      (U : (j : Fin 2) → MPSTensor 2 1),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, corollary312CandidateFamily j i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) *
          U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  refine ⟨corollary312Tensor_isCPSVCanonicalForm,
    corollary312Tensor_isTransferIdempotent, ?_,
    corollary312Tensor_isCPSVBasisOfNormalTensors, ?_,
    corollary312CandidateFamily_not_residual,
    corollary312CandidateFamily_no_residual_decomposition⟩
  · intro j
    fin_cases j
    · change IsTransferIdempotent corollary312Tensor
      exact corollary312Tensor_isTransferIdempotent
    · change IsTransferIdempotent corollary312UnusedTensor
      rw [IsTransferIdempotent, corollary312UnusedTensor_transferMap]
      rfl
  · intro N σ
    simp [corollary312CandidateFamily]

end MPSTensor
