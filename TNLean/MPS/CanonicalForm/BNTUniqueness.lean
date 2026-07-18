/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization

/-!
# Uniqueness boundary for bases of normal tensors

This module examines the uniqueness sentence following the characterization of
a basis of normal tensors in arXiv:1606.00608, Appendix A, line 1148.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The bond-dimension-one tensor supported on one physical symbol. -/
private def symbolTensor (a : Fin 2) : MPSTensor 2 1 :=
  fun i => if i = a then 1 else 0

private lemma symbolTensor_isIrreducibleTensor (a : Fin 2) :
    IsIrreducibleTensor (symbolTensor a) := by
  rintro ⟨P, ⟨_, hIdem⟩, hP0, hP1, _⟩
  have h00 := congrFun (congrFun hIdem (0 : Fin 1)) (0 : Fin 1)
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton] at h00
  have hfactor : P 0 0 * (P 0 0 - 1) = 0 := by
    linear_combination h00
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · apply hP0
    ext x y
    fin_cases x
    fin_cases y
    simpa using hzero
  · apply hP1
    ext x y
    fin_cases x
    fin_cases y
    simpa using sub_eq_zero.mp hone

private lemma symbolTensor_transferMap (a : Fin 2) :
    transferMap (symbolTensor a) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext x y
  fin_cases x
  fin_cases y
  simp [transferMap_apply, symbolTensor]

private theorem symbolTensor_isNormalTensor (a : Fin 2) :
    IsNormalTensor (symbolTensor a) := by
  refine ⟨symbolTensor_isIrreducibleTensor a, ?_, ?_⟩
  · rw [symbolTensor_transferMap]
    change spectralRadius ℂ
      (1 : Matrix (Fin 1) (Fin 1) ℂ →L[ℂ] Matrix (Fin 1) (Fin 1) ℂ) = 1
    exact spectrum.spectralRadius_one
  · rw [symbolTensor_transferMap]
    apply isPrimitive_of_unique_norm_one LinearMap.id
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
    · rfl
    · exact one_ne_zero
    · intro μ hμ _hμnorm
      obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
      have hEq := hX.apply_eq_smul
      have hX00 : X 0 0 ≠ 0 := by
        intro hzero
        apply hX.2
        ext x y
        fin_cases x
        fin_cases y
        simpa using hzero
      have hEq00 := congrFun (congrFun hEq (0 : Fin 1)) (0 : Fin 1)
      simp only [LinearMap.id_apply, Matrix.smul_apply, smul_eq_mul] at hEq00
      apply mul_right_cancel₀ hX00
      simpa using hEq00.symm

private lemma symbolTensor_evalWord_self (a : Fin 2) (N : ℕ) :
    evalWord (symbolTensor a) (List.replicate N a) = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [List.replicate_succ, evalWord_cons, ih]
      simp [symbolTensor]

private lemma symbolTensor_evalWord_other {a b : Fin 2} (hab : a ≠ b) (N : ℕ) :
    evalWord (symbolTensor a) (List.replicate (N + 1) b) = 0 := by
  rw [List.replicate_succ, evalWord_cons]
  simp [symbolTensor, Ne.symm hab]

private lemma symbolTensor_mpv_self (a : Fin 2) (N : ℕ) :
    mpv (symbolTensor a) (fun _ : Fin N => a) = 1 := by
  rw [mpv_const_eq_trace_pow]
  simp [symbolTensor, Matrix.trace]

private lemma symbolTensor_mpv_other {a b : Fin 2} (hab : a ≠ b)
    (N : ℕ) (hN : 0 < N) :
    mpv (symbolTensor a) (fun _ : Fin N => b) = 0 := by
  rw [mpv_const_eq_trace_pow]
  simp [symbolTensor, Ne.symm hab, Matrix.trace, Nat.ne_of_gt hN]

private lemma symbolTensor_pair_linearIndependent (N : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ (fun j : Fin 2 => mpvState (symbolTensor j) N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum j
  fin_cases j
  · have hzero := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (0 : Fin 2))) hsum
    have h00 : mpv (symbolTensor 0) (fun _ : Fin N => (0 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 0 N
    have h10 : mpv (symbolTensor 1) (fun _ : Fin N => (0 : Fin 2)) = 0 :=
      symbolTensor_mpv_other (by decide) N hN
    have hc0 : c (0 : Fin 2) = 0 := by
      simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
        mpvState_apply, smul_eq_mul, h00, h10, mul_one, mul_zero, add_zero,
        PiLp.zero_apply] using hzero
    simpa using hc0
  · have hone := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (1 : Fin 2))) hsum
    have h01 : mpv (symbolTensor 0) (fun _ : Fin N => (1 : Fin 2)) = 0 :=
      symbolTensor_mpv_other (by decide) N hN
    have h11 : mpv (symbolTensor 1) (fun _ : Fin N => (1 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 1 N
    have hc1 : c (1 : Fin 2) = 0 := by
      simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
        mpvState_apply, smul_eq_mul, h01, h11, mul_zero, mul_one, zero_add,
        PiLp.zero_apply] using hone
    simpa using hc1

private def singletonSymbolFamily : Fin 1 → Σ D : ℕ, MPSTensor 2 D :=
  fun _ => ⟨1, symbolTensor 0⟩

private def pairSymbolFamily : Fin 2 → Σ D : ℕ, MPSTensor 2 D :=
  fun j => ⟨1, symbolTensor j⟩

private theorem singletonSymbolFamily_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors (symbolTensor 0) singletonSymbolFamily := by
  refine {
    blocks_normal := fun _ => symbolTensor_isNormalTensor 0
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N _hN
    refine ⟨fun _ => 1, ?_⟩
    intro σ
    simp [singletonSymbolFamily]
  · refine ⟨0, ?_⟩
    intro N hN
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hzero
    have hcomponent := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (0 : Fin 2))) hzero
    have hself : mpv (symbolTensor 0) (fun _ : Fin N => (0 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 0 N
    have hone : (1 : ℂ) = 0 := by
      simpa only [singletonSymbolFamily, mpvState_apply, hself, PiLp.zero_apply]
        using hcomponent
    exact one_ne_zero hone

private theorem pairSymbolFamily_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors (symbolTensor 0) pairSymbolFamily := by
  refine {
    blocks_normal := fun j => symbolTensor_isNormalTensor j
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N _hN
    refine ⟨fun j => if j = 0 then 1 else 0, ?_⟩
    intro σ
    simp [pairSymbolFamily]
  · refine ⟨0, ?_⟩
    intro N hN
    exact symbolTensor_pair_linearIndependent N (by omega)

/-- Two bases of normal tensors for one fixed canonical-form family need not
have equivalent index types under the literal definition of arXiv:1606.00608.

This is a counterexample to the unrestricted uniqueness sentence in
arXiv:1606.00608, Appendix A, line 1148. Take the bond-dimension-one tensor
supported on physical symbol zero. Its singleton family is a basis of normal
tensors. Adjoining the tensor supported on physical symbol one gives a second
basis: its coefficient is identically zero, while the two matrix product
vectors are orthogonal and hence linearly independent at every positive
length. The two index types have cardinalities one and two.

See `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`. -/
theorem exists_isCPSVBasisOfNormalTensors_unequal_card :
    ∃ (A : MPSTensor 2 1)
      (basis₁ : Fin 1 → Σ D : ℕ, MPSTensor 2 D)
      (basis₂ : Fin 2 → Σ D : ℕ, MPSTensor 2 D),
      IsNormalTensor A ∧
      SameMPV₂Pos A
        (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) ∧
      IsCPSVBasisOfNormalTensors A basis₁ ∧
      IsCPSVBasisOfNormalTensors A basis₂ ∧
      Fintype.card (Fin 1) ≠ Fintype.card (Fin 2) ∧
      ¬ Nonempty (Fin 1 ≃ Fin 2) := by
  refine ⟨symbolTensor 0, singletonSymbolFamily, pairSymbolFamily,
    symbolTensor_isNormalTensor 0, ?_,
    singletonSymbolFamily_isCPSVBasisOfNormalTensors,
    pairSymbolFamily_isCPSVBasisOfNormalTensors, ?_, ?_⟩
  · intro N _hN σ
    rw [mpv_toTensorFromBlocks_eq_sum]
    simp
  · norm_num
  · rintro ⟨e⟩
    have hcard := Fintype.card_congr e
    norm_num at hcard

end MPSTensor
