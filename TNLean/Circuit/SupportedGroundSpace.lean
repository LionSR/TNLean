/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedFunctionalCalculus
import TNLean.Circuit.Channel.Layer
import QICLean.Algebra.HermitianHelpers
import QICLean.Analysis.TraceCFC

/-!
# Simultaneous regional ground vectors on disjoint supports

The ground spectral cutoff of a supported Hermitian operator is supported
on the same region. Its trace is nonzero. Factorization of the trace for
operators on disjoint regions then proves that the product of the regional
ground cutoffs is nonzero, so its range contains a common ground vector.
No common ground vector is assumed.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the normalization argument
preceding Theorem 6.1.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero d]

/-- A supported Hermitian operator has a supported ground spectral cutoff
of nonzero trace, killed by subtraction of its actual minimum eigenvalue.
Source: AKLV, arXiv:1301.1162v1, Section 6.1 normalization. -/
theorem exists_supported_ground_cutoff {S : Set ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A.IsHermitian)
    (hs : A ∈ supportedOperators d S) :
    ∃ P : Matrix (ι → Fin d) (ι → Fin d) ℂ,
      P ∈ supportedOperators d S ∧ Matrix.trace P ≠ 0 ∧
      (A - (minEigenvalue hA : ℂ) • 1) * P = 0 := by
  classical
  let λ := minEigenvalue hA
  let f : ℝ → ℝ := fun x => if x = λ then 1 else 0
  let P := cfc f A
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn g
  have hshift : cfc (fun x : ℝ => x - λ) A = A - (λ : ℂ) • 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => λ) A (hc _) (hc _),
      cfc_id' ℝ A hA.isSelfAdjoint, cfc_const λ A hA.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have hkill : (A - (λ : ℂ) • 1) * P = 0 := by
    rw [← hshift, P, ← cfc_mul _ _ A (hc _) (hc _)]
    have hfun : (fun x : ℝ => (x - λ) * f x) = fun _ => 0 := by
      funext x
      by_cases hx : x = λ <;> simp [f, hx]
    rw [hfun, cfc_const_zero]
  let T := Finset.univ.filter fun i => hA.eigenvalues i = λ
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hA
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have htrace : Matrix.trace P = (T.card : ℂ) := by
    simp [P, hA.cfc_eq, hA.trace_cfc_eq_sum, f, T, ← Finset.sum_filter]
  refine ⟨P, cfc_mem_supportedOperators f hs, ?_, hkill⟩
  rw [htrace]
  exact_mod_cast Finset.card_ne_zero.mpr hT

/-- On disjoint regions, nonzero traces force a nonzero trace of the product.
Source context: AKLV, Section 6.1, tensor product of regional ground states. -/
theorem trace_mul_ne_zero_of_disjoint {S T : Set ι} (hST : Disjoint S T)
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators d T)
    (htrA : Matrix.trace A ≠ 0) (htrB : Matrix.trace B ≠ 0) :
    Matrix.trace (A * B) ≠ 0 := by
  have hfactor := trace_rectKronecker_mul_mul hST
    (fun _ : ι => (1 : Matrix (Fin d) (Fin d) ℂ)) hA hB
  rw [rectKronecker_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at hfactor
  intro hzero
  rw [hzero, zero_mul] at hfactor
  exact mul_ne_zero htrA htrB hfactor.symm

/-- Three Hermitian operators on disjoint regions have a nonzero common
minimum-energy vector. Their individual minimum eigenvalues are derived.
Source: AKLV, arXiv:1301.1162v1, Section 6.1. -/
theorem exists_common_ground_of_disjoint
    {S T R : Set ι} (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    {A B C : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hsA : A ∈ supportedOperators d S) (hsB : B ∈ supportedOperators d T)
    (hsC : C ∈ supportedOperators d R) :
    ∃ v : (ι → Fin d) → ℂ, v ≠ 0 ∧
      (A - (minEigenvalue hA : ℂ) • 1) *ᵥ v = 0 ∧
      (B - (minEigenvalue hB : ℂ) • 1) *ᵥ v = 0 ∧
      (C - (minEigenvalue hC : ℂ) • 1) *ᵥ v = 0 := by
  classical
  obtain ⟨P, hsP, hP, hAP⟩ := exists_supported_ground_cutoff hA hsA
  obtain ⟨Q, hsQ, hQ, hBQ⟩ := exists_supported_ground_cutoff hB hsB
  obtain ⟨W, hsW, hW, hCW⟩ := exists_supported_ground_cutoff hC hsC
  have hsPQ : P * Q ∈ supportedOperators d (S ∪ T) :=
    mul_mem_supportedOperators (supportedOperators_mono Set.subset_union_left hsP)
      (supportedOperators_mono Set.subset_union_right hsQ)
  have hPQ := trace_mul_ne_zero_of_disjoint hST hsP hsQ hP hQ
  have hPQW := trace_mul_ne_zero_of_disjoint (Set.disjoint_union_left.mpr ⟨hSR, hTR⟩)
    hsPQ hsW hPQ hW
  have hnonzero : P * Q * W ≠ 0 := by
    intro hzero
    exact hPQW (by rw [hzero, Matrix.trace_zero])
  have hBP : Commute (B - (minEigenvalue hB : ℂ) • 1) P :=
    (commute_of_mem_supportedOperators hST.symm hsB hsP).sub_left
      ((Commute.one_left P).smul_left _)
  have hCP : Commute (C - (minEigenvalue hC : ℂ) • 1) P :=
    (commute_of_mem_supportedOperators hSR.symm hsC hsP).sub_left
      ((Commute.one_left P).smul_left _)
  have hCQ : Commute (C - (minEigenvalue hC : ℂ) • 1) Q :=
    (commute_of_mem_supportedOperators hTR.symm hsC hsQ).sub_left
      ((Commute.one_left Q).smul_left _)
  have hkillA : (A - (minEigenvalue hA : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAP, Matrix.zero_mul, Matrix.zero_mul]
  have hkillB : (B - (minEigenvalue hB : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBP.eq, Matrix.mul_assoc,
      hBQ, Matrix.mul_zero, Matrix.zero_mul]
  have hkillC : (C - (minEigenvalue hC : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCP.eq, Matrix.mul_assoc,
      hCQ.eq, Matrix.mul_assoc, Matrix.mul_assoc, hCW, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hnonzero
  obtain ⟨y, hxy⟩ := Function.ne_iff.mp hx
  refine ⟨(P * Q * W).col y, ?_, ?_, ?_, ?_⟩
  · intro hz
    exact hxy (congrFun hz x)
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillA]
    rfl
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillB]
    rfl
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillC]
    rfl

end QuantumCircuit
