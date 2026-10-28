/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Periodic

/-!
# Same word traces, no gauge

The tensors `B' = (E₁₁, E₂₂)` and `B = (E₁₁ + E₁₂, E₂₂)` on `ℂ²` (lecture note AsymmetricFT,
Example 4.5; milestone V, V3.5) have the same trace on every word, `1` on a nonempty word that
uses one letter only and `0` on a word that uses both, but they are not gauge equivalent: the
letters of `B'` commute and those of `B` do not, `B¹B² - B²B¹ = E₁₂`. The only line invariant
under both letters of `B` is `ℂ e₁`, while `B'` has the two invariant lines `ℂ e₁` and `ℂ e₂`.

## Main results

* `MultiBlockExamples.NoGauge.V3_5a_trace_eq`, `V3_5a_trace_single`, `V3_5a_trace_mixed`.
* `MultiBlockExamples.NoGauge.V3_5b`: the commutators.
* `MultiBlockExamples.NoGauge.V3_5c_B`, `V3_5c_B'`: the invariant lines.
* `MultiBlockExamples.NoGauge.V3_5d`: no gauge transformation.

## References

Lecture note AsymmetricFT, Example 4.5; milestone V, V3.5.
-/

open scoped Matrix

namespace MultiBlockExamples

namespace NoGauge

/-- `B' = (E₁₁, E₂₂)` (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5). -/
noncomputable def tensorB' : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![E 0 0, E 1 1]

/-- `B = (E₁₁ + E₁₂, E₂₂)` (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5). -/
noncomputable def tensorB : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![E 0 0 + E 0 1, E 1 1]

/-- A word of `B'` is the diagonal matrix with `1` at `k` when every letter is `k`. -/
theorem evalWord_tensorB' (w : List (Fin 2)) :
    Kraus.evalWord tensorB' w = Matrix.diagonal fun k => if ∀ a ∈ w, a = k then 1 else 0 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [Kraus.evalWord_cons, ih]
    have ha : tensorB' a = Matrix.diagonal fun k => if a = k then 1 else 0 := by
      ext i j
      fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [tensorB']
    rw [ha, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [ite_zero_mul_ite_zero, mul_one]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- A word of `B` is upper triangular with the diagonal of the word of `B'`. -/
theorem evalWord_tensorB_apply (w : List (Fin 2)) :
    Kraus.evalWord tensorB w 1 0 = 0 ∧
      Kraus.evalWord tensorB w 0 0 = Kraus.evalWord tensorB' w 0 0 ∧
      Kraus.evalWord tensorB w 1 1 = Kraus.evalWord tensorB' w 1 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨h10, h00, h11⟩ := ih
    have h'01 : Kraus.evalWord tensorB' w 0 1 = 0 := by rw [evalWord_tensorB']; simp
    have h'10 : Kraus.evalWord tensorB' w 1 0 = 0 := by rw [evalWord_tensorB']; simp
    have hB0 : tensorB 0 = !![1, 1; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tensorB]
    have hB1 : tensorB 1 = !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tensorB]
    have hB'0 : tensorB' 0 = !![1, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tensorB']
    have hB'1 : tensorB' 1 = !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tensorB']
    simp only [Kraus.evalWord_cons, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, hB0, hB'0]
      simp [h10, h00, h11, h'01, h'10]
    · simp only [Fin.mk_one, Fin.isValue, hB1, hB'1]
      simp [h10, h00, h11, h'01, h'10]

/-- **V3.5(a)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(a)): `tr B^w = tr B'^w`
for every word. -/
theorem V3_5a_trace_eq (w : List (Fin 2)) :
    (Kraus.evalWord tensorB w).trace = (Kraus.evalWord tensorB' w).trace := by
  obtain ⟨-, h00, h11⟩ := evalWord_tensorB_apply w
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, h00, h11]

/-- **V3.5(a)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(a)): a nonempty word
using a single letter has trace `1`. -/
theorem V3_5a_trace_single (w : List (Fin 2)) (hw : w ≠ [])
    (h : ∃ i, w = List.replicate w.length i) : (Kraus.evalWord tensorB' w).trace = 1 := by
  obtain ⟨i, hi⟩ := h
  have hall : ∀ a ∈ w, a = i := (List.eq_replicate_iff.1 hi).2
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w hw
  have hother : ¬ ∀ a ∈ w, a = i + 1 := fun h' => by
    have := (hall a ha).symm.trans (h' a ha)
    fin_cases i <;> simp at this
  rw [evalWord_tensorB', Matrix.trace_diagonal, Fin.sum_univ_two]
  fin_cases i
  · have h0 : ∀ a ∈ w, a = 0 := by simpa using hall
    have h1 : ¬ ∀ a ∈ w, a = 1 := by simpa using hother
    simp only [eq_true h0, eq_false h1, ite_true, ite_false]
    norm_num
  · have h1 : ∀ a ∈ w, a = 1 := by simpa using hall
    have h0 : ¬ ∀ a ∈ w, a = 0 := fun h0 => by
      have := (h0 a ha).symm.trans (h1 a ha)
      simp at this
    simp only [eq_true h1, eq_false h0, ite_true, ite_false]
    norm_num

/-- **V3.5(a)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(a)): a word using both
letters has trace `0`. -/
theorem V3_5a_trace_mixed (w : List (Fin 2)) (h : ¬ ∃ i, w = List.replicate w.length i) :
    (Kraus.evalWord tensorB' w).trace = 0 := by
  have hk : ∀ k, ¬ ∀ a ∈ w, a = k := fun k hk =>
    h ⟨k, List.eq_replicate_iff.2 ⟨rfl, hk⟩⟩
  rw [evalWord_tensorB', Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [hk]

/-- **V3.5(b)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(b)): `B²B¹ = 0`,
`B¹B² - B²B¹ = E₁₂`, and the letters of `B'` commute. -/
theorem V3_5b : tensorB 1 * tensorB 0 = 0 ∧ tensorB 0 * tensorB 1 - tensorB 1 * tensorB 0 = E 0 1 ∧
    tensorB' 0 * tensorB' 1 = tensorB' 1 * tensorB' 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tensorB, tensorB', Matrix.mul_apply, Fin.sum_univ_two]

/-- **V3.5(c)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(c)): the only line
invariant under both letters of `B` is `ℂ e₁`. -/
theorem V3_5c_B (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {v}) ↔
      Submodule.span ℂ {v} = Submodule.span ℂ {e 0} := by
  rw [isInvariantSubmodule_span_singleton_iff]
  constructor
  · intro h
    obtain ⟨c₀, h₀⟩ := h 0
    obtain ⟨c₁, h₁⟩ := h 1
    have a0 : v 0 + v 1 = c₀ * v 0 := by
      simpa [tensorB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₀ 0
    have a1 : 0 = c₀ * v 1 := by
      simpa [tensorB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₀ 1
    have b0 : 0 = c₁ * v 0 := by
      simpa [tensorB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₁ 0
    have b1 : v 1 = c₁ * v 1 := by
      simpa [tensorB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₁ 1
    have hv1 : v 1 = 0 := by
      by_contra hv1
      have hc₀ : c₀ = 0 := (mul_eq_zero.1 a1.symm).resolve_right hv1
      have hv0 : v 0 ≠ 0 := fun h0 => hv1 (by rw [hc₀, h0] at a0; simpa using a0)
      have hc₁ : c₁ = 0 := (mul_eq_zero.1 b0.symm).resolve_right hv0
      exact hv1 (by rw [hc₁, zero_mul] at b1; exact b1)
    have hv0 : v 0 ≠ 0 := fun h0 => hv (by ext i; fin_cases i <;> simp [h0, hv1])
    refine span_singleton_eq_of_eq_smul hv0 ?_
    ext i; fin_cases i <;> simp [hv1]
  · intro h i
    obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
    have hv1 : v 1 = 0 := by simpa using congrFun hc 1
    fin_cases i
    · exact ⟨1, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct, hv1]⟩
    · exact ⟨0, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct, hv1]⟩

/-- **V3.5(c)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(c)): the lines
invariant under both letters of `B'` are `ℂ e₁` and `ℂ e₂`. -/
theorem V3_5c_B' (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Matrix.IsInvariantSubmodule tensorB' (Submodule.span ℂ {v}) ↔
      Submodule.span ℂ {v} = Submodule.span ℂ {e 0} ∨
        Submodule.span ℂ {v} = Submodule.span ℂ {e 1} := by
  rw [isInvariantSubmodule_span_singleton_iff]
  constructor
  · intro h
    obtain ⟨c₀, h₀⟩ := h 0
    have a0 : v 0 = c₀ * v 0 := by
      simpa [tensorB', Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₀ 0
    have a1 : 0 = c₀ * v 1 := by
      simpa [tensorB', Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h₀ 1
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [hv0, h1])
      refine Or.inr (span_singleton_eq_of_eq_smul hv1 ?_)
      ext i; fin_cases i <;> simp [hv0]
    · have hc : c₀ = 1 := by
        have h' : (c₀ - 1) * v 0 = 0 := by linear_combination -a0
        exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv0)
      have hv1 : v 1 = 0 := by rw [hc, one_mul] at a1; exact a1.symm
      refine Or.inl (span_singleton_eq_of_eq_smul hv0 ?_)
      ext i; fin_cases i <;> simp [hv1]
  · rintro (h | h) i
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
      have hv1 : v 1 = 0 := by simpa using congrFun hc 1
      fin_cases i
      · exact ⟨1, by ext j; fin_cases j <;> simp [tensorB', Matrix.mulVec, dotProduct, hv1]⟩
      · exact ⟨0, by ext j; fin_cases j <;> simp [tensorB', Matrix.mulVec, dotProduct, hv1]⟩
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
      have hv0 : v 0 = 0 := by simpa using congrFun hc 0
      fin_cases i
      · exact ⟨0, by ext j; fin_cases j <;> simp [tensorB', Matrix.mulVec, dotProduct, hv0]⟩
      · exact ⟨1, by ext j; fin_cases j <;> simp [tensorB', Matrix.mulVec, dotProduct, hv0]⟩

/-- **V3.5(d)** (lecture note AsymmetricFT, Example 4.5; milestone V, V3.5(d)): there is no
invertible `X` with `X Bⁱ X⁻¹ = B'ⁱ`, since the letters of `B'` commute and those of `B` do
not. -/
theorem V3_5d : ¬ ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ, X * Y = 1 ∧ Y * X = 1 ∧
    ∀ i, X * tensorB i * Y = tensorB' i := by
  rintro ⟨X, Y, hXY, hYX, h⟩
  have hB : ∀ i, tensorB i = Y * tensorB' i * X := fun i => by
    calc tensorB i = (Y * X) * tensorB i * (Y * X) := by rw [hYX, Matrix.one_mul, Matrix.mul_one]
      _ = Y * (X * tensorB i * Y) * X := by simp only [Matrix.mul_assoc]
      _ = Y * tensorB' i * X := by rw [h i]
  have hcomm : tensorB 0 * tensorB 1 = tensorB 1 * tensorB 0 := by
    rw [hB 0, hB 1]
    calc Y * tensorB' 0 * X * (Y * tensorB' 1 * X)
        = Y * tensorB' 0 * (X * Y) * tensorB' 1 * X := by simp only [Matrix.mul_assoc]
      _ = Y * (tensorB' 0 * tensorB' 1) * X := by
          rw [hXY, Matrix.mul_one, Matrix.mul_assoc Y]
      _ = Y * (tensorB' 1 * tensorB' 0) * X := by rw [V3_5b.2.2]
      _ = Y * tensorB' 1 * (X * Y) * tensorB' 0 * X := by
          rw [hXY, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Y * tensorB' 1 * X * (Y * tensorB' 0 * X) := by simp only [Matrix.mul_assoc]
  have h01 := V3_5b.2.1
  rw [hcomm, sub_self] at h01
  have := congrFun (congrFun h01 0) 1
  simp at this

end NoGauge

end MultiBlockExamples
