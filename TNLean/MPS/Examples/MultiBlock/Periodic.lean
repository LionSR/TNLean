/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixFamilyAction
import QICLean.Kraus.Injectivity

/-!
# The periodic tensor: irreducible but not normal

The tensor `C = (E₁₂, E₂₁)` on `ℂ²` (*The asymmetric fundamental theorem of matrix product states*,
equation (1.1)) has no common invariant subspace other than `0` and `ℂ²`, so it is irreducible, but
it is not normal: for every length `ℓ ≥ 1` the words of length `ℓ` span a two-dimensional subspace
of `M₂(ℂ)`, the diagonal matrices for `ℓ` even and the off-diagonal ones for `ℓ` odd. It separates
the irreducible tensors from the normal ones.

## Main results

* `MultiBlockExamples.Periodic.isIrreducibleAction_tensorC`: `C` is irreducible.
* `MultiBlockExamples.Periodic.not_isNormal_tensorC`: `C` is not normal.
* `MultiBlockExamples.Periodic.finrank_wordSpan_tensorC`,
  `MultiBlockExamples.Periodic.wordSpan_tensorC_of_even`,
  `MultiBlockExamples.Periodic.wordSpan_tensorC_of_odd`: the words of length `ℓ ≥ 1`.

## References

*The asymmetric fundamental theorem of matrix product states*, equation (1.1).
-/

open scoped Matrix

namespace MultiBlockExamples

/-- The matrix unit `E_{ij}` (0-based indices). -/
noncomputable abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single i j 1

/-- The standard basis vector `e_j` (0-based). -/
noncomputable abbrev e {n : ℕ} (j : Fin n) : Fin n → ℂ := Pi.single j 1

/-- A line `ℂ v` is invariant under a family of matrices iff `v` is a common eigenvector. -/
theorem isInvariantSubmodule_span_singleton_iff {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    Matrix.IsInvariantSubmodule A (Submodule.span ℂ {v}) ↔ ∀ i, ∃ c : ℂ, A i *ᵥ v = c • v := by
  constructor
  · intro h i
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h i v (Submodule.mem_span_singleton_self v))
    exact ⟨c, hc.symm⟩
  · intro h i u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨c, hc⟩ := h i
    rw [Matrix.mulVec_smul, hc, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨a * c, rfl⟩

/-- Two vectors related by a nonzero scalar span the same line. -/
theorem span_singleton_eq_of_eq_smul {n : ℕ} {v u : Fin n → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : v = c • u) : Submodule.span ℂ {v} = Submodule.span ℂ {u} := by
  rw [h]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) u

/-- Equal lines: each spanning vector is a multiple of the other. -/
theorem exists_eq_smul_of_span_singleton_eq {n : ℕ} {v u : Fin n → ℂ}
    (h : Submodule.span ℂ {v} = Submodule.span ℂ {u}) : ∃ c : ℂ, v = c • u := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self v)
  exact ⟨c, hc.symm⟩

namespace Periodic

/-- **The periodic tensor** `C = (E₁₂, E₂₁)` (*The asymmetric fundamental theorem of matrix product
states*, equation (1.1)). -/
noncomputable def tensorC : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![E 0 1, E 1 0]

/-- The entry `(i, j)` of a word of length `ℓ` vanishes unless `i + j + ℓ` is even. -/
theorem evalWord_tensorC_apply_eq_zero (w : List (Fin 2)) (i j : Fin 2)
    (h : (i.val + j.val + w.length) % 2 = 1) : Kraus.evalWord tensorC w i j = 0 := by
  induction w generalizing i j with
  | nil =>
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  | cons a w ih =>
    rw [Kraus.evalWord_cons, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [List.length_cons] at h
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp only [tensorC, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.single_apply_same,
        Matrix.single_apply_of_ne, zero_ne_one, one_ne_zero, and_false, and_true, and_self,
        not_false_eq_true, zero_mul, one_mul, add_zero, zero_add, Nat.reduceAdd,
        Nat.add_mod_left] at h ⊢ <;>
      first
        | exact ih 0 0 (by simp; omega)
        | exact ih 0 1 (by simp; omega)
        | exact ih 1 0 (by simp; omega)
        | exact ih 1 1 (by simp; omega)

/-- A word of even length lies in the diagonal matrices. -/
theorem evalWord_tensorC_mem_of_even (w : List (Fin 2)) (h : w.length % 2 = 0) :
    Kraus.evalWord tensorC w ∈ Submodule.span ℂ {E 0 0, E 1 1} := by
  have hM : Kraus.evalWord tensorC w =
      Kraus.evalWord tensorC w 0 0 • E 0 0 + Kraus.evalWord tensorC w 1 1 • E 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.smul_single, smul_eq_mul, mul_one,
        Matrix.add_apply, Matrix.single_apply_same, Matrix.single_apply_of_ne, zero_ne_one,
        one_ne_zero, and_false, and_true, and_self, not_false_eq_true, add_zero, zero_add]
    · exact evalWord_tensorC_apply_eq_zero w 0 1 (by simp; omega)
    · exact evalWord_tensorC_apply_eq_zero w 1 0 (by simp; omega)
  rw [hM]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- A word of odd length lies in the off-diagonal matrices. -/
theorem evalWord_tensorC_mem_of_odd (w : List (Fin 2)) (h : w.length % 2 = 1) :
    Kraus.evalWord tensorC w ∈ Submodule.span ℂ {E 0 1, E 1 0} := by
  have hM : Kraus.evalWord tensorC w =
      Kraus.evalWord tensorC w 0 1 • E 0 1 + Kraus.evalWord tensorC w 1 0 • E 1 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.smul_single, smul_eq_mul, mul_one,
        Matrix.add_apply, Matrix.single_apply_same, Matrix.single_apply_of_ne, zero_ne_one,
        one_ne_zero, and_false, and_true, and_self, not_false_eq_true, add_zero, zero_add]
    · exact evalWord_tensorC_apply_eq_zero w 0 0 (by simp; omega)
    · exact evalWord_tensorC_apply_eq_zero w 1 1 (by simp; omega)
  rw [hM]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The word `a b a b ⋯ a b` with `m` blocks `a b`. -/
def altWord (a b : Fin 2) : ℕ → List (Fin 2)
  | 0 => []
  | m + 1 => a :: b :: altWord a b m

theorem length_altWord (a b : Fin 2) (m : ℕ) : (altWord a b m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [altWord, ih]; ring

theorem evalWord_altWord_zero_one (m : ℕ) :
    Kraus.evalWord tensorC (altWord 0 1 (m + 1)) = E 0 0 := by
  induction m with
  | zero => simp [altWord, tensorC, Matrix.single_mul_single_same]
  | succ m ih =>
    rw [altWord, Kraus.evalWord_cons, Kraus.evalWord_cons, ih]
    simp [tensorC, Matrix.single_mul_single_same]

theorem evalWord_altWord_one_zero (m : ℕ) :
    Kraus.evalWord tensorC (altWord 1 0 (m + 1)) = E 1 1 := by
  induction m with
  | zero => simp [altWord, tensorC, Matrix.single_mul_single_same]
  | succ m ih =>
    rw [altWord, Kraus.evalWord_cons, Kraus.evalWord_cons, ih]
    simp [tensorC, Matrix.single_mul_single_same]

theorem evalWord_cons_altWord_one_zero (m : ℕ) :
    Kraus.evalWord tensorC (0 :: altWord 1 0 m) = E 0 1 := by
  cases m with
  | zero => simp [altWord, tensorC]
  | succ m =>
    rw [Kraus.evalWord_cons, evalWord_altWord_one_zero]
    simp [tensorC, Matrix.single_mul_single_same]

theorem evalWord_cons_altWord_zero_one (m : ℕ) :
    Kraus.evalWord tensorC (1 :: altWord 0 1 m) = E 1 0 := by
  cases m with
  | zero => simp [altWord, tensorC]
  | succ m =>
    rw [Kraus.evalWord_cons, evalWord_altWord_zero_one]
    simp [tensorC, Matrix.single_mul_single_same]

/-- A word of length `ℓ` lies in the word span at `ℓ`. -/
theorem mem_wordSpan_of_length {ℓ : ℕ} (w : List (Fin 2)) (hw : w.length = ℓ) :
    Kraus.evalWord tensorC w ∈ Kraus.wordSpan tensorC ℓ :=
  hw ▸ Kraus.evalWord_mem_wordSpan tensorC w

/-- **Even lengths** (*The asymmetric fundamental theorem of matrix product states*, equation
(1.1)): for even `ℓ ≥ 1` the words of length `ℓ` span the diagonal matrices. -/
theorem wordSpan_tensorC_of_even {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (he : Even ℓ) :
    Kraus.wordSpan tensorC ℓ = Submodule.span ℂ {E 0 0, E 1 1} := by
  obtain ⟨m, rfl⟩ := he
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨σ, rfl⟩
    exact evalWord_tensorC_mem_of_even _ (by simp; omega)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← evalWord_altWord_zero_one m]
      exact mem_wordSpan_of_length _ (by rw [length_altWord]; ring)
    · rw [← evalWord_altWord_one_zero m]
      exact mem_wordSpan_of_length _ (by rw [length_altWord]; ring)

/-- **Odd lengths** (*The asymmetric fundamental theorem of matrix product states*, equation (1.1)):
for odd `ℓ` the words of length `ℓ` span the off-diagonal matrices. -/
theorem wordSpan_tensorC_of_odd {ℓ : ℕ} (ho : Odd ℓ) :
    Kraus.wordSpan tensorC ℓ = Submodule.span ℂ {E 0 1, E 1 0} := by
  obtain ⟨m, rfl⟩ := ho
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨σ, rfl⟩
    exact evalWord_tensorC_mem_of_odd _ (by simp)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← evalWord_cons_altWord_one_zero m]
      exact mem_wordSpan_of_length _ (by rw [List.length_cons, length_altWord])
    · rw [← evalWord_cons_altWord_zero_one m]
      exact mem_wordSpan_of_length _ (by rw [List.length_cons, length_altWord])

theorem finrank_span_pair {x y : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) :
    Module.finrank ℂ ↥(Submodule.span ℂ {x, y}) = 2 := by
  have hli : LinearIndependent ℂ ![x, y] := LinearIndependent.pair_iff.2 h
  have := finrank_span_eq_card hli
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this

/-- **The dimension** (*The asymmetric fundamental theorem of matrix product states*, equation
(1.1)): for every `ℓ ≥ 1` the words of length `ℓ` span a two-dimensional subspace of `M₂(ℂ)`. -/
theorem finrank_wordSpan_tensorC {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Module.finrank ℂ ↥(Kraus.wordSpan tensorC ℓ) = 2 := by
  rcases Nat.even_or_odd ℓ with he | ho
  · rw [wordSpan_tensorC_of_even hℓ he]
    refine finrank_span_pair fun s t hst => ?_
    have h0 := congrFun (congrFun hst 0) 0
    have h1 := congrFun (congrFun hst 1) 1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rw [wordSpan_tensorC_of_odd ho]
    refine finrank_span_pair fun s t hst => ?_
    have h0 := congrFun (congrFun hst 0) 1
    have h1 := congrFun (congrFun hst 1) 0
    exact ⟨by simpa using h0, by simpa using h1⟩

/-- **Not normal** (*The asymmetric fundamental theorem of matrix product states*, equation (1.1)):
no length `ℓ ≥ 1` has words spanning `M₂(ℂ)`. -/
theorem not_isNormal_tensorC : ¬ Kraus.IsNormal tensorC := by
  rintro ⟨N, hN, hinj⟩
  have h := finrank_wordSpan_tensorC (ℓ := N) hN
  rw [Kraus.IsNBlkInjective] at hinj
  rw [hinj, finrank_top, Module.finrank_matrix] at h
  simp at h

/-- **Irreducible** (*The asymmetric fundamental theorem of matrix product states*, equation (1.1)):
the only subspaces invariant under `E₁₂` and `E₂₁` are `0` and `ℂ²`. -/
theorem isIrreducibleAction_tensorC : Matrix.IsIrreducibleAction tensorC := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have h0 : tensorC 0 *ᵥ v = v 1 • e 0 := by
    ext i; fin_cases i <;> simp [tensorC, Matrix.mulVec, dotProduct, Matrix.single_apply]
  have h1 : tensorC 1 *ᵥ v = v 0 • e 1 := by
    ext i; fin_cases i <;> simp [tensorC, Matrix.mulVec, dotProduct, Matrix.single_apply]
  have he01 : tensorC 0 *ᵥ e 1 = e 0 := by
    ext i; fin_cases i <;> simp [tensorC, Matrix.mulVec, dotProduct, Matrix.single_apply]
  have he10 : tensorC 1 *ᵥ e 0 = e 1 := by
    ext i; fin_cases i <;> simp [tensorC, Matrix.mulVec, dotProduct, Matrix.single_apply]
  have hboth : e 0 ∈ W ∧ e 1 ∈ W := by
    by_cases hv1 : v 1 = 0
    · have hv0' : v 0 ≠ 0 := by
        intro h; apply hv0; ext i; fin_cases i <;> simp [h, hv1]
      have h1W : e 1 ∈ W := by
        have := W.smul_mem (v 0)⁻¹ (h1 ▸ hW 1 v hvW)
        rwa [smul_smul, inv_mul_cancel₀ hv0', one_smul] at this
      exact ⟨he01 ▸ hW 0 _ h1W, h1W⟩
    · have h0W : e 0 ∈ W := by
        have := W.smul_mem (v 1)⁻¹ (h0 ▸ hW 0 v hvW)
        rwa [smul_smul, inv_mul_cancel₀ hv1, one_smul] at this
      exact ⟨h0W, he10 ▸ hW 1 _ h0W⟩
  refine eq_top_iff.2 fun u _ => ?_
  have hu : u = u 0 • e 0 + u 1 • e 1 := by
    ext i; fin_cases i <;> simp
  rw [hu]
  exact W.add_mem (W.smul_mem _ hboth.1) (W.smul_mem _ hboth.2)

end Periodic

end MultiBlockExamples
