/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Boundary-word stripping for parent-Hamiltonian closure

Left-word annihilation forces a matrix to vanish: if every length-`k` word
product annihilates `Z` on the left and longer words span the full matrix
algebra, then `Z = 0`. This is the left-handed companion of the right-stripping
lemma that removes an unknown boundary matrix.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If every length-\(k\) word product annihilates \(Z\) on the left, and words of
some longer length \(n\) span the full matrix algebra, then \(Z = 0\). -/
theorem eq_zero_of_evalWord_mul_eq_zero_of_wordSpan_eq_top
    {A : MPSTensor d D} {k n : ℕ} {Z : Matrix (Fin D) (Fin D) ℂ}
    (htop : wordSpan A n = ⊤) (hkn : k ≤ n)
    (hzero : ∀ σ : Fin k → Fin d, evalWord A (List.ofFn σ) * Z = 0) :
    Z = 0 := by
  have hzero_span : ∀ M ∈ wordSpan A n, M * Z = 0 := by
    apply Submodule.span_induction
    · intro M hM
      rcases hM with ⟨σ, rfl⟩
      let w := List.ofFn σ
      have hdrop_len : (w.drop (n - k)).length = k := by
        rw [List.length_drop]
        have hwlen : w.length = n := by simp [w]
        omega
      let σk : Fin k → Fin d := fun i =>
        (w.drop (n - k)).get ⟨i.val, by simp [hdrop_len]⟩
      have hσk : List.ofFn σk = w.drop (n - k) := by
        simpa [σk, hdrop_len] using (List.ofFn_get (w.drop (n - k)))
      have hsuffix : evalWord A (w.drop (n - k)) * Z = 0 := by
        simpa [hσk] using hzero σk
      calc
        evalWord A w * Z =
            evalWord A (w.take (n - k) ++ w.drop (n - k)) * Z := by
          rw [List.take_append_drop (n - k) w]
        _ = (evalWord A (w.take (n - k)) *
              evalWord A (w.drop (n - k))) * Z := by
          rw [evalWord_append]
        _ = evalWord A (w.take (n - k)) *
              (evalWord A (w.drop (n - k)) * Z) := by
          rw [Matrix.mul_assoc]
        _ = 0 := by rw [hsuffix, mul_zero]
    · simp
    · intro M₁ M₂ _ _ h₁ h₂
      simp [Matrix.add_mul, h₁, h₂]
    · intro c M _ hM
      simp [hM]
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) * Z = 0 :=
    hzero_span 1 (htop ▸ Submodule.mem_top)
  simpa using h1

/-- Block-injective left-annihilation padding variant.

If \(A\) is \(L₀\)-block-injective, then a relation \(A^wZ=0\) for every word
\(w\) of length \(k\) already forces \(Z=0\) whenever \(k\) is bounded by a positive
multiple of \(L₀\). -/
theorem eq_zero_of_evalWord_mul_eq_zero_of_isNBlkInjective_of_le_mul
    {A : MPSTensor d D} {L₀ k q : ℕ} (hInj : IsNBlkInjective A L₀)
    (hq : 1 ≤ q) (hkq : k ≤ q * L₀) {Z : Matrix (Fin D) (Fin D) ℂ}
    (hzero : ∀ σ : Fin k → Fin d, evalWord A (List.ofFn σ) * Z = 0) :
    Z = 0 := by
  exact eq_zero_of_evalWord_mul_eq_zero_of_wordSpan_eq_top
    (A := A) (k := k) (n := q * L₀)
    (wordSpan_top_of_mul A ((wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj) q hq)
    hkq hzero

end MPSTensor
