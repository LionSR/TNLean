/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.InvertibleWordSpan

/-!
# Word-span dimensions for a channel root

An invertible matrix in the exact length-\(p-1\) word span embeds the
one-letter Kraus span into the length-\(p\) word span by multiplication.
This is a sufficient condition relevant to the reverse implication of
arXiv:1708.00029, Theorem 4.1; it is not asserted for arbitrary channel roots.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- If the length-\(p-1\) word span contains an invertible matrix, then the
length-\(p\) word span has dimension at least the one-letter Kraus span.
Source context: arXiv:1708.00029, Theorem 4.1, converse, lines 812--818. -/
theorem wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_pred
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) {p : ℕ} (hp : 0 < p)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A (p - 1))
    (hUnit : IsUnit X) :
    Module.finrank ℂ (wordSpan A 1) ≤ Module.finrank ℂ (wordSpan A p) := by
  have hMul : Submodule.map (LinearMap.mulLeft ℂ X) (wordSpan A 1) ≤
      wordSpan A p := by
    intro Y hY
    obtain ⟨Z, hZ, rfl⟩ := Submodule.mem_map.mp hY
    change X * Z ∈ wordSpan A p
    have hprod : X * Z ∈ wordSpan A ((p - 1) + 1) := by
      rw [wordSpan_add]
      exact Submodule.mul_mem_mul hX hZ
    simpa [Nat.sub_add_cancel hp] using hprod
  have hinj : Function.Injective (LinearMap.mulLeft ℂ X) := by
    intro Y Z hYZ
    exact hUnit.mul_right_injective (by simpa only [LinearMap.mulLeft_apply] using hYZ)
  have hdim : Module.finrank ℂ (wordSpan A 1) =
      Module.finrank ℂ (Submodule.map (LinearMap.mulLeft ℂ X) (wordSpan A 1)) := by
    let e := Submodule.equivMapOfInjective (LinearMap.mulLeft ℂ X) hinj (wordSpan A 1)
    exact LinearEquiv.finrank_eq e
  exact hdim.le.trans (Submodule.finrank_mono hMul)

/-- An invertible element of the one-letter Kraus span supplies the
length-\(p-1\) invertible element needed above, for every positive \(p\).
Source context: arXiv:1708.00029, Theorem 4.1, converse, lines 812--818. -/
theorem wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_one
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) {p : ℕ} (hp : 0 < p)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1)
    (hUnit : IsUnit X) :
    Module.finrank ℂ (wordSpan A 1) ≤ Module.finrank ℂ (wordSpan A p) := by
  have hpow : ∀ n : ℕ, X ^ n ∈ wordSpan A n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, wordSpan_zero]
        exact Submodule.subset_span (Set.mem_singleton (1 : Matrix (Fin D) (Fin D) ℂ))
    | succ n ih =>
        rw [pow_succ, wordSpan_add]
        exact Submodule.mul_mem_mul ih hX
  exact wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_pred A hp
    (hpow (p - 1)) (hUnit.pow _)

end Kraus
