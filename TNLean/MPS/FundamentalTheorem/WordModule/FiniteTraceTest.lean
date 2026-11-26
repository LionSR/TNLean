/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.TracePairing
import QICLean.Algebra.Module.FinSpanOfFinrank

/-!
# Finitely many lengths decide equality of states

Two tensors of bond dimensions `D₁`, `D₂` have the same states at every positive length as soon
as the traces of their words agree for all lengths from `1` to `D₁ ^ 2 + D₂ ^ 2`.

The proof considers the block diagonal tensor `B ⊕ B'`: the spans of its words of lengths `1`
to `n` increase inside a space of dimension `D₁ ^ 2 + D₂ ^ 2`, and a single plateau is permanent.

## Main results

* `Monotone.le_of_plateau`: a monotone chain of bounded rank whose plateaus are permanent is
  constant from the rank bound on.
* `prod_map_mem_span_of_finrank_le`: in a finite dimensional algebra, every word of
  length at least `k ≤ 1` lies in the span of the words of lengths `k` to `N`, once
  `finrank ≤ N + (1 - k)`.
* `MPSTensor.sameMPV₂Pos_of_forall_trace_evalWord_eq`
-/

namespace MPSTensor

variable {d : ℕ}

/-- Words of the block diagonal tensor `B ⊕ B'`, realized in the product algebra, are the pairs
of words. -/
theorem prod_map_prodMk_eq_evalWord {D₁ D₂ : ℕ} (B : MPSTensor d D₁) (B' : MPSTensor d D₂)
    (w : List (Fin d)) :
    (w.map fun i => (B i, B' i)).prod = (Kraus.evalWord B w, Kraus.evalWord B' w) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih]

/-- **Finite trace test.** If `tr B^w = tr B'^w` for every word with
`1 ≤ |w| ≤ D₁ ^ 2 + D₂ ^ 2`, then `B` and `B'` have the same states at every positive length. -/
theorem sameMPV₂Pos_of_forall_trace_evalWord_eq {D₁ D₂ : ℕ}
    {B : MPSTensor d D₁} {B' : MPSTensor d D₂}
    (h : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ D₁ ^ 2 + D₂ ^ 2 →
      Matrix.trace (Kraus.evalWord B w) = Matrix.trace (Kraus.evalWord B' w)) :
    SameMPV₂Pos B B' := by
  let A := Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ
  let φ : A →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin D₁) ℂ ℂ).comp (LinearMap.fst ℂ _ _) -
      (Matrix.traceLinearMap (Fin D₂) ℂ ℂ).comp (LinearMap.snd ℂ _ _)
  have hφ : ∀ Y : A, φ Y = Matrix.trace Y.1 - Matrix.trace Y.2 := fun _ => rfl
  have hfin : Module.finrank ℂ A ≤ (D₁ ^ 2 + D₂ ^ 2) + (1 - 1) := by
    simp [A, Module.finrank_prod, Module.finrank_matrix, sq]
  have hspan : Submodule.span ℂ {x | ∃ u : List (Fin d), 1 ≤ u.length ∧
      u.length ≤ D₁ ^ 2 + D₂ ^ 2 ∧ (u.map fun i => (B i, B' i)).prod = x} ≤
      LinearMap.ker φ := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ, prod_map_prodMk_eq_evalWord]
    rw [h u hu1 hu2, sub_self]
  intro n hn σ
  have hw : 1 ≤ (List.ofFn σ).length := by simp only [List.length_ofFn]; omega
  have hmem := hspan (prod_map_mem_span_of_finrank_le (A := A) (fun i => (B i, B' i))
    le_rfl hfin (List.ofFn σ) hw)
  rw [LinearMap.mem_ker, hφ, prod_map_prodMk_eq_evalWord] at hmem
  simpa [mpv, coeff, sub_eq_zero] using hmem

end MPSTensor
