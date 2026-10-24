/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit

/-!
# Support of operators under a permutation of the sites

Permuting the sites of a finite system permutes the support of every operator: if `A` acts on
`S`, then `A` with both configurations precomposed with `p` acts on `p(S)`.

Source context: Hastings–Koma, arXiv:math-ph/0507008, Appendix A, finite-volume local
interactions.
-/

open Matrix

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Permuting the sites permutes the support of an operator. Source context:
Hastings–Koma, arXiv:math-ph/0507008, Appendix A, finite-volume local interactions. -/
theorem supportedOperators_submatrix_siteEquiv {S : Set ι} (p : Equiv.Perm ι)
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d S) :
    A.submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) ∈ supportedOperators d (p '' S) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨m, hm, rfl⟩ := hA
    have heq : (rectKronecker m).submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) =
        rectKronecker (fun k ↦ m (p.symm k)) := by
      ext σ τ
      simp only [Matrix.submatrix_apply, rectKronecker_apply, Function.comp_apply]
      exact (Fintype.prod_equiv p (fun k ↦ m k (σ (p k)) (τ (p k)))
        (fun k ↦ m (p.symm k) (σ k) (τ k)) (by simp))
    rw [heq]
    exact rectKronecker_mem_supportedOperators fun k hk ↦ hm _ (by
      intro h; exact hk ⟨p.symm k, h, p.apply_symm_apply k⟩)
  | zero => simp
  | add A B _ _ hA hB => exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact Submodule.smul_mem _ c hA

end QuantumCircuit
