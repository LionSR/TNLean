/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BiCFDerivation.Selectors

/-!
# Propagation of simultaneous word spans in trace-preserving form

A full simultaneous word span at one length remains full at every larger
length when each block is trace-preserving. To extend by one site, express
$M_j(A^{j,a})^\dagger$ at the given length, append $A^{j,a}$, and sum over the
physical letter. This is the trace-preserving counterpart of the unital
propagation in PGVWC07, arXiv:quant-ph/0608197, lines 893--898.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

private theorem sum_adjoint_wordTuple_one
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    (M : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    (∑ a : Fin d, fun j : Fin r ↦
      (M j * (A j a)ᴴ) * wordTuple A 1 (fun _ ↦ a) j) = M := by
  funext j
  simp only [Finset.sum_apply, wordTuple, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one, Matrix.mul_assoc,
    ← Finset.mul_sum, hTP]

/-- Trace-preserving normalization propagates a full simultaneous word span
by one site. This is the adjoint normalization of PGVWC07,
arXiv:quant-ph/0608197, lines 893--898. -/
theorem wordTupleSpanTop_succ_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j)) {L : ℕ}
    (hSpan : WordTupleSpanTop A L)
    (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1) :
    WordTupleSpanTop A (L + 1) := by
  classical
  unfold WordTupleSpanTop at hSpan ⊢
  refine top_unique fun M _ ↦ ?_
  rw [← sum_adjoint_wordTuple_one A hTP M]
  exact Submodule.sum_mem _ fun a _ ↦
    pointwise_mul_mem_span_wordTuple_add A (L := L) (S := 1)
      (by simp [hSpan]) (Submodule.subset_span ⟨fun _ ↦ a, rfl⟩)

/-- Trace-preserving normalization propagates a full simultaneous word span
to every larger length, without increasing its initial threshold. -/
theorem wordTupleSpanTop_of_ge_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j)) {L n : ℕ}
    (hSpan : WordTupleSpanTop A L)
    (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1) (hLn : L ≤ n) :
    WordTupleSpanTop A n :=
  Nat.le_induction hSpan
    (fun _ _ h ↦ wordTupleSpanTop_succ_of_tracePreserving A h hTP) n hLn

end MPSTensor
