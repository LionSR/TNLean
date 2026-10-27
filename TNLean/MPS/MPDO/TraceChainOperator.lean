/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Trace contraction of a site-dependent operator chain

A supplied square closing matrix contracts the ordered product of the local
operator tensors. The local tensors may vary along the chain. Empty chains
and zero physical or virtual dimensions are permitted.

This is the site-dependent trace formula supporting the operator products in
CPSV17, arXiv:1606.00608, Section 4.5, lines 986–993, and the explicit stacked
cores in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333.
-/

namespace MPOTensor

/-- The operator obtained by contracting the actual site-dependent tensors
with the supplied closing matrix. For an empty chain its unique entry is the
trace of the closing matrix. Supporting CPSV17, arXiv:1606.00608, Section 4.5,
lines 986–993, and ALVV Proposition 5.7, lines 1311–1333. -/
noncomputable def traceChainOperator {L q D : ℕ}
    (A : Fin L → MPOTensor q D) (C : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  fun σ τ ↦ Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod)

end MPOTensor

namespace MPOTensor

/-- A closing matrix can be multiplied into the first tensor of a nonempty
site-dependent chain, with the same virtual dimension. The physical and virtual
dimensions may vanish. Elementary trace algebra supporting the explicit
trace presentations associated with ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333. -/
private theorem exists_trace_mul_prod_eq_trace_prod {L q D : ℕ}
    (hL : 1 ≤ L) (C : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin L → MPOTensor q D) :
    ∃ A' : Fin L → MPOTensor q D, ∀ σ τ : Fin L → Fin q,
      Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod) =
        Matrix.trace ((List.ofFn (fun v ↦ A' v (σ v) (τ v))).prod) := by
  cases L with
  | zero => simp at hL
  | succ n =>
    refine ⟨Fin.cons (fun x y ↦ C * A 0 x y) (fun v ↦ A v.succ), ?_⟩
    intro σ τ
    simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ,
      Matrix.mul_assoc]

end MPOTensor

namespace MPOTensor

/-- On a nonempty site-dependent chain, every supplied closing matrix can be
replaced by the identity after changing the site tensors at the same virtual
dimension. The physical and virtual dimensions may vanish. Supporting explicit
trace algebra associated with ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333. -/
theorem exists_traceChainOperator_one {L q D : ℕ}
    (hL : 1 ≤ L) (A : Fin L → MPOTensor q D)
    (C : Matrix (Fin D) (Fin D) ℂ) :
    ∃ A' : Fin L → MPOTensor q D,
      traceChainOperator A C = traceChainOperator A' 1 := by
  obtain ⟨A', hA'⟩ := exists_trace_mul_prod_eq_trace_prod hL C A
  refine ⟨A', ?_⟩
  ext σ τ
  change Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod) =
    Matrix.trace ((1 : Matrix (Fin D) (Fin D) ℂ) *
      (List.ofFn (fun v ↦ A' v (σ v) (τ v))).prod)
  rw [Matrix.one_mul]
  exact hA' σ τ

end MPOTensor
