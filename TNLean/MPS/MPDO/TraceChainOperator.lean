/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel

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


section

open Matrix

open scoped BigOperators Kronecker

noncomputable section

namespace MPOTensor

/-- Every operator on a finite chain has a site-dependent capped trace
representation of some finite bond dimension. The empty chain and zero local
dimension are permitted. Elementary finite-dimensional algebra supporting
ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024; this is an
existence statement and makes no efficient bond or running-time assertion. -/
theorem exists_traceChainOperator_of_finite_matrix {n q : ℕ}
    (M : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) :
    ∃ (B : ℕ) (A : Fin n → MPOTensor q B)
      (C : Matrix (Fin B) (Fin B) ℂ), M = traceChainOperator A C := by
  classical
  let V := (Fin n → Fin q) × (Fin n → Fin q)
  let B := Fintype.card V
  let e : Fin B ≃ V := (Fintype.equivFin V).symm
  let f : Fin n → Fin q → Fin q → Fin B → ℂ := fun u s t v ↦
    if (e v).1 u = s ∧ (e v).2 u = t then 1 else 0
  let A : Fin n → MPOTensor q B := fun u s t ↦ Matrix.diagonal (f u s t)
  let c : Fin B → ℂ := fun v ↦ M (e v).1 (e v).2
  refine ⟨B, A, Matrix.diagonal c, ?_⟩
  ext σ τ
  have hp : (List.ofFn (fun u ↦ A u (σ u) (τ u))).prod =
      Matrix.diagonal (fun v ↦ if v = e.symm (σ, τ) then (1 : ℂ) else 0) := by
    have hd := (map_list_prod (Matrix.diagonalRingHom (Fin B) ℂ)
      (List.ofFn (fun u ↦ f u (σ u) (τ u)))).symm
    have hd' : (List.ofFn (fun u ↦ A u (σ u) (τ u))).prod =
        Matrix.diagonal (List.ofFn (fun u ↦ f u (σ u) (τ u))).prod := by
      simpa only [A, List.map_ofFn, Function.comp_def, Matrix.diagonalRingHom_apply] using hd
    rw [hd']
    congr 1
    funext v
    simp only [List.prod_ofFn, Finset.prod_apply, f]
    have hv : (∀ u, (e v).1 u = σ u ∧ (e v).2 u = τ u) ↔
        v = e.symm (σ, τ) := by
      constructor
      · intro h
        apply e.injective
        rw [e.apply_symm_apply]
        exact Prod.ext (funext (fun u ↦ (h u).1)) (funext (fun u ↦ (h u).2))
      · intro h
        rw [h, e.apply_symm_apply]
        exact fun _ ↦ ⟨rfl, rfl⟩
    simp only [Fintype.prod_ite_zero, Finset.prod_const_one, hv]
  change M σ τ = Matrix.trace
    (Matrix.diagonal c * (List.ofFn (fun u ↦ A u (σ u) (τ u))).prod)
  rw [hp, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [c, mul_ite]
end MPOTensor
end
end
