/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TraceChainOperator
import QICLean.Algebra.TraceReindex

/-!
# Finite linear combinations of actual operator chains

Diagonal blocks combine a finite family of site-dependent operator tensors. The virtual
dimension is multiplied by the number of summands, rather than raised to that number.
Supporting ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.
-/

open Matrix

namespace MPOTensor

/-- A finite weighted sum of actual trace-chain operators has actual site-dependent tensors
with the sum of their virtual dimensions. Supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. The physical chain is nonempty; the coefficients
are arbitrary complex scalars. -/
theorem exists_traceChainOperator_linearCombination_varying {L q s : ℕ} (hL : 1 ≤ L)
    (D : Fin s → ℕ) (A : (a : Fin s) → Fin L → MPOTensor q (D a)) (c : Fin s → ℂ) :
    ∃ B : Fin L → MPOTensor q (∑ a, D a),
      (∑ a, c a • traceChainOperator (A a) 1) = traceChainOperator B 1 := by
  classical
  let e : (Σ a : Fin s, Fin (D a)) ≃ Fin (∑ a, D a) :=
    Fintype.equivFinOfCardEq (by simp)
  let φ : ((a : Fin s) → Matrix (Fin (D a)) (Fin (D a)) ℂ) →+*
      Matrix (Fin (∑ a, D a)) (Fin (∑ a, D a)) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom.comp
      (Matrix.blockDiagonal'RingHom (fun a : Fin s ↦ Fin (D a)) ℂ)
  let B : Fin L → MPOTensor q (∑ a, D a) := fun v x y ↦ φ (fun a ↦ A a v x y)
  let C := φ (fun a ↦ c a • (1 : Matrix (Fin (D a)) (Fin (D a)) ℂ))
  have hrepr : (∑ a, c a • traceChainOperator (A a) 1) = traceChainOperator B C := by
    ext σ τ
    have hp := map_list_prod φ (List.ofFn (fun v a ↦ A a v (σ v) (τ v)))
    simp only [List.map_ofFn, Function.comp_def] at hp
    simp only [Matrix.sum_apply, Matrix.smul_apply, traceChainOperator, Matrix.one_mul]
    change (∑ a, c a * Matrix.trace ((List.ofFn (fun v ↦ A a v (σ v) (τ v))).prod)) =
      Matrix.trace (φ (fun a ↦ c a • (1 : Matrix (Fin (D a)) (Fin (D a)) ℂ)) *
        (List.ofFn (fun v ↦ φ (fun a ↦ A a v (σ v) (τ v)))).prod)
    rw [← hp, ← map_mul]
    change (∑ a, c a * Matrix.trace ((List.ofFn (fun v ↦ A a v (σ v) (τ v))).prod)) =
      Matrix.trace ((Matrix.blockDiagonal' (fun a ↦
        (c a • (1 : Matrix (Fin (D a)) (Fin (D a)) ℂ)) *
          (List.ofFn (fun v a ↦ A a v (σ v) (τ v))).prod a)).reindex e e)
    rw [Matrix.trace_reindex, Matrix.trace_blockDiagonal']
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    simp only [Pi.list_prod_apply, List.map_ofFn, Function.comp_def, smul_eq_mul]
  obtain ⟨B', hB'⟩ := exists_traceChainOperator_one hL B C
  exact ⟨B', hrepr.trans hB'⟩

/-- A finite weighted sum of actual trace-chain operators has actual site-dependent tensors
with the sum of the equal virtual dimensions. Supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. The physical chain is nonempty; the coefficients
are arbitrary complex scalars. -/
theorem exists_traceChainOperator_linearCombination {L q D s : ℕ} (hL : 1 ≤ L)
    (A : Fin s → Fin L → MPOTensor q D) (c : Fin s → ℂ) :
    ∃ B : Fin L → MPOTensor q (D * s),
      (∑ a, c a • traceChainOperator (A a) 1) = traceChainOperator B 1 := by
  have hdim : (∑ _a : Fin s, D) = D * s := by simp [Nat.mul_comm]
  have H := exists_traceChainOperator_linearCombination_varying hL (fun _ : Fin s ↦ D) A c
  change ∃ B : Fin L → MPOTensor q (∑ _a : Fin s, D),
    (∑ a, c a • traceChainOperator (A a) 1) = traceChainOperator B 1 at H
  rwa [hdim] at H

/-- Adding two actual operator chains adds their virtual dimensions. Supporting the finite
heat sum in ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_traceChainOperator_add {L q D E : ℕ} (hL : 1 ≤ L)
    (A : Fin L → MPOTensor q D) (B : Fin L → MPOTensor q E) :
    ∃ C : Fin L → MPOTensor q (D + E),
      traceChainOperator A 1 + traceChainOperator B 1 = traceChainOperator C 1 := by
  classical
  let d : Fin 2 → ℕ := ![D, E]
  let F : (a : Fin 2) → Fin L → MPOTensor q (d a) :=
    Fin.cases A (Fin.cases B (fun i ↦ i.elim0))
  have H := exists_traceChainOperator_linearCombination_varying hL d F (fun _ ↦ 1)
  have hd : (∑ a, d a) = D + E := by simp [d, Fin.sum_univ_two]
  rw [hd] at H
  simp only [Fin.sum_univ_two, one_smul] at H
  change ∃ C : Fin L → MPOTensor q (D + E),
    traceChainOperator A 1 + traceChainOperator B 1 = traceChainOperator C 1 at H
  exact H

end MPOTensor
