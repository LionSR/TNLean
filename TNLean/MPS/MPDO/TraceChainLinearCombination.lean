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

/-- A finite linear combination of closing matrices is the same linear
combination of the represented operators, with all site tensors fixed. Empty
chains and zero dimensions are included. Trace algebra for ALVV,
arXiv:1602.08828v2, `prop:Cheby-AGSP-eff`, lines 1311–1333. -/
theorem traceChainOperator_sum_smul_closing {L q D : ℕ} {ι : Type*} [Fintype ι]
    (A : Fin L → MPOTensor q D) (c : ι → ℂ)
    (C : ι → Matrix (Fin D) (Fin D) ℂ) :
    traceChainOperator A (∑ a, c a • C a) =
      ∑ a, c a • traceChainOperator A (C a) := by
  ext sigma tau
  simp only [traceChainOperator, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Matrix.sum_apply, Matrix.smul_apply]

/-- One family of site tensors represents every weighted sum by varying only
its closing matrix. The tensors and coefficient matrices precede all weights;
the chain may be empty. This is trace algebra for the finite heat expansion in
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_traceChainOperator_common_linearCombination_varying {L q s : ℕ}
    (D : Fin s → ℕ) (A : (a : Fin s) → Fin L → MPOTensor q (D a))
    (Q : (a : Fin s) → Matrix (Fin (D a)) (Fin (D a)) ℂ) :
    ∃ (B : Fin L → MPOTensor q (∑ a, D a))
      (C : Fin s → Matrix (Fin (∑ a, D a)) (Fin (∑ a, D a)) ℂ),
      ∀ c : Fin s → ℂ,
        (∑ a, c a • traceChainOperator (A a) (Q a)) =
          traceChainOperator B (∑ a, c a • C a) := by
  classical
  let e : (Σ a : Fin s, Fin (D a)) ≃ Fin (∑ a, D a) :=
    Fintype.equivFinOfCardEq (by simp)
  let φ : ((a : Fin s) → Matrix (Fin (D a)) (Fin (D a)) ℂ) →+*
      Matrix (Fin (∑ a, D a)) (Fin (∑ a, D a)) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom.comp
      (Matrix.blockDiagonal'RingHom (fun a : Fin s ↦ Fin (D a)) ℂ)
  let B : Fin L → MPOTensor q (∑ a, D a) := fun v x y ↦ φ (fun a ↦ A a v x y)
  let C : Fin s → Matrix (Fin (∑ a, D a)) (Fin (∑ a, D a)) ℂ :=
    fun a ↦ φ (Pi.single a (Q a))
  have hφsmul (c : ℂ) (X : (a : Fin s) → Matrix (Fin (D a)) (Fin (D a)) ℂ) :
      φ (c • X) = c • φ X := by
    ext i j
    simp [φ, Matrix.blockDiagonal', Matrix.reindex]
  refine ⟨B, C, fun c ↦ ?_⟩
  have hcap : (∑ a, c a • C a) = φ (fun a ↦ c a • Q a) := by
    have hsingle : (∑ a, c a • Pi.single a (Q a)) =
        (fun a ↦ c a • Q a) := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _hb hba
        simp [Ne.symm hba]
      · simp
    rw [← hsingle, map_sum]
    simp only [C, hφsmul]
  rw [hcap]
  ext σ τ
  have hp := map_list_prod φ (List.ofFn (fun v a ↦ A a v (σ v) (τ v)))
  simp only [List.map_ofFn, Function.comp_def] at hp
  simp only [Matrix.sum_apply, Matrix.smul_apply, traceChainOperator]
  change (∑ a, c a * Matrix.trace (Q a * (List.ofFn (fun v ↦ A a v (σ v) (τ v))).prod)) =
    Matrix.trace (φ (fun a ↦ c a • Q a) *
      (List.ofFn (fun v ↦ φ (fun a ↦ A a v (σ v) (τ v)))).prod)
  rw [← hp, ← map_mul]
  change (∑ a, c a * Matrix.trace (Q a * (List.ofFn (fun v ↦ A a v (σ v) (τ v))).prod)) =
    Matrix.trace ((Matrix.blockDiagonal' (fun a ↦
      (c a • Q a) *
        (List.ofFn (fun v a ↦ A a v (σ v) (τ v))).prod a)).reindex e e)
  rw [Matrix.trace_reindex, Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp only [Pi.list_prod_apply, List.map_ofFn, Function.comp_def, smul_eq_mul]

/-- A finite weighted sum of actual trace-chain operators has actual site-dependent tensors
with the sum of their virtual dimensions. Supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. The physical chain is nonempty; the coefficients
are arbitrary complex scalars. -/
theorem exists_traceChainOperator_linearCombination_varying {L q s : ℕ} (hL : 1 ≤ L)
    (D : Fin s → ℕ) (A : (a : Fin s) → Fin L → MPOTensor q (D a)) (c : Fin s → ℂ) :
    ∃ B : Fin L → MPOTensor q (∑ a, D a),
      (∑ a, c a • traceChainOperator (A a) 1) = traceChainOperator B 1 := by
  obtain ⟨B, C, hrepr⟩ := exists_traceChainOperator_common_linearCombination_varying D A (fun _ ↦ 1)
  obtain ⟨B', hB'⟩ := exists_traceChainOperator_one hL B (∑ a, c a • C a)
  exact ⟨B', (hrepr c).trans hB'⟩

/-- Equal-bond operator chains admit one tensor family before every choice of
closing weights, including on an empty chain. This is finite trace algebra for
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_traceChainOperator_common_linearCombination {L q D s : ℕ}
    (A : Fin s → Fin L → MPOTensor q D)
    (Q : Fin s → Matrix (Fin D) (Fin D) ℂ) :
    ∃ (B : Fin L → MPOTensor q (D * s))
      (C : Fin s → Matrix (Fin (D * s)) (Fin (D * s)) ℂ),
      ∀ c : Fin s → ℂ,
        (∑ a, c a • traceChainOperator (A a) (Q a)) =
          traceChainOperator B (∑ a, c a • C a) := by
  have hdim : (∑ _a : Fin s, D) = D * s := by simp [Nat.mul_comm]
  have H := exists_traceChainOperator_common_linearCombination_varying (fun _ : Fin s ↦ D) A Q
  change ∃ (B : Fin L → MPOTensor q (∑ _a : Fin s, D))
    (C : Fin s → Matrix (Fin (∑ _a : Fin s, D)) (Fin (∑ _a : Fin s, D)) ℂ),
    ∀ c : Fin s → ℂ,
      (∑ a, c a • traceChainOperator (A a) (Q a)) =
        traceChainOperator B (∑ a, c a • C a) at H
  rwa [hdim] at H

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
