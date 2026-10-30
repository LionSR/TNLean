/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm

/-!
# Local index counts in Trotter product forms

Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075, expands each local exponential
only on the sites in its support. A site outside that support carries no index component.
Consequently, if at most `S` factors of one Trotter step touch a site, `n` steps carry at
most `n S` components there, each with `q²` values.
-/

open Matrix QuantumCircuit

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
  {near : ι → ι → Prop}

/-- The product form of a supported operator, with one matrix-unit label on its support
and no label off the support. Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
noncomputable def ProductForm.ofSupported {X : Finset ι} (i₀ : ι)
    (hX : ∀ j ∈ X, near i₀ j) {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set ι)) : ProductForm q near ρ := by
  classical
  let labels (α : ∀ j, j ∈ X → Fin q × Fin q) (j : ι) : Fin q × Fin q :=
    if hj : j ∈ X then α j hj else (0, 0)
  refine {
    Index := fun j ↦ j ∈ X → Fin q × Fin q
    siteOp := fun j a ↦ if hj : j ∈ X then single (a hj).1 (a hj).2 1 else 1
    coeff := fun i α ↦ if i = i₀ then ρ (fun j ↦ (labels α j).1) (fun j ↦ (labels α j).2)
      else 1
    coeff_local := ?_
    eq_sum := ?_ }
  · intro i α β h
    by_cases hi : i = i₀
    · subst i
      have hlabels : labels α = labels β := by
        funext j
        dsimp only [labels]
        split_ifs with hj
        · exact congrFun (h j (hX j hj)) hj
        · rfl
      simp only [hlabels]
    · simp only [ite_eq_right hi]
  · ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, rectKronecker_apply, smul_eq_mul,
      Fintype.prod_ite_eq']
    rw [Finset.sum_eq_single (fun j (_ : j ∈ X) ↦ (u j, v j))]
    · by_cases hoff : ∃ j ∉ (X : Set ι), u j ≠ v j
      · rw [apply_eq_zero_of_mem_supportedOperators hρ hoff]
        obtain ⟨j, hj, huv⟩ := hoff
        refine (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)).symm
        simp [show j ∉ X from hj, huv]
      · push Not at hoff
        rw [Finset.prod_eq_one fun j _ ↦ ?_, mul_one]
        · refine apply_eq_apply_of_mem_supportedOperators hρ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
            hoff fun j hj ↦ ?_
          · simp [labels, show j ∈ X from hj]
          · simp [labels, show j ∈ X from hj]
          · simp [labels, show j ∉ X from hj]
        · by_cases hj : j ∈ X
          · simp [hj]
          · simp [hj, Matrix.one_apply, hoff j hj]
    · intro α _ hα
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
      by_cases hmem : j ∈ X
      · have hbad : α j hmem ≠ (u j, v j) := fun h ↦ hj (funext fun _ ↦ h)
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
        rw [dite_eq_left hmem, single_apply]
        split_ifs with h
        · exact absurd (Prod.ext h.1 h.2) hbad
        · rfl
      · exact (hj (funext fun hk ↦ (hmem hk).elim)).elim
    · simp

/-- A supported factor has `q²` index values on its support and one value elsewhere.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
theorem ProductForm.card_index_ofSupported {X : Finset ι} (i₀ : ι)
    (hX : ∀ j ∈ X, near i₀ j) {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set ι)) (j : ι) :
    Fintype.card ((ProductForm.ofSupported i₀ hX hρ).Index j) =
      if j ∈ X then q * q else 1 := by
  change Fintype.card (j ∈ X → Fin q × Fin q) = _
  by_cases hj : j ∈ X
  · rw [ite_eq_left hj]
    let e : (j ∈ X → Fin q × Fin q) ≃ Fin q × Fin q :=
      ⟨fun f ↦ f hj, fun a _ ↦ a, fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)
  · rw [ite_eq_right hj]
    let e : (j ∈ X → Fin q × Fin q) ≃ Unit :=
      ⟨fun _ ↦ (), fun _ h ↦ (hj h).elim, fun f ↦ funext fun h ↦ (hj h).elim,
        fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)

/-- A product of local factors has exactly one matrix-unit index component for each
factor touching a site. Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_list_prod_card_index {κ : Type*}
    (H : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (X : κ → Finset ι) (c : κ → ι)
    (hX : ∀ k j, j ∈ X k → near (c k) j)
    (hH : ∀ k, H k ∈ supportedOperators q (X k : Set ι)) (seq : List κ) :
    ∃ P : ProductForm q near (seq.map H).prod, ∀ i,
      Fintype.card (P.Index i) = (q * q) ^ seq.countP (fun k ↦ decide (i ∈ X k)) := by
  induction seq with
  | nil => exact ⟨ProductForm.one near, fun i ↦ by simp⟩
  | cons k seq ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨(ProductForm.ofSupported (c k) (hX k) (hH k)).mul P, ?_⟩
    intro i
    change Fintype.card ((ProductForm.ofSupported (c k) (hX k) (hH k)).Index i ×
      P.Index i) = _
    rw [Fintype.card_prod, ProductForm.card_index_ofSupported, hP]
    by_cases hi : i ∈ X k <;> simp [hi, pow_succ, Nat.mul_comm]

/-- If at most `S` factors of one step act on any site, the `n`-step Trotter product has
at most `(q²)^(nS)` index values there. The product form is constructed from indices only on
the actual factor supports. Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_trotterProduct_card_index {κ : Type*}
    (H : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (X : κ → Finset ι) (c : κ → ι)
    (hX : ∀ k j, j ∈ X k → near (c k) j)
    (hH : ∀ k, H k ∈ supportedOperators q (X k : Set ι)) (seq : List κ)
    (S : ℕ) (hS : ∀ i, seq.countP (fun k ↦ decide (i ∈ X k)) ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm q near
        (((seq.map fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)).prod) ^ n),
      ∀ i, Fintype.card (P.Index i) ≤ (q * q) ^ (n * S) := by
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)) X c hX
    (fun k ↦ exp_mem_supportedOperators (Submodule.smul_mem _ _ (hH k))) seq
  refine ⟨P.pow n, fun i ↦ ?_⟩
  have hbase : 1 ≤ q * q := by
    have := NeZero.one_le (n := q)
    nlinarith
  calc
    Fintype.card ((P.pow n).Index i) = Fintype.card (P.Index i) ^ n :=
      ProductForm.card_index_pow P n i
    _ = (q * q) ^ (seq.countP (fun k ↦ decide (i ∈ X k)) * n) := by rw [hP, ← pow_mul]
    _ ≤ (q * q) ^ (S * n) := Nat.pow_le_pow_right hbase (Nat.mul_le_mul_right n (hS i))
    _ = (q * q) ^ (n * S) := by rw [Nat.mul_comm S n]

/-- Hastings' `nS` index-component bound on an arbitrary finite metric lattice.
Each centre occurs at most once in a Trotter step, every factor is supported in its
radius-`R` ball, and every such ball contains at most `S` sites. No Hermiticity is needed
for the exact product form. Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_trotterProduct_card_index_of_dist_le [PseudoMetricSpace ι]
    (H : ι → Matrix (ι → Fin q) (ι → Fin q) ℂ) (X : ι → Finset ι) (R : ℝ)
    (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, H i ∈ supportedOperators q (X i : Set ι))
    (seq : List ι) (hseq : seq.Nodup) (S : ℕ)
    (hS : ∀ i : ι, (Finset.univ.filter fun j ↦ dist i j ≤ R).card ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm q (fun i j ↦ dist i j ≤ R)
        (((seq.map fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)).prod) ^ n),
      ∀ i, Fintype.card (P.Index i) ≤ (q * q) ^ (n * S) := by
  classical
  have hBudget (i : ι) : seq.countP (fun k ↦ decide (i ∈ X k)) ≤ S := by
    rw [← hseq.card_eq_countP (P := fun k ↦ i ∈ X k)]
    refine (Finset.card_le_card (show seq.toFinset.filter (fun k ↦ i ∈ X k) ⊆
      Finset.univ.filter (fun k ↦ dist i k ≤ R) from ?_)).trans (hS i)
    intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
    rw [dist_comm]
    exact hX k i (Finset.mem_filter.mp hk).2
  exact exists_productForm_trotterProduct_card_index H X id hX hH seq S hBudget β n

end TNLean.Lattice
