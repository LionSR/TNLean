/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import TNLean.Lattice.TrotterActiveIndices
import QICLean.Entropy.FilterStationarity

/-!
# Local index counts in Trotter product forms

Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075, expands each local exponential
only on the sites in its support. A site outside that support carries no index component.
Consequently, if at most `S` factors of one Trotter step touch a site, `n` steps carry at
most `n S` components there, each with `d_j²` values at a site `j` of physical dimension
`d_j`.

The physical dimension may vary with the site. Supports are the matrix-entry supports
`Entropy.IsSupportedOn`; for a common dimension `q` these are the operators of
`QuantumCircuit.supportedOperators q` (`QuantumCircuit.isSupportedOn_of_mem_supportedOperators`).

## Main results

* `TNLean.Lattice.ProductForm.ofSupported`: the product form of a supported operator, with
  indices only on its support.
* `TNLean.Lattice.exists_productForm_list_prod_card_index`: one index component for each
  factor of an ordered product acting at a site.
* `TNLean.Lattice.exists_productForm_trotterProduct_card_index_eq`: for sweeps with one
  factor per centre, the index set at `j` has exactly as many values as the assignments of a
  pair of physical indices to the active occurrences at `j`, namely `(d_j²)^(n c_j)`.
* `TNLean.Lattice.exists_productForm_trotterProduct_card_index_of_dist_le`: the source's
  bound `(d_j²)^(n S)` on a finite metric lattice.
-/

open Matrix

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} {near : ι → ι → Prop}

/-- Exponentials of scalar multiples of an operator supported on `D` are supported on `D`.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem isSupportedOn_exp_smul {D : Finset ι}
    {A : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (hA : Entropy.IsSupportedOn (n := d) A D) (c : ℂ) :
    Entropy.IsSupportedOn (n := d) (NormedSpace.exp (c • A)) D := by
  by_cases hconfig : Nonempty ((j : ι) → Fin (d j))
  · obtain ⟨σ₀⟩ := hconfig
    let p : Submodule ℂ (Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) :=
      { carrier := {B | Entropy.IsSupportedOn (n := d) B D}
        add_mem' := fun {B C} (hB : Entropy.IsSupportedOn (n := d) B D)
            (hC : Entropy.IsSupportedOn (n := d) C D) ↦
          ⟨fun σ τ h ↦ by rw [Matrix.add_apply, hB.1 σ τ h, hC.1 σ τ h, add_zero],
            fun σ τ σ' τ' h1 h2 h3 h4 ↦ by
              rw [Matrix.add_apply, Matrix.add_apply, hB.2 σ τ σ' τ' h1 h2 h3 h4,
                hC.2 σ τ σ' τ' h1 h2 h3 h4]⟩
        zero_mem' := (⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩ :
          Entropy.IsSupportedOn (n := d) 0 D)
        smul_mem' := fun a {B} (hB : Entropy.IsSupportedOn (n := d) B D) ↦
          ⟨fun σ τ h ↦ by rw [Matrix.smul_apply, hB.1 σ τ h, smul_zero],
            fun σ τ σ' τ' h1 h2 h3 h4 ↦ by
              rw [Matrix.smul_apply, Matrix.smul_apply, hB.2 σ τ σ' τ' h1 h2 h3 h4]⟩ }
    let s : Subalgebra ℂ (Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) :=
      p.toSubalgebra (Entropy.isSupportedOn_one (n := d) D)
        fun B C (hB : Entropy.IsSupportedOn (n := d) B D)
          (hC : Entropy.IsSupportedOn (n := d) C D) ↦ hB.mul hC σ₀
    have hmem : c • A ∈ s := p.smul_mem c hA
    have hexp : NormedSpace.exp (c • A) ∈ s :=
      NormedSpace.exp_mem (R := ℂ) (s := s) (Submodule.closed_of_finiteDimensional p) hmem
    exact hexp
  · exact ⟨fun σ ↦ (hconfig ⟨σ⟩).elim, fun σ ↦ (hconfig ⟨σ⟩).elim⟩

/-- The product form of a supported operator, with one matrix-unit label on its support
and no label off the support. The configuration `z` supplies the labels off the support,
where they do not affect the operator. Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
noncomputable def ProductForm.ofSupported {X : Finset ι} (z : (j : ι) → Fin (d j)) (i₀ : ι)
    (hX : ∀ j ∈ X, near i₀ j) {ρ : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (hρ : Entropy.IsSupportedOn (n := d) ρ X) : ProductForm d near ρ := by
  classical
  let labels (α : ∀ j, j ∈ X → Fin (d j) × Fin (d j)) (j : ι) : Fin (d j) × Fin (d j) :=
    if hj : j ∈ X then α j hj else (z j, z j)
  refine {
    Index := fun j ↦ j ∈ X → Fin (d j) × Fin (d j)
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
    simp only [Matrix.sum_apply, Matrix.smul_apply, piKronecker_apply, smul_eq_mul,
      Fintype.prod_ite_eq']
    rw [Finset.sum_eq_single (fun j (_ : j ∈ X) ↦ (u j, v j))]
    · by_cases hoff : ∃ j ∉ X, u j ≠ v j
      · rw [hρ.1 u v hoff]
        obtain ⟨j, hj, huv⟩ := hoff
        refine (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)).symm
        simp [hj, huv]
      · push Not at hoff
        rw [Finset.prod_eq_one fun j _ ↦ ?_, mul_one]
        · refine hρ.2 u v _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_) hoff fun j hj ↦ ?_
          · simp [labels, hj]
          · simp [labels, hj]
          · simp [labels, hj]
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

/-- A supported factor has `d_j²` index values at a site `j` of its support and one value
elsewhere. Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
theorem ProductForm.card_index_ofSupported {X : Finset ι} (z : (j : ι) → Fin (d j)) (i₀ : ι)
    (hX : ∀ j ∈ X, near i₀ j) {ρ : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (hρ : Entropy.IsSupportedOn (n := d) ρ X) (j : ι) :
    Fintype.card ((ProductForm.ofSupported z i₀ hX hρ).Index j) =
      if j ∈ X then d j * d j else 1 := by
  change Fintype.card (j ∈ X → Fin (d j) × Fin (d j)) = _
  by_cases hj : j ∈ X
  · rw [ite_eq_left hj]
    let e : (j ∈ X → Fin (d j) × Fin (d j)) ≃ Fin (d j) × Fin (d j) :=
      ⟨fun f ↦ f hj, fun a _ ↦ a, fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)
  · rw [ite_eq_right hj]
    let e : (j ∈ X → Fin (d j) × Fin (d j)) ≃ Unit :=
      ⟨fun _ ↦ (), fun _ h ↦ (hj h).elim, fun f ↦ funext fun h ↦ (hj h).elim,
        fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)

/-- A product of local factors has exactly one matrix-unit index component for each
factor touching a site. When some site has dimension zero there are no configurations,
and any index sets of these cardinalities serve.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_list_prod_card_index {κ : Type*}
    (H : κ → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : κ → Finset ι)
    (c : κ → ι) (hX : ∀ k j, j ∈ X k → near (c k) j)
    (hH : ∀ k, Entropy.IsSupportedOn (n := d) (H k) (X k)) (seq : List κ) :
    ∃ P : ProductForm d near (seq.map H).prod, ∀ i,
      Fintype.card (P.Index i) = (d i * d i) ^ seq.countP (fun k ↦ decide (i ∈ X k)) := by
  by_cases hconfig : Nonempty ((j : ι) → Fin (d j))
  · obtain ⟨z⟩ := hconfig
    induction seq with
    | nil => exact ⟨ProductForm.one near, fun i ↦ by simp⟩
    | cons k seq ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨(ProductForm.ofSupported z (c k) (hX k) (hH k)).mul P, ?_⟩
      intro i
      change Fintype.card ((ProductForm.ofSupported z (c k) (hX k) (hH k)).Index i ×
        P.Index i) = _
      rw [Fintype.card_prod, ProductForm.card_index_ofSupported, hP]
      by_cases hi : i ∈ X k <;> simp [hi, pow_succ, Nat.mul_comm]
  · haveI : IsEmpty ((j : ι) → Fin (d j)) := not_nonempty_iff.mp hconfig
    exact ⟨{ Index := fun i ↦ Fin ((d i * d i) ^ seq.countP (fun k ↦ decide (i ∈ X k)))
             siteOp := fun _ _ ↦ 0
             coeff := fun _ _ ↦ 0
             coeff_local := fun _ _ _ _ ↦ rfl
             eq_sum := Subsingleton.elim _ _ }, fun i ↦ Fintype.card_fin _⟩

/-- **Exact index count of a Trotter product.** Let each sweep contain one factor per
centre. The `n`-step Trotter product has a product form whose index set at `j` has as many
values as the assignments of a pair of physical indices at `j` to the active occurrences
at `j`, that is `(d_j²)^(n c_j)` values (`card_trotterActiveIndices`), where `c_j` counts
the centres whose support contains `j`. The physical dimension `d_j` may vary with the site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1069–1077. -/
theorem exists_productForm_trotterProduct_card_index_eq
    (H : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : ι → Finset ι)
    (hX : ∀ i j, j ∈ X i → near i j)
    (hH : ∀ i, Entropy.IsSupportedOn (n := d) (H i) (X i))
    (seq : List ι) (hseq : seq.Nodup) (hall : ∀ i, i ∈ seq) (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d near
        (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)).prod) ^ n),
      ∀ j, Fintype.card (P.Index j) =
        Fintype.card (trotterActiveOccurrences X n j → Fin (d j) × Fin (d j)) := by
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)) X id hX
    (fun i ↦ isSupportedOn_exp_smul (hH i) _) seq
  refine ⟨P.pow n, fun j ↦ ?_⟩
  have huniv : seq.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun i ↦ List.mem_toFinset.mpr (hall i)
  have hcount : seq.countP (fun i ↦ decide (j ∈ X i)) =
      (Finset.univ.filter fun i ↦ j ∈ X i).card := by
    rw [← hseq.card_eq_countP (P := fun i ↦ j ∈ X i), huniv]
  rw [ProductForm.card_index_pow, hP, card_trotterActiveIndices, hcount, ← pow_mul,
    Nat.mul_comm n]

/-- If at most `S` factors of one step act on any site, the `n`-step Trotter product has
at most `(d_j²)^(nS)` index values at a site `j` of physical dimension `d_j`. The product
form is constructed from indices only on the actual factor supports.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_trotterProduct_card_index [∀ j, NeZero (d j)] {κ : Type*}
    (H : κ → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : κ → Finset ι)
    (c : κ → ι) (hX : ∀ k j, j ∈ X k → near (c k) j)
    (hH : ∀ k, Entropy.IsSupportedOn (n := d) (H k) (X k)) (seq : List κ)
    (S : ℕ) (hS : ∀ i, seq.countP (fun k ↦ decide (i ∈ X k)) ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d near
        (((seq.map fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)).prod) ^ n),
      ∀ i, Fintype.card (P.Index i) ≤ (d i * d i) ^ (n * S) := by
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)) X c hX
    (fun k ↦ isSupportedOn_exp_smul (hH k) _) seq
  refine ⟨P.pow n, fun i ↦ ?_⟩
  have hbase : 1 ≤ d i * d i := by
    have := NeZero.one_le (n := d i)
    nlinarith
  calc
    Fintype.card ((P.pow n).Index i) = Fintype.card (P.Index i) ^ n :=
      ProductForm.card_index_pow P n i
    _ = (d i * d i) ^ (seq.countP (fun k ↦ decide (i ∈ X k)) * n) := by rw [hP, ← pow_mul]
    _ ≤ (d i * d i) ^ (S * n) := Nat.pow_le_pow_right hbase (Nat.mul_le_mul_right n (hS i))
    _ = (d i * d i) ^ (n * S) := by rw [Nat.mul_comm S n]

/-- Hastings' `nS` index-component bound on an arbitrary finite metric lattice.
Each centre occurs at most once in a Trotter step, every factor is supported in its
radius-`R` ball, and every such ball contains at most `S` sites. No Hermiticity is needed
for the exact product form. The physical dimension `d_j` may vary with the site.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_trotterProduct_card_index_of_dist_le [PseudoMetricSpace ι]
    [∀ j, NeZero (d j)]
    (H : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : ι → Finset ι) (R : ℝ)
    (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, Entropy.IsSupportedOn (n := d) (H i) (X i))
    (seq : List ι) (hseq : seq.Nodup) (S : ℕ)
    (hS : ∀ i : ι, (Finset.univ.filter fun j ↦ dist i j ≤ R).card ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d (fun i j ↦ dist i j ≤ R)
        (((seq.map fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)).prod) ^ n),
      ∀ i, Fintype.card (P.Index i) ≤ (d i * d i) ^ (n * S) := by
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
