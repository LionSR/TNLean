/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import TNLean.Lattice.FiniteDomain
import QICLean.Analysis.ProductFormula
import QICLean.Entropy.FilterStationarity

/-!
# Local index counts in Trotter product forms

Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075, expands each local exponential
only on the sites in its support. A site outside that support carries no index component.
Consequently, if at most `S` factors of one Trotter step touch a site, `n` steps carry at
most `n S` components there, each with `d_j²` values at a site `j` of physical dimension
`d_j`.

The physical dimension may vary with the site. Supports are the matrix-entry supports
`Entropy.IsSupportedOn`, the carrier of `ManyBody.supportedOperators`.

## Main results

* `TNLean.Lattice.ProductForm.ofSupported`: the product form of a supported operator, with
  indices only on its support.
* `TNLean.Lattice.exists_productForm_list_prod_card_index`: one index component for each
  factor of an ordered product acting at a site.
* `TNLean.Lattice.exists_productForm_lie_card_index_eq`: for sweeps with one factor per
  centre, the index set at `j` has `(d_j²)^(n c_j)` values, where `c_j` counts the supports
  containing `j`.
* `TNLean.Lattice.exists_productForm_lie_card_index_of_dist_le`: the source's bound
  `(d_j²)^(n S)` on a finite metric lattice.
* `TNLean.Lattice.card_filter_mem_support_le`: on a finite planar domain, `c_j` is at most the
  number of sites in the radius ball about `j`.

The Trotter product is `ProductFormula.lie H order (-β) n` (QICLean).
-/

open Matrix
open scoped Matrix.Norms.L2Operator
open ManyBody (planeDomainGraph)

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} {near : ι → ι → Prop}

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
  · have : IsEmpty ((j : ι) → Fin (d j)) := not_nonempty_iff.mp hconfig
    exact ⟨{ Index := fun i ↦ Fin ((d i * d i) ^ seq.countP (fun k ↦ decide (i ∈ X k)))
             siteOp := fun _ _ ↦ 0
             coeff := fun _ _ ↦ 0
             coeff_local := fun _ _ _ _ ↦ rfl
             eq_sum := Subsingleton.elim _ _ }, fun i ↦ Fintype.card_fin _⟩

/-- **Exact index count of a Trotter product.** Let each sweep contain one factor per
centre. The `n`-step Trotter product has a product form whose index set at `j` has
`(d_j²)^(n c_j)` values, where `c_j` counts the centres whose support contains `j`; the
exponent `n c_j` is the number of gates of the Trotter circuit meeting `j` (QICLean
`QuantumCircuit.participation_productCircuit`). The physical dimension `d_j` may vary with the site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1069–1077. -/
theorem exists_productForm_lie_card_index_eq
    (H : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : ι → Finset ι)
    (hX : ∀ i j, j ∈ X i → near i j)
    (hH : ∀ i, Entropy.IsSupportedOn (n := d) (H i) (X i))
    (order : List ι) (horder : order.Nodup) (hall : ∀ i, i ∈ order) (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d near (ProductFormula.lie H order (-(β : ℂ)) n),
      ∀ j, Fintype.card (P.Index j) =
        (d j * d j) ^ (n * (Finset.univ.filter fun i ↦ j ∈ X i).card) := by
  rw [ProductFormula.lie, ProductFormula.step, ← List.map_reverse]
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun i ↦ NormedSpace.exp ((-(β : ℂ) / n) • H i)) X id hX
    (fun i ↦ ManyBody.exp_mem_supportedOperators (X := fun j ↦ Fin (d j)) (D := X i)
      (SMulMemClass.smul_mem _ (hH i))) order.reverse
  refine ⟨P.pow n, fun j ↦ ?_⟩
  have huniv : order.reverse.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun i ↦ List.mem_toFinset.mpr (List.mem_reverse.mpr (hall i))
  have hcount : order.reverse.countP (fun i ↦ decide (j ∈ X i)) =
      (Finset.univ.filter fun i ↦ j ∈ X i).card := by
    rw [← (List.nodup_reverse.mpr horder).card_eq_countP (P := fun i ↦ j ∈ X i), huniv]
  rw [ProductForm.card_index_pow, hP, hcount, ← pow_mul, Nat.mul_comm _ n]

/-- If at most `S` factors of one step act on any site, the `n`-step Trotter product has
at most `(d_j²)^(nS)` index values at a site `j` of physical dimension `d_j`. The product
form is constructed from indices only on the actual factor supports.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_lie_card_index [∀ j, NeZero (d j)] {κ : Type*}
    (H : κ → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : κ → Finset ι)
    (c : κ → ι) (hX : ∀ k j, j ∈ X k → near (c k) j)
    (hH : ∀ k, Entropy.IsSupportedOn (n := d) (H k) (X k)) (order : List κ)
    (S : ℕ) (hS : ∀ i, order.countP (fun k ↦ decide (i ∈ X k)) ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d near (ProductFormula.lie H order (-(β : ℂ)) n),
      ∀ i, Fintype.card (P.Index i) ≤ (d i * d i) ^ (n * S) := by
  rw [ProductFormula.lie, ProductFormula.step, ← List.map_reverse]
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun k ↦ NormedSpace.exp ((-(β : ℂ) / n) • H k)) X c hX
    (fun k ↦ ManyBody.exp_mem_supportedOperators (X := fun j ↦ Fin (d j)) (D := X k)
      (SMulMemClass.smul_mem _ (hH k))) order.reverse
  refine ⟨P.pow n, fun i ↦ ?_⟩
  have hbase : 1 ≤ d i * d i := by
    have := NeZero.one_le (n := d i)
    nlinarith
  calc
    Fintype.card ((P.pow n).Index i) = Fintype.card (P.Index i) ^ n :=
      ProductForm.card_index_pow P n i
    _ = (d i * d i) ^ (order.reverse.countP (fun k ↦ decide (i ∈ X k)) * n) := by
      rw [hP, ← pow_mul]
    _ ≤ (d i * d i) ^ (S * n) :=
      Nat.pow_le_pow_right hbase (Nat.mul_le_mul_right n (by rw [List.countP_reverse]; exact hS i))
    _ = (d i * d i) ^ (n * S) := by rw [Nat.mul_comm S n]

/-- Hastings' `nS` index-component bound on an arbitrary finite metric lattice.
Each centre occurs at most once in a Trotter step, every factor is supported in its
radius-`R` ball, and every such ball contains at most `S` sites. No Hermiticity is needed
for the exact product form. The physical dimension `d_j` may vary with the site.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_lie_card_index_of_dist_le [PseudoMetricSpace ι]
    [∀ j, NeZero (d j)]
    (H : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (X : ι → Finset ι) (R : ℝ)
    (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, Entropy.IsSupportedOn (n := d) (H i) (X i))
    (order : List ι) (horder : order.Nodup) (S : ℕ)
    (hS : ∀ i : ι, (Finset.univ.filter fun j ↦ dist i j ≤ R).card ≤ S)
    (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm d (fun i j ↦ dist i j ≤ R) (ProductFormula.lie H order (-(β : ℂ)) n),
      ∀ i, Fintype.card (P.Index i) ≤ (d i * d i) ^ (n * S) := by
  classical
  have hBudget (i : ι) : order.countP (fun k ↦ decide (i ∈ X k)) ≤ S := by
    rw [← horder.card_eq_countP (P := fun k ↦ i ∈ X k)]
    refine (Finset.card_le_card (show order.toFinset.filter (fun k ↦ i ∈ X k) ⊆
      Finset.univ.filter (fun k ↦ dist i k ≤ R) from ?_)).trans (hS i)
    intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
    rw [dist_comm]
    exact hX k i (Finset.mem_filter.mp hk).2
  exact exists_productForm_lie_card_index H X id hX hH order S hBudget β n

variable {Λ : Finset (ℤ × ℤ)}

/-- Radius locality bounds the number of supports containing a site by the number of sites
in the radius ball. Source: Hastings, arXiv:cond-mat/0508554v3, lines 1073–1075, on the
finite planar domain. -/
theorem card_filter_mem_support_le {R : ℕ} (X : Site Λ → Finset (Site Λ))
    (hX : ∀ i j, j ∈ X i → ∃ p : (planeDomainGraph Λ).Walk i j, p.length ≤ R) (j : Site Λ) :
    (Finset.univ.filter fun i ↦ j ∈ X i).card ≤ (graphNeighborhood Λ R {j}).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨p, hp⟩ := hX i j (Finset.mem_filter.mp hi).2
  simp only [graphNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, exists_eq_left]
  exact ⟨p.reverse, by simpa using hp⟩

end TNLean.Lattice
