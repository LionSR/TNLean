/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LocalHamiltonian
import TNLean.Circuit.SupportedMatrixElements
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Matrix product form on finite sets of sites

For a finite set of sites and a locality relation `near`, a matrix product form is an
expansion
`ρ = ∑_α (∏_i F_i(α)) • ⊗_j ρ_j(α_j)`
in which `F_i` depends only on indices `α_j` with `near i j`. On a metric lattice the
relation is `dist i j ≤ l`; on a finite graph it may instead mean that a walk of length
at most `l` joins the sites. The construction and its closure under products use no
embedding or particular metric.

An operator supported in the neighborhood of a specified centre has this form. Applying
this to each exponential in a finite Trotter product and grouping the indices at each
site proves the product form for an arbitrary finite metric lattice. Empty supports and
zero Trotter steps are included. The planar local-Hamiltonian result is a specialization.

The index type may depend on the site, as in the source's indices `α_i`. A supported
factor can therefore carry a matrix-unit index only on its support. The construction and
the source's bound of `n S` index components at each site are proved in
`TNLean/Lattice/TrotterIndexCount.lean`.

## Main results

* `hasProductForm_of_mem_supportedOperators_radius`: the expansion for a supported operator.
* `HasProductForm.mul`, `HasProductForm.pow`: closure under products and powers.
* `hasProductForm_trotterProduct_of_dist_le`: the source's finite metric-lattice statement.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
  eq. `mpf`, lines 1024–1046, and the Trotter decomposition, lines 1048–1079.
-/

open Matrix QuantumCircuit
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- An entry of an operator supported on `S` depends only on the labels on `S`, provided both
pairs of configurations agree with each other off `S`. -/
theorem apply_eq_apply_of_mem_supportedOperators {S : Set ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d S)
    {u v x y : ι → Fin d} (hux : ∀ j ∈ S, u j = x j) (hvy : ∀ j ∈ S, v j = y j)
    (huv : ∀ j ∉ S, u j = v j) (hxy : ∀ j ∉ S, x j = y j) : A u v = A x y := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨m, hm, rfl⟩ := hA
    simp only [rectKronecker_apply]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    by_cases hj : j ∈ S
    · rw [hux j hj, hvy j hj]
    · rw [hm j hj, huv j hj, hxy j hj, one_apply_eq, one_apply_eq]
  | zero => rfl
  | add A B _ _ hA hB => simp [hA, hB]
  | smul c A _ hA => simp [hA]

/-- The operators supported on a set of sites are closed under the exponential. -/
theorem exp_mem_supportedOperators {S : Set ι} {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) : NormedSpace.exp A ∈ supportedOperators d S := by
  let s : Subalgebra ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
    (supportedOperators d S).toSubalgebra (one_mem_supportedOperators S)
      fun _ _ ↦ mul_mem_supportedOperators
  exact NormedSpace.exp_mem (R := ℂ) (s := s)
    (Submodule.closed_of_finiteDimensional (supportedOperators d S)) hA

end QuantumCircuit

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {near : ι → ι → Prop}

/-- A coefficient function at site `i` that depends only on indices at the sites `j`
with `near i j`. On a metric lattice of range `l`, this means `dist i j ≤ l`.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1037–1039. -/
def IsLocalCoefficient (near : ι → ι → Prop) (i : ι) {A : ι → Type*} (f : (∀ j, A j) → ℂ) : Prop :=
  ∀ α β : (∀ j, A j),
    (∀ j, near i j → α j = β j) → f α = f β

/-- **Matrix product form.** The data of eq. `mpf`: an index type at each site and operators
`siteOp j a`, and coefficient functions `coeff i` depending only on `near i`, with
`ρ = ∑_α (∏ᵢ coeff i α) • ⊗ⱼ siteOp j (α j)`.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
structure ProductForm (q : ℕ) (near : ι → ι → Prop)
    (ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ) where
  /-- The values of the index carried by each site; the type may vary with the site. -/
  Index : ι → Type
  /-- The index at each site takes finitely many values. -/
  [fintype : ∀ j, Fintype (Index j)]
  /-- The operator `ρⱼ(a)` acting only on site `j`. -/
  siteOp : (j : ι) → Index j → Matrix (Fin q) (Fin q) ℂ
  /-- The coefficient function `Fᵢ` attached to site `i`. -/
  coeff : ι → (∀ j, Index j) → ℂ
  /-- Each `Fᵢ` depends only on the indices at sites `j` with `near i j`. -/
  coeff_local : ∀ i, IsLocalCoefficient near i (coeff i)
  /-- The expansion of eq. `mpf`. -/
  eq_sum : ρ = ∑ α : (∀ j, Index j), (∏ i, coeff i α) • rectKronecker fun j ↦ siteOp j (α j)

attribute [instance] ProductForm.fintype

/-- An operator has a matrix product form with coefficient neighborhoods `near`.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
def HasProductForm (q : ℕ) (near : ι → ι → Prop)
    (ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ) : Prop :=
  Nonempty (ProductForm q near ρ)

omit [Fintype ι] [DecidableEq ι] in
/-- A coefficient depending only on `near i` also depends only on any larger set. -/
theorem IsLocalCoefficient.mono {near' : ι → ι → Prop}
    (hnear : ∀ i j, near i j → near' i j) {i : ι} {A : ι → Type*}
    {f : (∀ j, A j) → ℂ} (hf : IsLocalCoefficient near i f) : IsLocalCoefficient near' i f :=
  fun α β h ↦ hf α β fun j hj ↦ h j (hnear i j hj)

/-- Enlarging the allowed neighborhoods preserves a product form. -/
theorem HasProductForm.mono {near' : ι → ι → Prop}
    (hnear : ∀ i j, near i j → near' i j)
    {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hρ : HasProductForm q near ρ) :
    HasProductForm q near' ρ := by
  obtain ⟨P⟩ := hρ
  exact ⟨{ P with coeff_local := fun i ↦ (P.coeff_local i).mono hnear }⟩

/-- The product form of the identity with one index value at every site.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
noncomputable def ProductForm.one (near : ι → ι → Prop) : ProductForm q near 1 where
  Index := fun _ ↦ Unit
  siteOp := fun _ _ ↦ 1
  coeff := fun _ _ ↦ 1
  coeff_local := fun _ _ _ _ ↦ rfl
  eq_sum := by simp

/-- The identity has a product form for every locality relation. -/
theorem hasProductForm_one (near : ι → ι → Prop) : HasProductForm q near 1 :=
  ⟨ProductForm.one near⟩

/-- **Products.** Product forms with the same coefficient neighborhoods are closed under
multiplication: pair the two indices at each site and multiply the coefficient functions.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
noncomputable def ProductForm.mul {ρ σ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) (Q : ProductForm q near σ) :
    ProductForm q near (ρ * σ) := by
  refine {
    Index := fun j ↦ P.Index j × Q.Index j
    siteOp := fun j a ↦ P.siteOp j a.1 * Q.siteOp j a.2
    coeff := fun i γ ↦ P.coeff i (fun j ↦ (γ j).1) * Q.coeff i (fun j ↦ (γ j).2)
    coeff_local := fun i α β h ↦ ?_
    eq_sum := ?_ }
  · dsimp only
    rw [P.coeff_local i _ _ fun j hj ↦ congrArg Prod.fst (h j hj),
      Q.coeff_local i _ _ fun j hj ↦ congrArg Prod.snd (h j hj)]
  · refine (congrArg₂ (· * ·) P.eq_sum Q.eq_sum).trans ?_
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun x ↦ ?_
    simp [rectKronecker_mul, Finset.prod_mul_distrib, Equiv.arrowProdEquivProdArrow, smul_smul,
      mul_comm]

/-- Products preserve coefficient neighborhoods. -/
theorem HasProductForm.mul {ρ σ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : HasProductForm q near ρ) (hσ : HasProductForm q near σ) :
    HasProductForm q near (ρ * σ) := by
  obtain ⟨P⟩ := hρ
  obtain ⟨Q⟩ := hσ
  exact ⟨P.mul Q⟩

/-- Repeated multiplication groups the per-site indices in the product form of a power.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mplt`, lines 1303–1317. -/
noncomputable def ProductForm.pow {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) : (n : ℕ) → ProductForm q near (ρ ^ n)
  | 0 => ProductForm.one near
  | n + 1 => (P.pow n).mul P

/-- The index of the identity product form has one value at each site. -/
@[simp] theorem ProductForm.card_index_one (near : ι → ι → Prop) (i : ι) :
    Fintype.card ((ProductForm.one (q := q) near).Index i) = 1 := by
  change Fintype.card Unit = 1
  exact Fintype.card_unique

/-- Multiplying product forms multiplies the numbers of index values at each site. -/
@[simp] theorem ProductForm.card_index_mul {ρ σ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) (Q : ProductForm q near σ) (i : ι) :
    Fintype.card ((P.mul Q).Index i) = Fintype.card (P.Index i) * Fintype.card (Q.Index i) := by
  exact Fintype.card_prod _ _

/-- The index count in a power is the corresponding power of the original count.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1072–1075 and 1318–1320. -/
@[simp] theorem ProductForm.card_index_pow {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) (n : ℕ) (i : ι) :
    Fintype.card ((P.pow n).Index i) = Fintype.card (P.Index i) ^ n := by
  induction n with
  | zero => exact card_index_one near i
  | succ n ih =>
    change Fintype.card ((P.pow n).Index i × P.Index i) = _
    rw [Fintype.card_prod, ih, pow_succ]

/-- Finite ordered products preserve the coefficient neighborhoods of a product form. -/
theorem hasProductForm_list_prod (L : List (Matrix (ι → Fin q) (ι → Fin q) ℂ))
    (hL : ∀ ρ ∈ L, HasProductForm q near ρ) : HasProductForm q near L.prod := by
  induction L with
  | nil => exact hasProductForm_one near
  | cons ρ L ih =>
    rw [List.prod_cons]
    exact (hL ρ (by simp)).mul (ih fun σ hσ ↦ hL σ (by simp [hσ]))

/-- Powers preserve the coefficient neighborhoods of a product form. -/
theorem HasProductForm.pow {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : HasProductForm q near ρ) (n : ℕ) : HasProductForm q near (ρ ^ n) := by
  obtain ⟨P⟩ := hρ
  exact ⟨P.pow n⟩

/-- An operator supported in the neighborhood of a specified centre has a product form
with those coefficient neighborhoods. The centre need not belong to the support, which may
be empty. Every site is assumed to belong to its own neighborhood.
The matrix-element coefficient is attached to the centre; diagonal identity factors
are retained at every site off the support, including the centre when necessary.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators_radius {X : Finset ι}
    (hnear : ∀ i, near i i) (i₀ : ι) (hX : ∀ j ∈ X, near i₀ j)
    {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set ι)) : HasProductForm q near ρ := by
  classical
  /- The configurations read off the indices: their labels on `X`, and one common label
  (the row label at `i₀`) off `X`. -/
  let row : (ι → Fin q × Fin q) → ι → Fin q :=
    fun α j ↦ if j ∈ X then (α j).1 else (α i₀).1
  let col : (ι → Fin q × Fin q) → ι → Fin q :=
    fun α j ↦ if j ∈ X then (α j).2 else (α i₀).1
  refine ⟨{ Index := fun _ ↦ Fin q × Fin q
            siteOp := fun _ a ↦ single a.1 a.2 1
            coeff := fun i α ↦ (if i = i₀ then ρ (row α) (col α) else 1) *
              if i ∈ X then 1 else if (α i).1 = (α i).2 then 1 else 0
            coeff_local := fun i α β h ↦ ?_
            eq_sum := ?_ }⟩
  · have hnil : α i = β i := h i (hnear i)
    by_cases hi : i = i₀
    · subst hi
      have hrow : row α = row β := funext fun j ↦ by
        simp only [row]
        split_ifs with hj
        · rw [h j (hX j hj)]
        · rw [hnil]
      have hcol : col α = col β := funext fun j ↦ by
        simp only [col]
        split_ifs with hj
        · rw [h j (hX j hj)]
        · rw [hnil]
      simp only [hrow, hcol, hnil]
    · simp [hi, hnil]
  · ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, rectKronecker_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (fun j ↦ (u j, v j))]
    · simp only [single_apply_same, Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
        Fintype.prod_ite_eq']
      by_cases hoff : ∃ j ∉ (X : Set ι), u j ≠ v j
      · rw [apply_eq_zero_of_mem_supportedOperators hρ hoff]
        obtain ⟨j, hj, huv⟩ := hoff
        refine (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)).symm
        simp [show j ∉ X from hj, huv]
      · push Not at hoff
        rw [Finset.prod_eq_one fun j _ ↦ ?_, mul_one]
        · refine apply_eq_apply_of_mem_supportedOperators hρ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
            hoff fun j hj ↦ ?_
          · simp [row, show j ∈ X from hj]
          · simp [col, show j ∈ X from hj]
          · simp [row, col, show j ∉ X from hj]
        · by_cases hj : j ∈ X
          · simp [hj]
          · simp [hj, hoff j hj]
    · intro α _ hα
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
      rw [single_apply]
      split_ifs with h
      · exact absurd (Prod.ext h.1 h.2) hj
      · rfl
    · simp

/-- An operator on a nonempty support whose sites are pairwise related by `near` has
the corresponding product form, by choosing any site of the support as its centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators {X : Finset ι}
    (hnear : ∀ i, near i i)
    (hX : X.Nonempty ∧ ∀ i ∈ X, ∀ j ∈ X, near i j)
    {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set ι)) : HasProductForm q near ρ := by
  obtain ⟨i₀, hi₀⟩ := hX.1
  exact hasProductForm_of_mem_supportedOperators_radius hnear i₀ (hX.2 i₀ hi₀) hρ

/-- Trotter products of operators supported in the neighborhoods of their centres have
the same product form. Empty supports and zero steps are admitted.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077. -/
theorem hasProductForm_trotterProduct_of_radius
    (hnear : ∀ i, near i i)
    (H : ι → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → near i j)
    (hH : ∀ i, H i ∈ supportedOperators q (X i : Set ι))
    (seq : List ι) (β : ℝ) (n : ℕ) :
    HasProductForm q near
      (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)).prod) ^ n) := by
  refine HasProductForm.pow (hasProductForm_list_prod _ fun ρ hρ ↦ ?_) n
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hρ
  exact hasProductForm_of_mem_supportedOperators_radius hnear i (hX i)
    (exp_mem_supportedOperators (Submodule.smul_mem _ _ (hH i)))

/-- The Trotter product on an arbitrary finite pseudometric site set has product form
of range `R` when each term is supported within distance `R` of its centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1024–1077. -/
theorem hasProductForm_trotterProduct_of_dist_le [PseudoMetricSpace ι] {R : ℝ}
    (hR : 0 ≤ R) (H : ι → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, H i ∈ supportedOperators q (X i : Set ι))
    (seq : List ι) (β : ℝ) (n : ℕ) :
    HasProductForm q (fun i j ↦ dist i j ≤ R)
      (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)).prod) ^ n) := by
  exact hasProductForm_trotterProduct_of_radius (fun i ↦ by simpa using hR)
    H X hX hH seq β n

variable {Λ : Finset (ℤ × ℤ)}

/-- The Trotter product `ρₙ = [∏_X exp(-(β / n) H_X)]ⁿ` of a local Hamiltonian, for an ordered
sequence of supports `seq`.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1048–1053. -/
noncomputable def LocalHamiltonian.trotterProduct {R : ℕ} {J : ℝ}
    (h : LocalHamiltonian Λ q R J) (seq : List (AdmissibleSupport Λ R)) (β : ℝ) (n : ℕ) :
    Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  ((seq.map fun X ↦ NormedSpace.exp ((-((β : ℂ) / n)) • h.term X)).prod) ^ n

/-- **Trotter form.** Every Trotter product of a local Hamiltonian of range `R` has a matrix
product form of range `R`, exactly.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077. -/
theorem LocalHamiltonian.hasProductForm_trotterProduct {R : ℕ} {J : ℝ}
    (h : LocalHamiltonian Λ q R J) (seq : List (AdmissibleSupport Λ R)) (β : ℝ) (n : ℕ) :
    HasProductForm q (fun i j : Site Λ ↦
      ∃ p : (domainGraph Λ).Walk i j, p.length ≤ R) (h.trotterProduct seq β n) := by
  refine HasProductForm.pow (hasProductForm_list_prod _ fun ρ hρ ↦ ?_) n
  obtain ⟨X, _, rfl⟩ := List.mem_map.mp hρ
  exact hasProductForm_of_mem_supportedOperators (fun _ ↦ ⟨.nil, Nat.zero_le _⟩) X.2
    (exp_mem_supportedOperators (Submodule.smul_mem _ _ (h.supported X)))

end TNLean.Lattice
