/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LocalHamiltonian
import TNLean.Circuit.SupportedMatrixElements
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Matrix product form of operators and of Trotter products

Hastings writes the thermal density matrix in the matrix product form of eq. `mpf`:
`ρ = ∑_{α} ρ₁(α₁) ρ₂(α₂) ⋯ F₁(α) F₂(α) ⋯`, where each site `i` carries an index `αᵢ`, each
`ρᵢ(αᵢ)` acts only on site `i`, and each function `Fᵢ` depends only on the indices `αⱼ` with
`d(i, j) ≤ l`. He then observes that every Trotter product
`ρₙ = [∏ᵢ exp(-β Hᵢ / n)]ⁿ`, taken over any sequence of interaction terms, can be written exactly
in this form with range `R`: each factor `exp(-β Hᵢ / n)` is a sum of products of single-site
operators near `i` with one coefficient function, and the indices of all factors at a site are
grouped into one index, with the coefficient functions multiplied.

## Correspondence with eq. `mpf`

`TNLean.Lattice.ProductForm Λ q l ρ` records the data of eq. `mpf` for an operator `ρ` on the
configurations of a finite domain `Λ`: one finite index type `Index`, a single-site operator
`siteOp j a` for every site `j` and index value `a`, and a coefficient function `coeff i` for
every site `i`, depending only on the indices at sites joined to `i` in the domain by a walk of
length at most `l` (the distance used for the supports of `TNLean.Lattice.LocalHamiltonian`).
The product `ρ₁(α₁) ρ₂(α₂) ⋯` of operators on distinct sites is the site-wise Kronecker product
`Matrix.rectKronecker`. The index type is the same at every site; this loses nothing, since
indices of a smaller site can be padded with values on which the coefficient vanishes.

## Main definitions

* `TNLean.Lattice.ProductForm`: the data of eq. `mpf` for an operator.
* `TNLean.Lattice.HasProductForm`: an operator admits such data.
* `TNLean.Lattice.LocalHamiltonian.trotterProduct`: the Trotter product `ρₙ`.

## Main results

* `TNLean.Lattice.hasProductForm_of_mem_supportedOperators`: an operator supported on an
  admissible support of range `R` has a product form of range `R`.
* `TNLean.Lattice.HasProductForm.mul`: product forms of a common range are closed under
  multiplication.
* `TNLean.Lattice.LocalHamiltonian.hasProductForm_trotterProduct`: every Trotter product of a
  local Hamiltonian of range `R` has a product form of range `R`.

The error between `ρₙ` and `exp(-β H)` is not estimated here, and neither is the source's
count of at most `n S` indices per site (lines 1069–1075): every factor is expanded in
single-site matrix units at every site, so a product of `m` factors carries `(q²)^m` index
values at each site.

**Scope restriction (planar domains):** the source works on an arbitrary lattice with a metric;
this file states the product form for finite domains `Λ ⊆ ℤ²` with the walk distance of
`TNLean.Lattice.LocalHamiltonian`, and does not establish the index count. Documented in
`docs/paper-gaps/hastings05_planar_domain_scope.tex`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, Section IV,
  eq. `mpf` (lines 1024–1046) and the Trotter decomposition (lines 1048–1079).
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

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- A coefficient function at site `i` that reads only the indices at sites joined to `i` by a
walk of length at most `l` in the domain.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1037–1039. -/
def IsLocalCoefficient (l : ℕ) (i : Site Λ) {A : Type*} (f : (Site Λ → A) → ℂ) : Prop :=
  ∀ α β : Site Λ → A,
    (∀ j, (∃ p : (domainGraph Λ).Walk i j, p.length ≤ l) → α j = β j) → f α = f β

/-- **Matrix product form.** The data of eq. `mpf`: an index type, single-site operators
`siteOp j a`, and coefficient functions `coeff i` of range `l`, with
`ρ = ∑_α (∏ᵢ coeff i α) • ⊗ⱼ siteOp j (α j)`.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
structure ProductForm (Λ : Finset (ℤ × ℤ)) (q l : ℕ)
    (ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) where
  /-- The values of the index carried by each site. -/
  Index : Type
  /-- The index takes finitely many values. -/
  [fintype : Fintype Index]
  /-- The operator `ρⱼ(a)` acting only on site `j`. -/
  siteOp : Site Λ → Index → Matrix (Fin q) (Fin q) ℂ
  /-- The coefficient function `Fᵢ` attached to site `i`. -/
  coeff : Site Λ → (Site Λ → Index) → ℂ
  /-- Each `Fᵢ` depends only on the indices at distance at most `l` from `i`. -/
  coeff_local : ∀ i, IsLocalCoefficient l i (coeff i)
  /-- The expansion of eq. `mpf`. -/
  eq_sum : ρ = ∑ α : Site Λ → Index, (∏ i, coeff i α) • rectKronecker fun j ↦ siteOp j (α j)

attribute [instance] ProductForm.fintype

/-- An operator has a matrix product form of range `l`.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
def HasProductForm (Λ : Finset (ℤ × ℤ)) (q l : ℕ)
    (ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) : Prop :=
  Nonempty (ProductForm Λ q l ρ)

/-- A coefficient function of range `l` has every larger range. -/
theorem IsLocalCoefficient.mono {l l' : ℕ} (hl : l ≤ l') {i : Site Λ} {A : Type*}
    {f : (Site Λ → A) → ℂ} (hf : IsLocalCoefficient l i f) : IsLocalCoefficient l' i f :=
  fun α β h ↦ hf α β fun j ⟨p, hp⟩ ↦ h j ⟨p, hp.trans hl⟩

/-- A product form of range `l` has every larger range. -/
theorem HasProductForm.mono {l l' : ℕ} (hl : l ≤ l')
    {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ} (hρ : HasProductForm Λ q l ρ) :
    HasProductForm Λ q l' ρ := by
  obtain ⟨P⟩ := hρ
  exact ⟨{ P with coeff_local := fun i ↦ (P.coeff_local i).mono hl }⟩

/-- The identity has a product form of every range, with one index value at every site. -/
theorem hasProductForm_one (l : ℕ) : HasProductForm Λ q l 1 :=
  ⟨{ Index := Unit
     siteOp := fun _ _ ↦ 1
     coeff := fun _ _ ↦ 1
     coeff_local := fun _ _ _ _ ↦ rfl
     eq_sum := by simp }⟩

/-- **Products.** Product forms of range `l` are closed under multiplication: the indices of the
two factors at each site are grouped into one index and the coefficient functions are multiplied.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
theorem HasProductForm.mul {l : ℕ} {ρ σ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : HasProductForm Λ q l ρ) (hσ : HasProductForm Λ q l σ) :
    HasProductForm Λ q l (ρ * σ) := by
  obtain ⟨P⟩ := hρ
  obtain ⟨Q⟩ := hσ
  refine ⟨{ Index := P.Index × Q.Index
            siteOp := fun j a ↦ P.siteOp j a.1 * Q.siteOp j a.2
            coeff := fun i γ ↦ P.coeff i (fun j ↦ (γ j).1) * Q.coeff i (fun j ↦ (γ j).2)
            coeff_local := fun i α β h ↦ ?_
            eq_sum := ?_ }⟩
  · dsimp only
    rw [P.coeff_local i _ _ fun j hj ↦ congrArg Prod.fst (h j hj),
      Q.coeff_local i _ _ fun j hj ↦ congrArg Prod.snd (h j hj)]
  · refine (congrArg₂ (· * ·) P.eq_sum Q.eq_sum).trans ?_
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun x ↦ ?_
    simp [rectKronecker_mul, Finset.prod_mul_distrib, Equiv.arrowProdEquivProdArrow, smul_smul,
      mul_comm]

/-- Finite ordered products of operators with product forms of range `l` have product forms of
range `l`. -/
theorem hasProductForm_list_prod {l : ℕ}
    (L : List (Matrix (Configuration Λ q) (Configuration Λ q) ℂ))
    (hL : ∀ ρ ∈ L, HasProductForm Λ q l ρ) : HasProductForm Λ q l L.prod := by
  induction L with
  | nil => exact hasProductForm_one l
  | cons ρ L ih =>
    rw [List.prod_cons]
    exact (hL ρ (by simp)).mul (ih fun σ hσ ↦ hL σ (by simp [hσ]))

/-- Powers of an operator with a product form of range `l` have product forms of range `l`. -/
theorem HasProductForm.pow {l : ℕ} {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : HasProductForm Λ q l ρ) (n : ℕ) : HasProductForm Λ q l (ρ ^ n) := by
  induction n with
  | zero => simpa using hasProductForm_one l
  | succ n ih => simpa [pow_succ] using ih.mul hρ

/-- **Supported operators.** An operator supported on an admissible support of range `R` has a
product form of range `R`. It is expanded in single-site matrix units; the coefficient of a
configuration pair is attached to one site of the support, and every site off the support
carries the coefficient forcing equal row and column labels.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set (Site Λ))) : HasProductForm Λ q R ρ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hX.1
  /- The configurations read off the indices: their labels on `X`, and one common label
  (the row label at `i₀`) off `X`. -/
  let row : (Site Λ → Fin q × Fin q) → Configuration Λ q :=
    fun α j ↦ if j ∈ X then (α j).1 else (α i₀).1
  let col : (Site Λ → Fin q × Fin q) → Configuration Λ q :=
    fun α j ↦ if j ∈ X then (α j).2 else (α i₀).1
  refine ⟨{ Index := Fin q × Fin q
            siteOp := fun _ a ↦ single a.1 a.2 1
            coeff := fun i α ↦ (if i = i₀ then ρ (row α) (col α) else 1) *
              if i ∈ X then 1 else if (α i).1 = (α i).2 then 1 else 0
            coeff_local := fun i α β h ↦ ?_
            eq_sum := ?_ }⟩
  · have hnil : α i = β i := h i ⟨.nil, Nat.zero_le _⟩
    by_cases hi : i = i₀
    · subst hi
      have hrow : row α = row β := funext fun j ↦ by
        simp only [row]
        split_ifs with hj
        · rw [h j (hX.2 i hi₀ j hj)]
        · rw [hnil]
      have hcol : col α = col β := funext fun j ↦ by
        simp only [col]
        split_ifs with hj
        · rw [h j (hX.2 i hi₀ j hj)]
        · rw [hnil]
      simp only [hrow, hcol, hnil]
    · simp [hi, hnil]
  · ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, rectKronecker_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (fun j ↦ (u j, v j))]
    · simp only [single_apply_same, Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
        Fintype.prod_ite_eq']
      by_cases hoff : ∃ j ∉ (X : Set (Site Λ)), u j ≠ v j
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
    HasProductForm Λ q R (h.trotterProduct seq β n) := by
  refine HasProductForm.pow (hasProductForm_list_prod _ fun ρ hρ ↦ ?_) n
  obtain ⟨X, _, rfl⟩ := List.mem_map.mp hρ
  exact hasProductForm_of_mem_supportedOperators X.2
    (exp_mem_supportedOperators (Submodule.smul_mem _ _ (h.supported X)))

end TNLean.Lattice
