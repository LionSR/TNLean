/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LocalHamiltonian
import TNLean.Lattice.ProductForm.Supported
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

* `TNLean.Lattice.hasProductForm_of_mem_supportedOperators_radius`: an operator supported
  within radius `R` of a specified centre has a product form of range `R`.
* `TNLean.Lattice.hasProductForm_of_mem_supportedOperators`: the diameter-bounded corollary.
* `TNLean.Lattice.HasProductForm.mul`: product forms of a common range are closed under
  multiplication.
* `TNLean.Lattice.hasProductForm_trotterProduct_of_radius`: centre-indexed Trotter products
  preserve the radius bound.
* `TNLean.Lattice.LocalHamiltonian.hasProductForm_trotterProduct`: every Trotter product of a
  local Hamiltonian of range `R` has a product form of range `R`.

The canonical structure is `TNLean.Lattice.Locality.ProductForm`, with arbitrary finite
sites, varying physical dimensions, and prescribed coefficient neighbourhoods. The definitions
here specialize it to walk neighbourhoods and constant physical dimension; no separate product
representation is introduced. The metric theorem and the source's `n S` count are proved in
`TNLean.Lattice.ProductForm.Metric` and `TNLean.Lattice.ProductFormActiveIndices`.
The count assumes each centre occurs once per sweep. An arbitrary list instead counts each
factor occurrence with its multiplicity. No estimate of the error between `ρₙ` and `exp(-β H)`
is asserted by these finite-product results.

The planar restriction and unproved local index count of the separate truncated cluster
expansion remain documented in `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

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
abbrev IsLocalCoefficient (l : ℕ) (i : Site Λ) {A : Type*} (f : (Site Λ → A) → ℂ) : Prop :=
  DependsOn f {j | ∃ p : (domainGraph Λ).Walk i j, p.length ≤ l}

/-- The finite-site product form specialized to a planar domain with walk locality.
Source: Hastings, arXiv:cond-mat/0508554v3, equation `mpf`, lines 1024–1039. -/
abbrev ProductForm (Λ : Finset (ℤ × ℤ)) (q l : ℕ)
    (ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :=
  Locality.ProductForm (fun i ↦ {j | ∃ p : (domainGraph Λ).Walk i j, p.length ≤ l})
    (fun _ ↦ q) ρ

/-- An operator has a matrix product form of range `l`.
Source: Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
abbrev HasProductForm (Λ : Finset (ℤ × ℤ)) (q l : ℕ)
    (ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) : Prop :=
  Nonempty (ProductForm Λ q l ρ)

/-- A coefficient function of range `l` has every larger range. -/
theorem IsLocalCoefficient.mono {l l' : ℕ} (hl : l ≤ l') {i : Site Λ} {A : Type*}
    {f : (Site Λ → A) → ℂ} (hf : IsLocalCoefficient l i f) : IsLocalCoefficient l' i f :=
  fun _ _ h ↦ hf fun j ⟨p, hp⟩ ↦ h j ⟨p, hp.trans hl⟩

/-- A product form of range `l` has every larger range. -/
theorem HasProductForm.mono {l l' : ℕ} (hl : l ≤ l')
    {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ} (hρ : HasProductForm Λ q l ρ) :
    HasProductForm Λ q l' ρ := by
  obtain ⟨P⟩ := hρ
  exact ⟨{ P with coeff_local := fun i ↦ IsLocalCoefficient.mono hl (P.coeff_local i) }⟩

/-- The identity has a product form of every range, with one index value at every site. -/
theorem hasProductForm_one (l : ℕ) : HasProductForm Λ q l 1 :=
  Locality.hasProductForm_one _ _

/-- **Products.** Product forms of range `l` are closed under multiplication: the indices of the
two factors at each site are grouped into one index and the coefficient functions are multiplied.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
theorem HasProductForm.mul {l : ℕ} {ρ σ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : HasProductForm Λ q l ρ) (hσ : HasProductForm Λ q l σ) :
    HasProductForm Λ q l (ρ * σ) :=
  Locality.HasProductForm.mul hρ hσ

/-- Finite ordered products of operators with product forms of range `l` have product forms of
range `l`. -/
theorem hasProductForm_list_prod {l : ℕ}
    (L : List (Matrix (Configuration Λ q) (Configuration Λ q) ℂ))
    (hL : ∀ ρ ∈ L, HasProductForm Λ q l ρ) : HasProductForm Λ q l L.prod :=
  Locality.hasProductForm_list_prod L hL

/-- Powers of an operator with a product form of range `l` have product forms of range `l`. -/
theorem HasProductForm.pow {l : ℕ} {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : HasProductForm Λ q l ρ) (n : ℕ) : HasProductForm Λ q l (ρ ^ n) :=
  Locality.HasProductForm.pow hρ n

/-- An operator supported within walk distance `R` of a specified centre has a product
form of range `R`. The centre need not belong to the support, which may be empty.
The matrix-element coefficient is attached to the centre; diagonal identity factors
are retained at every site off the support, including the centre when necessary.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators_radius {R : ℕ} {X : Finset (Site Λ)}
    (i₀ : Site Λ) (hX : ∀ j ∈ X, ∃ p : (domainGraph Λ).Walk i₀ j, p.length ≤ R)
    {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set (Site Λ))) : HasProductForm Λ q R ρ := by
  apply Locality.hasProductForm_of_isSupportedOn
    (fun i ↦ {j | ∃ p : (domainGraph Λ).Walk i j, p.length ≤ R}) (fun _ ↦ q)
    (fun i ↦ ⟨.nil, Nat.zero_le _⟩) X i₀ hX
  exact ⟨fun u v h ↦ apply_eq_zero_of_mem_supportedOperators hρ h,
    fun _ _ _ _ hux hvy huv hxy ↦ apply_eq_apply_of_mem_supportedOperators hρ hux hvy huv hxy⟩

/-- An operator on a nonempty support of diameter at most `R` has a product form of
range `R`, by choosing any site of the support as its centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061, specialized to such supports. -/
theorem hasProductForm_of_mem_supportedOperators {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : ρ ∈ supportedOperators q (X : Set (Site Λ))) : HasProductForm Λ q R ρ := by
  obtain ⟨i₀, hi₀⟩ := hX.1
  exact hasProductForm_of_mem_supportedOperators_radius i₀ (hX.2 i₀ hi₀) hρ

/-- Trotter products of centre-indexed operators supported within radius `R` have a
product form of range `R`. No diameter bound, nonempty support, or Hermiticity is needed.
At zero steps the product is the identity. This is the finite planar-domain case of
Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077; no index-component count is asserted. -/
theorem hasProductForm_trotterProduct_of_radius {R : ℕ}
    (H : Site Λ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (X : Site Λ → Finset (Site Λ))
    (hX : ∀ i j, j ∈ X i → ∃ p : (domainGraph Λ).Walk i j, p.length ≤ R)
    (hH : ∀ i, H i ∈ supportedOperators q (X i : Set (Site Λ)))
    (seq : List (Site Λ)) (β : ℝ) (n : ℕ) :
    HasProductForm Λ q R
      (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)).prod) ^ n) := by
  refine HasProductForm.pow (hasProductForm_list_prod _ fun ρ hρ ↦ ?_) n
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hρ
  exact hasProductForm_of_mem_supportedOperators_radius i (hX i)
    (exp_mem_supportedOperators (Submodule.smul_mem _ _ (hH i)))

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
