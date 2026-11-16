/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.Circuit.ProductVector
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Operators supported on a set of sites

On a finite type of sites `ι` with local dimension `d`, an operator acts on a set of sites `S`
when it lies in the complex span of the product operators `⊗ᵢ mᵢ` with `mᵢ = 1` for every
`i ∉ S`; this span is the algebraic tensor product `M_d^{⊗ S} ⊗ 1`. This file defines these
operators and proves their closure under products and adjoints, the commutation of operators
on disjoint sets, and the factorization of expectations in product vectors and of traces
against product operators.

No layer, gate or circuit occurs here: the circuits built from supported operators are in
`TNLean.Circuit.LocalCircuit`.

## Main definitions

* `QuantumCircuit.supportedOperators` — operators acting on a set of sites.
* `QuantumCircuit.expect` — the expectation `⟨ψ|A|ψ⟩`, without normalization.

## Main results

* `QuantumCircuit.mul_mem_supportedOperators`, `QuantumCircuit.star_mem_supportedOperators`.
* `QuantumCircuit.commute_of_mem_supportedOperators` — operators on disjoint sets commute.
* `QuantumCircuit.expect_productVector_mul` — product vectors factorize expectations of
  products of operators on disjoint sets.
* `QuantumCircuit.trace_rectKronecker_mul_mul` — the same for traces against a product
  operator.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), Supplemental Material, proof of Theorem 1.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Product operators and support -/

/-- The operators acting on the set of sites `S`: the complex span of the product operators
`⊗ᵢ mᵢ` with `mᵢ = 1` off `S`, that is, `M_d^{⊗ S} ⊗ 1`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (operators `𝒪₁`, `𝒪'ₛ`
acting on sites of the chain). -/
def supportedOperators (d : ℕ) (S : Set ι) :
    Submodule ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  Submodule.span ℂ {A | ∃ m : ι → Matrix (Fin d) (Fin d) ℂ,
    (∀ i ∉ S, m i = 1) ∧ A = rectKronecker m}

omit [DecidableEq ι] in
/-- A product operator `⊗ᵢ mᵢ` acts on `S` when `mᵢ = 1` for every site `i ∉ S`. -/
theorem rectKronecker_mem_supportedOperators {S : Set ι}
    {m : ι → Matrix (Fin d) (Fin d) ℂ} (hm : ∀ i ∉ S, m i = 1) :
    rectKronecker m ∈ supportedOperators d S :=
  Submodule.subset_span ⟨m, hm, rfl⟩

/-- The chain form of `rectKronecker_mem_supportedOperators`, for the sites `Fin N`. -/
theorem finKronecker_mem_supportedOperators {N : ℕ} {S : Set (Fin N)}
    {m : Fin N → Matrix (Fin d) (Fin d) ℂ} (hm : ∀ i ∉ S, m i = 1) :
    finKronecker m ∈ supportedOperators d S :=
  rectKronecker_mem_supportedOperators hm

omit [DecidableEq ι] in
theorem supportedOperators_mono {S S' : Set ι} (h : S ⊆ S') :
    supportedOperators d S ≤ supportedOperators d S' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, fun i hi ↦ hm i fun hiS ↦ hi (h hiS), rfl⟩

omit [DecidableEq ι] in
theorem one_mem_supportedOperators (S : Set ι) :
    (1 : Matrix (ι → Fin d) (ι → Fin d) ℂ) ∈ supportedOperators d S := by
  rw [← rectKronecker_one]
  exact rectKronecker_mem_supportedOperators fun _ _ ↦ rfl

theorem mul_mem_supportedOperators {S : Set ι}
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators d S) :
    A * B ∈ supportedOperators d S := by
  have hAB := Submodule.mul_mem_mul hA hB
  rw [supportedOperators, Submodule.span_mul_span] at hAB
  refine Submodule.span_le.mpr ?_ hAB
  rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨m', hm', rfl⟩, rfl⟩
  change rectKronecker m * rectKronecker m' ∈ _
  rw [rectKronecker_mul]
  exact rectKronecker_mem_supportedOperators fun i hi ↦ by simp [hm i hi, hm' i hi]

omit [DecidableEq ι] in
theorem star_mem_supportedOperators {S : Set ι} {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) : star A ∈ supportedOperators d S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [star_eq_conjTranspose, rectKronecker_conjTranspose]
    exact rectKronecker_mem_supportedOperators fun i hi ↦ by simp [hm i hi]
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

omit [DecidableEq ι] in
/-- Two bilinear maps agree on every pair of an operator acting on `S` and an operator acting
on `S'` once they agree on the pairs of product operators `⊗ᵢ mᵢ`, `⊗ᵢ m'ᵢ` with `mᵢ = 1` off
`S` and `m'ᵢ = 1` off `S'`. -/
theorem eq_of_mem_supportedOperators₂ {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {S S' : Set ι}
    (f g : Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] M)
    (h : ∀ m m' : ι → Matrix (Fin d) (Fin d) ℂ, (∀ i ∉ S, m i = 1) → (∀ i ∉ S', m' i = 1) →
      f (rectKronecker m) (rectKronecker m') = g (rectKronecker m) (rectKronecker m'))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d S)
    (hB : B ∈ supportedOperators d S') : f A B = g A B := by
  have hgen : ∀ m, (∀ i ∉ S, m i = 1) → f (rectKronecker m) B = g (rectKronecker m) B :=
    fun m hm ↦ LinearMap.eqOn_span' (by rintro _ ⟨m', hm', rfl⟩; exact h m m' hm hm') hB
  exact LinearMap.eqOn_span' (f := f.flip B) (g := g.flip B)
    (by rintro _ ⟨m, hm, rfl⟩; exact hgen m hm) hA

/-- Operators acting on disjoint sets of sites commute. -/
theorem commute_of_mem_supportedOperators {S S' : Set ι} (hSS' : Disjoint S S')
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d S)
    (hB : B ∈ supportedOperators d S') : Commute A B := by
  refine eq_of_mem_supportedOperators₂ (LinearMap.mul ℂ _) (LinearMap.mul ℂ _).flip
    (fun m m' hm hm' ↦ ?_) hA hB
  change rectKronecker m * rectKronecker m' = rectKronecker m' * rectKronecker m
  rw [rectKronecker_mul, rectKronecker_mul]
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [hm' i (Set.disjoint_left.mp hSS' hi)]
  · simp [hm i hi]

/-! ### Expectations in product vectors -/

/-- The expectation `⟨ψ|A|ψ⟩` of an operator on the sites `ι`, without normalization.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1
(`b_Q = ⟨ψ|Q|ψ⟩`). -/
def expect (ψ : (ι → Fin d) → ℂ) (A : Matrix (ι → Fin d) (ι → Fin d) ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)

theorem expect_add (ψ : (ι → Fin d) → ℂ) (A B : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    expect ψ (A + B) = expect ψ A + expect ψ B := by
  simp [expect, add_mulVec, dotProduct_add]

theorem expect_smul (ψ : (ι → Fin d) → ℂ) (c : ℂ)
    (A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    expect ψ (c • A) = c * expect ψ A := by
  simp [expect, smul_mulVec, dotProduct_smul]

theorem expect_one (ψ : (ι → Fin d) → ℂ) :
    expect ψ (1 : Matrix (ι → Fin d) (ι → Fin d) ℂ) = star ψ ⬝ᵥ ψ := by
  simp [expect]

/-- Expectations in `U ψ` are expectations of `U† A U` in `ψ`. -/
theorem expect_mulVec (U A : Matrix (ι → Fin d) (ι → Fin d) ℂ) (ψ : (ι → Fin d) → ℂ) :
    expect (U *ᵥ ψ) A = expect ψ (star U * A * U) := by
  simp only [expect, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, star_eq_conjTranspose,
    Matrix.mul_assoc]

/-- The expectation of a product operator `⊗ᵢ mᵢ` in a product vector `⊗ᵢ |vᵢ⟩` is
`∏ᵢ ⟨vᵢ|mᵢ|vᵢ⟩`. -/
theorem expect_productVector_rectKronecker (v : ι → Fin d → ℂ)
    (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    expect (productVector v) (rectKronecker m) = ∏ i, star (v i) ⬝ᵥ (m i *ᵥ v i) := by
  simp only [expect, productVector, rectKronecker, dotProduct, mulVec, of_apply, Pi.star_apply,
    star_prod, Finset.mul_sum]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Product vectors factorize expectations of products of operators on disjoint sets of
sites: `⟨AB⟩⟨1⟩ = ⟨A⟩⟨B⟩`. -/
theorem expect_productVector_mul {S S' : Set ι} (hSS' : Disjoint S S')
    (v : ι → Fin d → ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators d S') :
    expect (productVector v) (A * B) * expect (productVector v) 1 =
      expect (productVector v) A * expect (productVector v) B := by
  let φ : Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := expect (productVector v), map_add' := expect_add _, map_smul' := expect_smul _ }
  rw [mul_comm]
  refine eq_of_mem_supportedOperators₂ (expect (productVector v) 1 • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change expect (productVector v) 1 *
      expect (productVector v) (rectKronecker m * rectKronecker m') =
    expect (productVector v) (rectKronecker m) * expect (productVector v) (rectKronecker m')
  rw [rectKronecker_mul, ← rectKronecker_one, expect_productVector_rectKronecker,
    expect_productVector_rectKronecker, expect_productVector_rectKronecker,
    expect_productVector_rectKronecker, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Set.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

/-! ### Traces against product operators -/

theorem _root_.Matrix.trace_rectKronecker (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    trace (rectKronecker m) = ∏ i, trace (m i) := by
  simp only [trace, diag_apply, rectKronecker_apply]
  exact (Fintype.prod_sum fun i j ↦ m i j j).symm

/-- Product densities factorize expectations of products of operators on disjoint sets of
sites: `tr(σ AB) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗ᵢ σᵢ`. -/
theorem trace_rectKronecker_mul_mul {S S' : Set ι} (hSS' : Disjoint S S')
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators d S') :
    trace (rectKronecker σ * (A * B)) * trace (rectKronecker σ) =
      trace (rectKronecker σ * A) * trace (rectKronecker σ * B) := by
  let φ := traceLinearMap (ι → Fin d) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (rectKronecker σ)
  rw [mul_comm]
  refine eq_of_mem_supportedOperators₂ (trace (rectKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (rectKronecker σ) * trace (rectKronecker σ * (rectKronecker m * rectKronecker m')) =
    trace (rectKronecker σ * rectKronecker m) * trace (rectKronecker σ * rectKronecker m')
  simp only [rectKronecker_mul, trace_rectKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Set.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

end QuantumCircuit
