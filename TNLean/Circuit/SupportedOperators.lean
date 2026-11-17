/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.Circuit.ProductVector
import QICLean.ManyBody.Sites.Placement
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Product operators and expectations on sets of sites

On a finite type of sites `ι` with local dimension `d`, the operators acting on a set of sites
`S` are `ManyBody.supportedOperators (fun _ ↦ Fin d) S`, the operators that act as the identity
off `S`. This file places the product operators `⊗ᵢ mᵢ` with `mᵢ = 1` off `S` in it, and proves
the factorization of expectations in product vectors and of traces against product operators
for operators on disjoint sets.

No layer, gate or circuit occurs here: the circuits built from supported operators are in
`TNLean.Circuit.LocalCircuit`.

## Main definitions

* `QuantumCircuit.expect` — the expectation `⟨ψ|A|ψ⟩`, without normalization.

## Main results

* `QuantumCircuit.rectKronecker_mem_supportedOperators` — product operators that are the
  identity off `S` act on `S`.
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

/-! ### Product operators -/

/-- On sites of local dimension `d`, the product operator `⊗ᵢ mᵢ` of the many-body system is
`rectKronecker m`. -/
theorem prodOp_eq_rectKronecker (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    ManyBody.prodOp (X := fun _ : ι ↦ Fin d) m = rectKronecker m :=
  rfl

/-- A product operator `⊗ᵢ mᵢ` acts on `S` when `mᵢ = 1` for every site `i ∉ S`. -/
theorem rectKronecker_mem_supportedOperators {S : Finset ι}
    {m : ι → Matrix (Fin d) (Fin d) ℂ} (hm : ∀ i ∉ S, m i = 1) :
    rectKronecker m ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  ManyBody.prodOp_mem_supportedOperators hm

/-- The chain form of `rectKronecker_mem_supportedOperators`, for the sites `Fin N`. -/
theorem finKronecker_mem_supportedOperators {N : ℕ} {S : Finset (Fin N)}
    {m : Fin N → Matrix (Fin d) (Fin d) ℂ} (hm : ∀ i ∉ S, m i = 1) :
    finKronecker m ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  rectKronecker_mem_supportedOperators hm

/-- Two linear maps on the operators of the sites `ι` agree once they agree on the product
operators `⊗ᵢ mᵢ`. -/
theorem linearMap_ext_rectKronecker {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (Φ Ψ : Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] M)
    (h : ∀ m : ι → Matrix (Fin d) (Fin d) ℂ, Φ (rectKronecker m) = Ψ (rectKronecker m)) :
    Φ = Ψ := by
  apply LinearMap.ext
  intro X
  have hX : X ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Finset.univ := by simp
  induction hX using ManyBody.supportedOperators_induction with
  | prod m _ => exact h m
  | add A B _ _ hA hB => rw [map_add, map_add, hA, hB]
  | smul c A _ hA => rw [map_smul, map_smul, hA]

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
theorem expect_productVector_mul {S S' : Finset ι} (hSS' : Disjoint S S')
    (v : ι → Fin d → ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S') :
    expect (productVector v) (A * B) * expect (productVector v) 1 =
      expect (productVector v) A * expect (productVector v) B := by
  let φ : Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := expect (productVector v), map_add' := expect_add _, map_smul' := expect_smul _ }
  rw [mul_comm]
  refine ManyBody.eq_of_mem_supportedOperators₂
    (expect (productVector v) 1 • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change expect (productVector v) 1 *
      expect (productVector v) (rectKronecker m * rectKronecker m') =
    expect (productVector v) (rectKronecker m) * expect (productVector v) (rectKronecker m')
  rw [rectKronecker_mul, ← rectKronecker_one, expect_productVector_rectKronecker,
    expect_productVector_rectKronecker, expect_productVector_rectKronecker,
    expect_productVector_rectKronecker, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Finset.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

/-! ### Traces against product operators -/

theorem _root_.Matrix.trace_rectKronecker (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    trace (rectKronecker m) = ∏ i, trace (m i) := by
  simp only [trace, diag_apply, rectKronecker_apply]
  exact (Fintype.prod_sum fun i j ↦ m i j j).symm

/-- Product densities factorize expectations of products of operators on disjoint sets of
sites: `tr(σ AB) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗ᵢ σᵢ`. -/
theorem trace_rectKronecker_mul_mul {S S' : Finset ι} (hSS' : Disjoint S S')
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S') :
    trace (rectKronecker σ * (A * B)) * trace (rectKronecker σ) =
      trace (rectKronecker σ * A) * trace (rectKronecker σ * B) := by
  let φ := traceLinearMap (ι → Fin d) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (rectKronecker σ)
  rw [mul_comm]
  refine ManyBody.eq_of_mem_supportedOperators₂
    (trace (rectKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (rectKronecker σ) * trace (rectKronecker σ * (rectKronecker m * rectKronecker m')) =
    trace (rectKronecker σ * rectKronecker m) * trace (rectKronecker σ * rectKronecker m')
  simp only [rectKronecker_mul, trace_rectKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Finset.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

end QuantumCircuit
