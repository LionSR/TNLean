/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Sites.Placement
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Product operators on sets of sites

On a finite type of sites `ι` with local dimension `d`, the operators acting on a set of sites
`S` are `ManyBody.supportedOperators (fun _ ↦ Fin d) S`, the operators that act as the identity
off `S`; the product operators `⊗ᵢ mᵢ` with `mᵢ = 1` off `S` lie in it by QICLean's
`ManyBody.piKronecker_mem_supportedOperators`. This file proves that linear maps agreeing on the
product operators are equal, and the factorization of traces against product operators for
operators on disjoint sets.

The expectations `star ψ ⬝ᵥ (A *ᵥ ψ)` in product vectors, and their factorization for
operators on disjoint sets, are in QICLean's `QICLean.ManyBody.Sites.ProductVector`
(`QuantumCircuit.star_productVector_dotProduct_piKronecker_mulVec`) and
`QICLean.Circuit.Model.Unitary` (`QuantumCircuit.dotProduct_prod_mul_mul`). No layer, gate or
circuit occurs here: the circuits built from supported operators are in QICLean's
`QICLean.Circuit.Model.Unitary`.

## Main results

* `QuantumCircuit.linearMap_ext_rectKronecker` — linear maps on the operators of the sites
  agree once they agree on the product operators.
* `QuantumCircuit.trace_rectKronecker_mul_mul` — product densities factorize traces of
  products of operators on disjoint sets.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), Supplemental Material, proof of Theorem 1.
-/
open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Product operators -/

omit [DecidableEq ι] in
/-- Two linear maps on the operators of the sites `ι` agree once they agree on the product
operators `⊗ᵢ mᵢ`. -/
theorem linearMap_ext_rectKronecker {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (Φ Ψ : Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] M)
    (h : ∀ m : ι → Matrix (Fin d) (Fin d) ℂ, Φ (Matrix.piKronecker m) = Ψ (Matrix.piKronecker m)) :
    Φ = Ψ := by
  classical
  apply LinearMap.ext
  intro X
  have hX : X ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Finset.univ := by simp
  induction hX using ManyBody.supportedOperators_induction with
  | prod m _ => exact h m
  | add A B _ _ hA hB => rw [map_add, map_add, hA, hB]
  | smul c A _ hA => rw [map_smul, map_smul, hA]

/-! ### Traces against product operators -/

/-- Product densities factorize expectations of products of operators on disjoint sets of
sites: `tr(σ AB) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗ᵢ σᵢ`. -/
theorem trace_rectKronecker_mul_mul {S S' : Finset ι} (hSS' : Disjoint S S')
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S') :
    trace (Matrix.piKronecker σ * (A * B)) * trace (Matrix.piKronecker σ) =
      trace (Matrix.piKronecker σ * A) * trace (Matrix.piKronecker σ * B) := by
  let φ := traceLinearMap (ι → Fin d) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (Matrix.piKronecker σ)
  rw [mul_comm]
  refine ManyBody.eq_of_mem_supportedOperators₂
    (trace (Matrix.piKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (Matrix.piKronecker σ) * trace (Matrix.piKronecker σ * (Matrix.piKronecker m *
      Matrix.piKronecker m')) =
    trace (Matrix.piKronecker σ * Matrix.piKronecker m) * trace (Matrix.piKronecker σ *
        Matrix.piKronecker m')
  simp only [Matrix.piKronecker_mul, Matrix.trace_piKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Finset.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

end QuantumCircuit
