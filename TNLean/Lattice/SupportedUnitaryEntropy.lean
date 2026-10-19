/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixKroneckerContraction
import TNLean.Lattice.EntropyComparison
import TNLean.Lattice.RegionSplit

/-!
# The entropy comparison for a unitary acting away from two regions

Let `U` be a unitary acting on a set `S` of sites disjoint from two regions `X` and `J`, and let
`η` be a unit vector with `I_η(X : J) = 0`. In the coordinates of `X ∪ J` and its complement,
`U` is `1 ⊗ U₂`, so every unit vector `φ` satisfies `I_φ(X : J) ≤ 8 √‖U φ - η‖ log(e dim X)`.
Only the dimension of `X` enters, and nothing depends on a geometry of the sites.

## Main statements

* `TNLean.Lattice.exists_one_kronecker_unitary_of_mem_supportedOperators`: a unitary acting
  away from `X` is `1 ⊗ U₂` with `U₂` unitary.
* `TNLean.Lattice.mutualInformation_le_of_supported_unitary`: the entropy comparison.
* `TNLean.Lattice.mutualInformation_le_inv_pow_of_supported_unitary`: its polynomial scale.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 547–561, and `02-information.tex`, lines 600–630.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **A unitary acting away from a region.** Let `U` be a unitary acting on a set `S` disjoint
from a region `X`, on a nonempty configuration space. Then `U = 1 ⊗ U₂` in the coordinates of
`X` and its complement, for a unitary `U₂` on the complement.
Source: `09-amplification.tex`, lines 547–550. -/
theorem exists_one_kronecker_unitary_of_mem_supportedOperators [Nonempty (ι → Fin q)]
    {X S : Finset ι} (hS : Disjoint (S : Set ι) (X : Set ι))
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hU : U ∈ supportedOperators q (S : Set ι))
    (hUu : Uᴴ * U = 1) :
    ∃ U₂ : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) Xᶜ)
        (FiniteProduct.Configuration (fun _ : ι => Fin q) Xᶜ) ℂ,
      U = ((1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) X)
        (FiniteProduct.Configuration (fun _ : ι => Fin q) X) ℂ) ⊗ₖ U₂).submatrix
          (FiniteProduct.splitEquiv (fun _ : ι => Fin q) X)
          (FiniteProduct.splitEquiv (fun _ : ι => Fin q) X) ∧ U₂ᴴ * U₂ = 1 := by
  obtain ⟨U₂, hU₂⟩ := exists_one_kronecker_of_mem_supportedOperators hS hU
  set e := FiniteProduct.splitEquiv (fun _ : ι => Fin q) X with he
  have hUeq : U = ((1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) X)
      (FiniteProduct.Configuration (fun _ : ι => Fin q) X) ℂ) ⊗ₖ U₂).submatrix e e := by
    rw [← hU₂]
    simp [e]
  refine ⟨U₂, hUeq, ?_⟩
  have h1 : ((1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) X)
      (FiniteProduct.Configuration (fun _ : ι => Fin q) X) ℂ) ⊗ₖ
        (U₂ᴴ * U₂)).submatrix e e = 1 := by
    rw [← hUu, hUeq, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  have h2 : (1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) X)
      (FiniteProduct.Configuration (fun _ : ι => Fin q) X) ℂ) ⊗ₖ (U₂ᴴ * U₂) = 1 := by
    simpa using congrArg (fun A => A.submatrix e.symm e.symm) h1
  obtain ⟨c⟩ := ‹Nonempty (ι → Fin q)›
  ext i j
  have hij := congrFun (congrFun h2 ((e c).1, i)) ((e c).1, j)
  simpa [kroneckerMap_apply, one_apply] using hij

/-- A unit vector lives on a nonempty configuration space. -/
theorem nonempty_of_norm_eq_one {φ : EuclideanSpace ℂ (ι → Fin q)} (hφ : ‖φ‖ = 1) :
    Nonempty (ι → Fin q) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hz : φ = 0 := by
    ext c
    exact (IsEmpty.false c).elim
  rw [hz, norm_zero] at hφ
  exact zero_ne_one hφ

/-- **The entropy comparison for a unitary acting away from both regions.** Let `U` be a
unitary acting on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. Every unit vector `φ` then satisfies
`I_φ(X : J) ≤ 8 √‖U φ - η‖ log(e dim X)`. Only the dimension of `X` enters.
Source: `09-amplification.tex`, lines 547–555, and `02-information.tex`, lines 600–630. -/
theorem mutualInformation_le_of_supported_unitary
    {φ η : EuclideanSpace ℂ (ι → Fin q)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset ι} (hXJ : Disjoint X J) (hS : Disjoint (S : Set ι) ((X ∪ J : Finset ι) :
      Set ι)) {U : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hU : U ∈ supportedOperators q (S : Set ι))
    (hUu : Uᴴ * U = 1)
    (hprod : FiniteProduct.mutualInformation (fun _ : ι => Fin q) η X J = 0) :
    FiniteProduct.mutualInformation (fun _ : ι => Fin q) φ X J ≤
      8 * √‖WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) - η‖ *
        Real.log (Real.exp 1 *
          Fintype.card (FiniteProduct.Configuration (fun _ : ι => Fin q) X)) := by
  have := nonempty_of_norm_eq_one hφ
  obtain ⟨U₂, hUeq, hU₂u⟩ := exists_one_kronecker_unitary_of_mem_supportedOperators hS hU hUu
  have h := FiniteProduct.mutualInformation_le_of_unitary_sub_le (fun _ : ι => Fin q) hφ hη
    hXJ U₂ hU₂u hprod
  have hφ' : toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ) U φ =
      WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) := by
    rw [← toEuclideanCLM_toLp, WithLp.toLp_ofLp]
  rw [← hUeq, hφ'] at h
  exact h

/-- **The entropy comparison for a unitary acting away from both regions.** Let `U` be a
unitary acting on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. If `‖U φ - η‖ ≤ C₁ n^(-K/2)` with `K ≥ 4(M + 2)` and `log dim X ≤ C₂ n²`,
then every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` with `J` in
the unit vector `φ`. Source: `09-amplification.tex`, lines 547–561. -/
theorem mutualInformation_le_inv_pow_of_supported_unitary
    {φ η : EuclideanSpace ℂ (ι → Fin q)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset ι} (hXJ : Disjoint X J) (hS : Disjoint (S : Set ι) ((X ∪ J : Finset ι) :
      Set ι)) {U : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hU : U ∈ supportedOperators q (S : Set ι))
    (hUu : Uᴴ * U = 1)
    (hprod : FiniteProduct.mutualInformation (fun _ : ι => Fin q) η X J = 0)
    {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) - η‖ ≤ C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : Real.log (Fintype.card (FiniteProduct.Configuration (fun _ : ι => Fin q) X)) ≤
      C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, FiniteProduct.mutualInformation (fun _ : ι => Fin q) φ X' J ≤
      8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  have := nonempty_of_norm_eq_one hφ
  obtain ⟨U₂, hUeq, hU₂u⟩ := exists_one_kronecker_unitary_of_mem_supportedOperators hS hU hUu
  have t1 := FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le (fun _ : ι => Fin q)
    hφ hη hXJ U₂
  have t2 := t1 hU₂u hprod (C₁ := C₁) (C₂ := C₂) hn hK
  refine t2 ?_ hdim
  have hφ' : toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ) U φ =
      WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) := by
    rw [← toEuclideanCLM_toLp, WithLp.toLp_ofLp]
  rw [← hUeq, hφ']
  exact hδ

end TNLean.Lattice
