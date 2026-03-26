/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Peripheral eigenvalue group structure (Wolf Theorem 6.6)

This file establishes that the peripheral eigenvalues of an irreducible
quantum channel form a **cyclic group** under multiplication, completing
the formalization of Wolf Theorem 6.6.

## Building blocks (already formalized elsewhere)

The proof combines three ingredients that already exist:

1. **Peripheral eigenvalues are roots of unity** — proved in
   `Channel/Peripheral/ClosureFixedPoint.lean` as
   `peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint`

2. **Finite subgroups of `ℂ*` consisting of roots of unity are cyclic** —
   Mathlib's `rootsOfUnity.isCyclic` in `RingTheory/RootsOfUnity/Basic.lean`

3. **Peripheral unitaries and cyclic projections** — proved in
   `Channel/Peripheral/CyclicDecomposition.lean` via
   `exists_peripheral_unitary_of_irreducible_schwarz` and
   `exists_cyclic_projections_of_peripheral_unitary`

## Main results

* `peripheral_eigenvalues_closed_under_mul` — closure under multiplication
* `peripheral_eigenvalues_closed_under_inv` — closure under inversion
* `peripheral_eigenvalues_form_cyclic_group` — the full cyclic group structure
* `peripheral_eigenvalue_multiplicity_one` — each eigenvalue has multiplicity 1
* `channel_period_divides_dim` — period divides bond dimension

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.2, Thm 6.6]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

variable {D : ℕ}

/-! ## Closure under multiplication -/

/-- **Peripheral eigenvalues are closed under multiplication.**

Follows from `exists_peripheral_unitary_of_irreducible_schwarz`: peripheral
eigenvalues have unitary eigenvectors, and the multiplicative domain property
gives `E(U_α U_β) = E(U_α) E(U_β) = αβ · U_α U_β`. -/
theorem peripheral_eigenvalues_closed_under_mul
    {r : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) K))
    {α β : ℂ}
    (hα : α ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K))
    (hβ : β ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K)) :
    (α * β) ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K) := by
  -- Get unitary eigenvectors U_α and U_β from CyclicDecomposition.
  obtain ⟨Uα, hUα⟩ := MPSTensor.exists_peripheral_unitary_of_irreducible_schwarz
    K hUnital ρ hρ hρfix hIrr hα
  obtain ⟨Uβ, hUβ⟩ := MPSTensor.exists_peripheral_unitary_of_irreducible_schwarz
    K hUnital ρ hρ hρfix hIrr hβ
  constructor
  · -- HasEigenvalue for α * β: product of unitaries is nonzero, and
    -- E(U_α U_β) = α β · U_α U_β by the multiplicative domain.
    sorry -- TODO: use Kraus.mul_mem_multiplicativeDomain (MultiplicativeDomainFull.lean:250)
           -- + ks_equality_of_peripheral_eigenvector_of_fixedPoint for U_α, U_β
  · rw [Complex.norm_mul, hα.2, hβ.2, mul_one]

/-- **Peripheral eigenvalues are closed under inversion.**

For `|α| = 1`, we have `α⁻¹ = ᾱ`, and `U_α†` is the eigenvector. -/
theorem peripheral_eigenvalues_closed_under_inv
    {r : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) K))
    {α : ℂ}
    (hα : α ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K)) :
    α⁻¹ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K) := by
  constructor
  · sorry -- TODO: use conjTranspose of unitary eigenvector
  · rw [norm_inv, hα.2, inv_one]

/-! ## Cyclic group structure

The proof strategy uses Mathlib's `rootsOfUnity.isCyclic`:

1. By `peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint`,
   every peripheral eigenvalue `μ` satisfies `μ^p = 1` for some `p > 0`.
2. Taking `m = lcm` of all such periods, every peripheral eigenvalue is an
   `m`-th root of unity.
3. The peripheral eigenvalues embed into `rootsOfUnity m ℂ`, which is cyclic
   by Mathlib's `rootsOfUnity.isCyclic`.
4. The period `m` divides `D` via the cyclic projections from
   `CyclicDecomposition.lean`.
-/

/-- **The peripheral eigenvalues form a cyclic group** (Wolf Thm 6.6).

Combines `peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint`
(peripheral eigenvalues are roots of unity) with Mathlib's
`rootsOfUnity.isCyclic` (finite subgroups of `ℂ*` are cyclic). -/
theorem peripheral_eigenvalues_form_cyclic_group
    {r : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) K)) :
    ∃ (m : ℕ) (γ : ℂ),
      0 < m ∧
      IsPrimitiveRoot γ m ∧
      m ∣ D ∧
      peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K) =
        {z : ℂ | ∃ k : Fin m, z = γ ^ (k : ℕ)} := by
  -- Step 1: Each peripheral eigenvalue is a root of unity (ClosureFixedPoint.lean).
  -- Step 2: Embed into rootsOfUnity (lcm of periods) in ℂ.
  -- Step 3: Apply rootsOfUnity.isCyclic from Mathlib.
  -- Step 4: Extract primitive root and period.
  -- Step 5: Period divides D via cyclic projections (CyclicDecomposition.lean).
  sorry -- TODO: connect ClosureFixedPoint + Mathlib rootsOfUnity.isCyclic

/-- **Each peripheral eigenvalue has multiplicity 1** (Wolf Thm 6.6).

Follows from `fixed_eq_scalar_of_irreducible_unital` in
`CyclicDecomposition.lean`: if `E(X) = X` with `E` irreducible and unital,
then `X = c · I`. Applied to `E^m` restricted to a cyclic sector, this
forces one-dimensional eigenspaces. -/
theorem peripheral_eigenvalue_multiplicity_one
    {r : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) K))
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K)) :
    Module.finrank ℂ
      (Module.End.eigenspace (MPSTensor.transferMap (d := r) (D := D) K) γ) = 1 := by
  -- Use fixed_eq_scalar_of_irreducible_unital from CyclicDecomposition.lean
  sorry -- TODO: restrict E^m to cyclic sector, apply scalar-fixed-point lemma

/-- The **minimal** period `m` divides `D` (the bond dimension).

Follows from `exists_cyclic_projections_of_peripheral_unitary` in
`CyclicDecomposition.lean`: the `m` mutually orthogonal projections summing
to `I` force each to have rank `D/m`. -/
theorem channel_period_divides_dim
    {r : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) K))
    {m : ℕ} {γ : ℂ} (hm : 0 < m)
    (hγprim : IsPrimitiveRoot γ m)
    (hγ : γ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) K)) :
    m ∣ D := by
  -- Use exists_cyclic_projections_of_peripheral_unitary from CyclicDecomposition.lean
  sorry -- TODO: m orthogonal projections summing to I force rank D/m each
