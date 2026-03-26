/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Primitivity.IrreducibleAnalysis

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two parts:

**Part 1 — Irreducibility propagation** (`hT_irr_all`):
`T_{t₀}` irreducible → `T_s` irreducible for ALL `s > 0`.
Uses the kernel bridge: `ker(L) = Span{σ}` where `σ` is the unique
faithful density fixed point of `T_{t₀}`. Then `σ` is fixed by all `T_s`
(semigroup commutativity + density uniqueness). For each `s > 0`, `T_s`
is shown irreducible via `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.

**Part 2 — Roots of unity → primitivity**:
Given irreducibility at all times, peripheral eigenvalues are roots of unity
(Wolf Thm 6.6). If `μ` is a peripheral eigenvalue of `T_t` with `μ^p = 1`,
the eigenvector `V` is a fixed point of `T_{pt}`. By irreducibility of
`T_{pt}`, `V` must be proportional to the unique faithful density fixed
point `σ'`, giving `T_t σ' = μ σ'`. Trace preservation then forces `μ = 1`.

**Status**: The glue logic is complete, but this theorem transitively depends on
13 `sorry` placeholders in `IrreducibleAnalysis.lean` (formerly `axiom`
declarations), including `primitive_of_irreducible_all`,
`exists_primitive_fraction_slice`, and `fixedPoint_eq_trace_smul_of_primitive_slice`. -/
theorem irreducible_semigroup_implies_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t) := by
  have hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) :=
    irreducible_all_of_irreducible_time L T hT hexp t₀ ht₀ hirr
  intro t ht
  exact ⟨
    primitive_of_irreducible_all T hT hT_irr_all t ht,
    hT_irr_all t ht
  ⟩

/-- **Wolf Proposition 7.5** (full equivalence): For a QDS of channels, the
following are equivalent:
1. There exists `t₀ > 0` such that `T_{t₀}` is irreducible.
2. `T_t` is irreducible for all `t > 0`.
3. `T_t` is primitive for all `t > 0`.
4. There exists a positive definite `ρ_∞` such that `T_t(ρ) → ρ_∞` for all
   density matrices `ρ`.
5. `ker(L)` is one-dimensional and spanned by a positive definite `ρ_∞`.

This formalization captures the equivalence of items 1, 2, and 3:
`(∃ t₀ > 0, IsIrreducibleMap (T t₀)) ↔ (∀ t > 0, IsPrimitive (T t) ∧ IsIrreducibleMap (T t))`.

The RHS includes `IsIrreducibleMap` alongside `IsPrimitive` because the definition
`IsPrimitive E := peripheralEigenvalues E = {1}` records only the *set* of peripheral
eigenvalues, which alone does not imply irreducibility (e.g. the identity map on
`M₂(ℂ)` is primitive but not irreducible). For quantum dynamical semigroups,
irreducibility at one time propagates to all times, making the conjunction equivalent
to item 2, and `IsPrimitive` then follows as a consequence. -/
theorem qds_irreducible_iff_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀)) ↔
    (∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t)) := by
  constructor
  · -- Forward: ∃ t₀, irreducible T_{t₀} → ∀ t, primitive ∧ irreducible T_t
    rintro ⟨t₀, ht₀, hirr⟩
    exact irreducible_semigroup_implies_primitive L T hT hexp t₀ ht₀ hirr
  · -- Backward: ∀ t > 0, primitive ∧ irreducible T_t → ∃ t₀ > 0, irreducible T_{t₀}
    intro h
    exact ⟨1, one_pos, (h 1 one_pos).2⟩

end -- noncomputable section
