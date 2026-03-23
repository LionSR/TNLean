/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra

/-!
# Conditional expectation onto fixed-point algebra (Wolf Theorem 6.15)

This file formalizes the conditional expectation projecting onto the
fixed-point *-subalgebra of a quantum channel's Heisenberg-picture map,
following Wolf Theorem 6.15.

When the fixed-point *-subalgebra is the scalar algebra `ℂ · 1` (as for
primitive channels), the conditional expectation takes the explicit form
`E_σ(X) = (tr(σ X) / tr(σ)) • 1`, where `σ` is the unique positive-definite
stationary state. The general irreducible case (period > 1) requires the
Wedderburn block decomposition from Wolf Theorem 6.14 (issue #27).

## Main results

* `IsConditionalExpectation`: predicate recording that a linear map is
  idempotent, unital, maps into a `StarSubalgebra`, and fixes it pointwise.
* `scalarConditionalExpectationLM`: the linear map `X ↦ (tr(σX)/tr(σ)) • 1`.
* `scalarConditionalExpectation_idempotent`: `E_σ² = E_σ`.
* `scalarConditionalExpectation_unital`: `E_σ(1) = 1`.
* `scalarConditionalExpectation_absorbs_adjointMap`:
  `E_σ(T*(X)) = E_σ(X)` when `T(σ) = σ`.
* `adjointMap_absorbs_scalarConditionalExpectation`:
  `T*(E_σ(X)) = E_σ(X)` when `T` is trace-preserving.
* `scalarConditionalExpectation_mem_adjointFixedPoints`:
  `E_σ(X)` is always a fixed point of `T*`.
* `scalarConditionalExpectation_isConditionalExpectation`:
  **Wolf Theorem 6.15** for the scalar fixed-point algebra case.

## Cross-references

* Wolf Proposition 6.6 (Similarity preserving irreducibility):
  `TNLean.Channel.Irreducible.Similarity`.
* Wolf Proposition 6.8 (Hermitian fixed-point decomposition):
  `TNLean.Channel.FixedPoint.Cesaro`,
  `IsChannel.posSemidef_parts_of_hermitian_fixedPoint`.
* Wolf Theorems 6.12-6.13 (fixed-point *-algebra and Kraus commutant):
  `TNLean.Channel.FixedPoint.Algebra`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 6.15, §6.4]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Abstract conditional expectation -/

/-- A **conditional expectation** onto a `StarSubalgebra` `A ⊆ M_D(ℂ)` is a
ℂ-linear map that is idempotent, unital, maps into `A`, and fixes every
element of `A`. This is the abstract property from Wolf Theorem 6.15. -/
structure IsConditionalExpectation
    (E : Mat →ₗ[ℂ] Mat) (A : StarSubalgebra ℂ Mat) : Prop where
  /-- Idempotent: `E(E(X)) = E(X)`. -/
  idempotent : ∀ X : Mat, E (E X) = E X
  /-- Unital: `E(1) = 1`. -/
  unital : E 1 = 1
  /-- Range contained in `A`. -/
  range_subset : ∀ X : Mat, E X ∈ A
  /-- Fixes `A` pointwise. -/
  fixes : ∀ X : Mat, X ∈ A → E X = X

/-! ## Scalar conditional expectation -/

/-- The **scalar conditional expectation** weighted by `σ`:

`E_σ(X) = (tr(σ X) / tr(σ)) • 1`.

This is the conditional expectation from Wolf Theorem 6.15 in the case where
the fixed-point *-subalgebra of the adjoint map is the scalar algebra `ℂ · 1`
(i.e., the channel is primitive). -/
noncomputable def scalarConditionalExpectationLM
    (σ : Mat) (_hσ_tr : trace σ ≠ 0) : Mat →ₗ[ℂ] Mat where
  toFun X := (trace (σ * X) / trace σ) • (1 : Mat)
  map_add' X Y := by
    change (trace (σ * (X + Y)) / trace σ) • (1 : Mat) =
      (trace (σ * X) / trace σ) • 1 + (trace (σ * Y) / trace σ) • 1
    rw [mul_add, trace_add, add_div, add_smul]
  map_smul' c X := by
    simp only [RingHom.id_apply, smul_smul]
    congr 1
    rw [Algebra.mul_smul_comm, trace_smul, smul_eq_mul, mul_div_assoc]

@[simp]
theorem scalarConditionalExpectationLM_apply
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (X : Mat) :
    scalarConditionalExpectationLM σ hσ_tr X =
      (trace (σ * X) / trace σ) • (1 : Mat) := rfl

/-- `E_σ(1) = 1`: the scalar conditional expectation is unital. -/
@[simp]
theorem scalarConditionalExpectation_unital
    (σ : Mat) (hσ_tr : trace σ ≠ 0) :
    scalarConditionalExpectationLM σ hσ_tr 1 = (1 : Mat) := by
  simp [scalarConditionalExpectationLM_apply, mul_one, div_self hσ_tr]

/-- `E_σ(E_σ(X)) = E_σ(X)`: the scalar conditional expectation is
idempotent. -/
theorem scalarConditionalExpectation_idempotent
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (X : Mat) :
    scalarConditionalExpectationLM σ hσ_tr
      (scalarConditionalExpectationLM σ hσ_tr X) =
      scalarConditionalExpectationLM σ hσ_tr X := by
  simp only [scalarConditionalExpectationLM_apply]
  congr 1
  rw [Algebra.mul_smul_comm, mul_one, trace_smul, smul_eq_mul,
    div_mul_cancel₀ (trace (σ * X)) hσ_tr]

/-- `E_σ` maps every matrix to a scalar multiple of `1`. -/
theorem scalarConditionalExpectation_range_scalar
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (X : Mat) :
    ∃ c : ℂ, scalarConditionalExpectationLM σ hσ_tr X = c • (1 : Mat) :=
  ⟨trace (σ * X) / trace σ, rfl⟩

/-- `E_σ(c • 1) = c • 1`: the scalar conditional expectation fixes scalar
matrices. -/
theorem scalarConditionalExpectation_fixes_scalar
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (c : ℂ) :
    scalarConditionalExpectationLM σ hσ_tr (c • (1 : Mat)) =
      c • (1 : Mat) := by
  simp only [scalarConditionalExpectationLM_apply, Algebra.mul_smul_comm, mul_one,
    trace_smul, smul_eq_mul, mul_div_cancel_right₀ c hσ_tr]

/-! ## Commutation with the adjoint map -/

/-- `E_σ` absorbs the adjoint map: `E_σ(adjointMap K X) = E_σ(X)`,
provided `σ` is a fixed point of `map K`.

This uses the Kraus adjointness identity
`tr(ρ · map K X) = tr(adjointMap K ρ · X)`. -/
theorem scalarConditionalExpectation_absorbs_adjointMap
    (σ : Mat) (hσ_tr : trace σ ≠ 0)
    (K : Fin d → Mat) (hσ_fix : map K σ = σ) (X : Mat) :
    scalarConditionalExpectationLM σ hσ_tr (adjointMap K X) =
      scalarConditionalExpectationLM σ hσ_tr X := by
  simp only [scalarConditionalExpectationLM_apply]
  congr 1
  have : trace (σ * adjointMap K X) = trace (σ * X) :=
    calc trace (σ * adjointMap K X)
        = trace (adjointMap K X * σ) := trace_mul_comm σ (adjointMap K X)
      _ = trace (X * map K σ) := by
          rw [← trace_mul_map_eq_trace_adjointMap_mul K X σ]
      _ = trace (X * σ) := by rw [hσ_fix]
      _ = trace (σ * X) := trace_mul_comm X σ
  rw [this]

/-- The adjoint map absorbs `E_σ`: `adjointMap K (E_σ(X)) = E_σ(X)`,
provided `K` is trace-preserving (equivalently, `adjointMap K` is unital). -/
theorem adjointMap_absorbs_scalarConditionalExpectation
    (σ : Mat) (hσ_tr : trace σ ≠ 0)
    (K : Fin d → Mat) (h_tp : IsTP K) (X : Mat) :
    adjointMap K (scalarConditionalExpectationLM σ hσ_tr X) =
      scalarConditionalExpectationLM σ hσ_tr X := by
  simp only [scalarConditionalExpectationLM_apply, adjointMap_smul,
    adjointMap_one_of_isTP K h_tp]

/-- `E_σ(X)` is always a fixed point of the adjoint map (when `K` is TP). -/
theorem scalarConditionalExpectation_mem_adjointFixedPoints
    (σ : Mat) (hσ_tr : trace σ ≠ 0)
    (K : Fin d → Mat) (h_tp : IsTP K) (X : Mat) :
    scalarConditionalExpectationLM σ hσ_tr X ∈ adjointFixedPoints K :=
  adjointMap_absorbs_scalarConditionalExpectation σ hσ_tr K h_tp X

/-- The scalar conditional expectation commutes with the adjoint map in both
senses: `E_σ(adjointMap K X) = E_σ(X)` and
`adjointMap K (E_σ(X)) = E_σ(X)`. -/
theorem scalarConditionalExpectation_commutes_adjointMap
    (σ : Mat) (hσ_tr : trace σ ≠ 0)
    (K : Fin d → Mat) (h_tp : IsTP K) (hσ_fix : map K σ = σ) (X : Mat) :
    scalarConditionalExpectationLM σ hσ_tr (adjointMap K X) =
      scalarConditionalExpectationLM σ hσ_tr X ∧
    adjointMap K (scalarConditionalExpectationLM σ hσ_tr X) =
      scalarConditionalExpectationLM σ hσ_tr X :=
  ⟨scalarConditionalExpectation_absorbs_adjointMap σ hσ_tr K hσ_fix X,
   adjointMap_absorbs_scalarConditionalExpectation σ hσ_tr K h_tp X⟩

/-! ## Conditional expectation onto the adjoint fixed-point *-subalgebra -/

/-- **Wolf Theorem 6.15** (scalar fixed-point algebra case):

When a TP Kraus family has `ρ` as a positive-definite fixed point of the
Schrödinger map, and the adjoint fixed-point set consists only of scalar
matrices, the scalar conditional expectation `E_ρ` is a conditional
expectation onto the adjoint fixed-point `StarSubalgebra`.

This covers the primitive channel case. In the general irreducible case
with period `h > 1`, the fixed-point algebra is `h`-dimensional and the
conditional expectation requires the Wedderburn block decomposition
(Wolf Theorem 6.14, issue #27). -/
theorem scalarConditionalExpectation_isConditionalExpectation
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (hρ_tr : trace ρ ≠ 0)
    (h_scalar : ∀ X : Mat, X ∈ adjointFixedPoints K →
      ∃ c : ℂ, X = c • (1 : Mat)) :
    IsConditionalExpectation
      (scalarConditionalExpectationLM ρ hρ_tr)
      (adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix) where
  idempotent := scalarConditionalExpectation_idempotent ρ hρ_tr
  unital := scalarConditionalExpectation_unital ρ hρ_tr
  range_subset X := by
    rw [mem_adjointFixedPointsStarSubalgebra]
    exact scalarConditionalExpectation_mem_adjointFixedPoints ρ hρ_tr K h_tp X
  fixes X hX := by
    rw [mem_adjointFixedPointsStarSubalgebra] at hX
    obtain ⟨c, hc⟩ := h_scalar X hX
    rw [hc]
    exact scalarConditionalExpectation_fixes_scalar ρ hρ_tr c

end Kraus
