/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import TNLean.PEPS.ParentHamiltonian.DependentRegionCoordinates

/-!
# Canonical marginals of regularized patch outputs

The normalized output of the regularized patch problem has its regional density
matrices given by the existing finite-product partial trace. The only coordinate
change removes the redundant membership witness in the full-region index.
Expectations of arbitrary complex regional matrices agree with the complex trace
pairing against these marginals. Local dimensions may vary, and regions may be
empty.

Source: OpenAI `03-patches.tex`, lines 68–99, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*}

variable [∀ v, Fintype (Out v)]

variable {m : ℕ} (regions : Fin m → Finset V)

/-- The canonical regional density of the same normalized vector used in the
regularized patch minimum problem. Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def normalizedRegularizedPatchMarginal (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ :=
  FiniteProduct.reducedPure Out
    (dependentGlobalConfigIsometry (normalizedRegularizedPatchOutput regions a b Ω x)) R

/-- Canonical regularized patch marginals are positive semidefinite. -/
theorem normalizedRegularizedPatchMarginal_posSemidef (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) :
    (normalizedRegularizedPatchMarginal regions a b Ω x R).PosSemidef :=
  FiniteProduct.reducedPure_posSemidef Out _ R

/-- Every feasible regularized output has trace-one canonical marginals,
including the marginal on the empty region. -/
theorem trace_normalizedRegularizedPatchMarginal (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (R : Finset V) :
    (normalizedRegularizedPatchMarginal regions a b Ω x R).trace = 1 := by
  apply FiniteProduct.trace_reducedPure
  rw [dependentGlobalConfigIsometry.norm_map]
  exact norm_normalizedRegularizedPatchOutput regions a ha hb Ω hΩ hx

/-- Regional expectations in the normalized regularized output are precisely
the complex trace pairings with its canonical reduced state. -/
theorem inner_normalizedRegularizedPatchOutput_lift_eq_trace (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ) :
    inner ℂ (normalizedRegularizedPatchOutput regions a b Ω x)
        (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ
          normalizedRegularizedPatchOutput regions a b Ω x)) =
      Matrix.trace (normalizedRegularizedPatchMarginal regions a b Ω x R * K) :=
  inner_dependentRegionOperatorLift_eq_trace_reducedPure R K _

/-- Relabelling the actual normalized final-state marginal gives the QIC
regional state of that same normalized output. No optimizer or commutation
hypothesis is involved. -/
theorem reindex_normalizedRegularizedPatchMarginal {n : V → ℕ}
    (e : ∀ v, Out v ≃ Fin (n v)) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) :
    Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R)
        (normalizedRegularizedPatchMarginal regions a b Ω x R) =
      Entropy.regionState R (dependentGlobalFinIsometry e
        (normalizedRegularizedPatchOutput regions a b Ω x)) :=
  reindex_reducedPure_eq_regionState e R _

end TNLean.PEPS
