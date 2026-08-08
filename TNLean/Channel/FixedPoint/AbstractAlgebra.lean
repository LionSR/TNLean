/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.AbstractMultiplicativeDomain
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.MatrixTracePairing

/-!
# Fixed points of abstract unital Schwarz maps

This file proves the algebraic step in Wolf's structure theorem after a
positive-definite invariant weight has been chosen.  The map is not assumed to
admit a Kraus representation.

## Main results

* `SchwarzMap.schwarz_equality_of_mem_fixedPoints`: a fixed point attains equality in
  the Schwarz inequality when the trace adjoint has a positive-definite fixed point.
* `SchwarzMap.mem_multiplicativeDomain_of_mem_fixedPoints`: every fixed point belongs
  to the abstract multiplicative domain.
* `SchwarzMap.fixedPointsStarSubalgebra`: the fixed points form a star-subalgebra.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.12 and
  Equation (6.60); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1395--1417.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzMap

variable {n : Type*}

local notation "Mat" => Matrix n n ℂ

/-- The fixed-point set of a complex-linear matrix map. -/
def fixedPoints (E : Mat →ₗ[ℂ] Mat) : Set Mat :=
  {X | E X = X}

@[simp] theorem mem_fixedPoints (E : Mat →ₗ[ℂ] Mat) (X : Mat) :
    X ∈ fixedPoints E ↔ E X = X :=
  Iff.rfl

section

variable [Finite n]

/-- Fixed points of a positive map are closed under conjugate transpose. -/
theorem conjTranspose_mem_fixedPoints
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E)
    {X : Mat} (hX : X ∈ fixedPoints E) :
    Xᴴ ∈ fixedPoints E := by
  change E Xᴴ = Xᴴ
  rw [hEpos.map_conjTranspose, hX]

end


variable [Fintype n]

/-- A fixed point attains equality in the Schwarz inequality when the trace adjoint
has a positive-definite fixed point.

This is the weighted-trace step in Wolf, Equation (6.60), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1404--1413. -/
theorem schwarz_equality_of_mem_fixedPoints
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE : IsSchwarzMap E)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : Matrix.traceAdjointMap E ρ = ρ)
    {X : Mat} (hX : X ∈ fixedPoints E) :
    E (Xᴴ * X) = E Xᴴ * E X := by
  have hgap : (E (Xᴴ * X) - E Xᴴ * E X).PosSemidef := hE X
  have hXstar : E Xᴴ = Xᴴ := by
    rw [hEpos.map_conjTranspose, hX]
  have htrace_first :
      Matrix.trace (ρ * E (Xᴴ * X)) = Matrix.trace (ρ * (Xᴴ * X)) := by
    calc
      Matrix.trace (ρ * E (Xᴴ * X)) =
          Matrix.trace (Matrix.traceAdjointMap E ρ * (Xᴴ * X)) :=
        (Matrix.trace_traceAdjointMap_mul E ρ (Xᴴ * X)).symm
      _ = Matrix.trace (ρ * (Xᴴ * X)) := by rw [hρ_fix]
  have htrace_gap :
      Matrix.trace (ρ * (E (Xᴴ * X) - E Xᴴ * E X)) = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, htrace_first, hXstar, hX]
    simp
  exact sub_eq_zero.mp
    (Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hgap hρ htrace_gap)

/-- Every fixed point belongs to the full abstract multiplicative domain.

The second one-sided equality is obtained by applying the weighted-trace argument to
the adjoint fixed point.  This is the multiplicative-domain step in Wolf Theorem 6.12,
local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1404--1415. -/
theorem mem_multiplicativeDomain_of_mem_fixedPoints
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE : IsSchwarzMap E)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : Matrix.traceAdjointMap E ρ = ρ)
    {X : Mat} (hX : X ∈ fixedPoints E) :
    X ∈ multiplicativeDomain E := by
  rw [mem_multiplicativeDomain_iff E hE X]
  refine ⟨schwarz_equality_of_mem_fixedPoints E hEpos hE hρ hρ_fix hX, ?_⟩
  have hXstar : Xᴴ ∈ fixedPoints E :=
    conjTranspose_mem_fixedPoints E hEpos hX
  simpa using
    (schwarz_equality_of_mem_fixedPoints E hEpos hE hρ hρ_fix hXstar)

/-- Fixed points are closed under multiplication under the hypotheses of Wolf
Theorem 6.12. -/
theorem mul_mem_fixedPoints
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE : IsSchwarzMap E)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : Matrix.traceAdjointMap E ρ = ρ)
    {X Y : Mat} (hX : X ∈ fixedPoints E) (hY : Y ∈ fixedPoints E) :
    X * Y ∈ fixedPoints E := by
  have hXmd : X ∈ multiplicativeDomain E :=
    mem_multiplicativeDomain_of_mem_fixedPoints E hEpos hE hρ hρ_fix hX
  change E (X * Y) = X * Y
  rw [hXmd.2 Y, hX, hY]

variable [DecidableEq n]

/-- **Full-support fixed-point algebra after choosing a faithful invariant weight.**

Let `E` be a positive unital complex-linear map satisfying the Schwarz inequality.
If the trace-pairing adjoint of `E` has a positive-definite fixed point, then the
fixed points of `E` form a star-subalgebra.

Wolf uses the term *Schwarz map* for a positive unital map satisfying Equation (5.2);
the three properties are separate hypotheses here because they are separate predicates
in the formal library.  Source: Wolf Theorem 6.12 and Equation (6.60), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1395--1417.  The explicit
block realization from Wolf Equation (1.39) is not asserted here.

**Scope restriction (positive-definite witness):** Wolf Theorem 6.12 assumes an
arbitrary full-rank fixed point and invokes the proposition on positive fixed
points to choose a positive-definite one (local source lines 1161--1192 and
1404--1405).  This declaration takes the positive-definite witness explicitly.
Documented in `docs/paper-gaps/wolf_thm6_12_abstract_schwarz_fixed_points.tex`.
Elimination: formalize that source reduction for abstract positive
trace-preserving maps and use it to wrap this lemma with the literal theorem
hypothesis. -/
noncomputable def fixedPointsStarSubalgebra
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    (hE : IsSchwarzMap E) {ρ : Mat} (hρ : ρ.PosDef)
    (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) :
    StarSubalgebra ℂ Mat where
  carrier := fixedPoints E
  zero_mem' := E.map_zero
  add_mem' := by
    intro X Y hX hY
    change E (X + Y) = X + Y
    rw [E.map_add, hX, hY]
  one_mem' := hE_one
  mul_mem' := by
    intro X Y hX hY
    exact mul_mem_fixedPoints E hEpos hE hρ hρ_fix hX hY
  algebraMap_mem' := by
    intro c
    change E (algebraMap ℂ Mat c) = algebraMap ℂ Mat c
    simp [Algebra.algebraMap_eq_smul_one, hE_one]
  star_mem' := by
    intro X hX
    change Xᴴ ∈ fixedPoints E
    exact conjTranspose_mem_fixedPoints E hEpos hX

@[simp] theorem mem_fixedPointsStarSubalgebra
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    (hE : IsSchwarzMap E) {ρ : Mat} (hρ : ρ.PosDef)
    (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) (X : Mat) :
    X ∈ fixedPointsStarSubalgebra E hEpos hE_one hE hρ hρ_fix ↔
      E X = X :=
  Iff.rfl

end SchwarzMap
