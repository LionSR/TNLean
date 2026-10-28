/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ProjectiveRephasing
import TNLean.MPS.Symmetry.StringOrder

/-!
# Zero-dimensional arbitrary-cochain boundaries

A projective action on a zero-dimensional bond space does not force its raw
factor system to be a cocycle. Rephasing and the supplied-data SPT relation
therefore retain their coboundary-ratio statements at dimension zero.
-/

open TNLean.Algebra
open scoped Matrix TNLean.Algebra.ScalarCohomology

namespace UpstreamCohomologyBoundary

variable {G : Type} [Group G]

private def zeroDimRep (ω : G × G → ℂˣ) : ProjectiveRepresentation (D := 0) ω where
  X := fun _ ↦ 1
  map_mul' := by
    intro g h
    ext i
    exact Fin.elim0 i

-- These raw factors carry no cocycle or normalization hypothesis.
example (ω₀ ω₁ : G × G → ℂˣ)
    (h : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₀)) :
    ∃ (ρ₁ : ProjectiveRepresentation (D := 0) (ScalarCocycle.circlePhaseInclusion ω₁))
      (φ : G → Circle),
      (∀ g, (ρ₁.X g : Matrix (Fin 0) (Fin 0) ℂ) ∈ Matrix.unitaryGroup (Fin 0) ℂ) ∧
      (∀ g, ρ₁.X g = Matrix.GeneralLinearGroup.scalar (Fin 0)
        (Circle.toUnits (φ g)) * (zeroDimRep (ScalarCocycle.circlePhaseInclusion ω₀)).X g) := by
  apply ProjectiveRepresentation.exists_unitary_rephase_of_cohomologous
    (zeroDimRep (ScalarCocycle.circlePhaseInclusion ω₀)) h
  intro g
  exact (Matrix.unitaryGroup (Fin 0) ℂ).one_mem

example {d : ℕ} (A B : MPSTensor d 0)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (ωA ωB : G × G → ℂˣ)
    (h : groupCohomology.IsMulCoboundary₂ (ωA / ωB)) :
    MPSTensor.IsSameSPTPhase A B U := by
  refine ⟨ωA, ωB, zeroDimRep ωA, zeroDimRep ωB, ?_, ?_, h⟩
  all_goals
    intro g i
    ext j
    exact Fin.elim0 j

end UpstreamCohomologyBoundary
