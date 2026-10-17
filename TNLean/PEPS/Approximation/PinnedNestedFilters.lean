/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Adapted definitions from openai/math, Apache-2.0, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a:
lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean, lines 35–40, 52–53, 151–179;
ContourEnergy.lean, lines 65–66; HamiltonianEnergy.lean, lines 64–65.
Changes: namespace, explicit imports, and the existing shared ForwardEdge name.
The existing Pinned.State and Pinned.RegionConfiguration are reused. Positivity,
eigenvalue powers, ascending action, inverse-zero normalization and forward-edge
counting retain the source conventions. No upstream Lean proof text is copied.
-/
import TNLean.PEPS.Approximation.PinnedRegionalState
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Adapted positive filters on the original finite square

This restricted adaptation provides the source-facing filter data and predicates.
It is not an identification with unimported OAI declarations. The coordinate
comparison and physical existence theorem are proved in separate modules.
Singular filters, empty regions, empty configuration types and empty families are
allowed. No eigenbasis or spectral-coordinate representation is part of the data.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace TNLean.PEPS.Approximation.Pinned

/-- Adapted complement-agreement lift from source `Basic.lean`, lines 35–40. -/
def liftLocal {L q : ℕ} (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) :
    Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ := fun x y ↦
  if ∀ v, v ∉ X → x v = y v then
    A (fun v ↦ x v.val) (fun v ↦ y v.val)
  else 0

/-- Adapted Euclidean continuous-linear action from source `Basic.lean`, lines 52–53. -/
def asMap {L q : ℕ} (A : Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ) :
    State L q →L[ℂ] State L q :=
  Matrix.toEuclideanCLM (n := Vertex L → Fin q) (𝕜 := ℂ) A

namespace NestedFilter

/-- Adapted source `PositiveFilter`: positive semidefinite, including singular matrices. -/
structure PositiveFilter {L : ℕ} (q : ℕ) (X : Finset (Vertex L)) where
  matrix : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ
  positive : matrix.PosSemidef

/-- Adapted source `tracePower`, with real powers of the nonnegative eigenvalues. -/
def tracePower {L q : ℕ} {X : Finset (Vertex L)}
    (F : PositiveFilter q X) (p : ℝ) : ℝ :=
  ∑ i, Real.rpow (F.positive.isHermitian.eigenvalues i) p

/-- Adapted source `FilterFamily`, retaining every occurrence of a repeated region. -/
abbrev FilterFamily {L : ℕ} (q m : ℕ) (X : Fin m → Finset (Vertex L)) :=
  (j : Fin m) → PositiveFilter q (X j)

/-- Adapted source reciprocal-eigenvalue-power normalization. -/
def Admissible {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (F : FilterFamily q m X) : Prop :=
  ∀ j, tracePower (F j) (2 / a j) = 1

/-- Adapted source output: local continuous linear maps act in ascending index order. -/
def output {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (Ω : State L q) : State L q :=
  (List.ofFn fun j ↦ asMap (liftLocal (X j) (F j).matrix)).foldl
    (fun ψ T ↦ T ψ) Ω

/-- Adapted source global maximum against every admissible bundled filter family. -/
def IsMaximizer {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (Ω : State L q) (a : Fin m → ℝ) (F : FilterFamily q m X) : Prop :=
  Admissible a F ∧ ∀ G : FilterFamily q m X,
    Admissible a G → ‖output G Ω‖ ≤ ‖output F Ω‖

/-- Adapted source inverse-norm normalization, equal to zero when the output vanishes. -/
def normalizedOutput {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (Ω : State L q) : State L q :=
  ((‖output F Ω‖⁻¹ : ℝ) : ℂ) • output F Ω

namespace Energy

/-- Adapted source crossing predicate on the shared original forward-edge type. -/
def Crosses {L : ℕ} (X : Finset (Vertex L)) (e : ForwardEdge L) : Prop :=
  (e.val.1 ∈ X ∧ e.val.2 ∉ X) ∨ (e.val.2 ∈ X ∧ e.val.1 ∉ X)

instance {L : ℕ} (X : Finset (Vertex L)) (e : ForwardEdge L) :
    Decidable (Crosses X e) :=
  inferInstanceAs (Decidable
    ((e.val.1 ∈ X ∧ e.val.2 ∉ X) ∨ (e.val.2 ∈ X ∧ e.val.1 ∉ X)))

/-- Adapted source count of forward crossings, with each physical edge counted once. -/
def crossingCount {L : ℕ} (X : Finset (Vertex L)) : ℕ :=
  (Finset.univ.filter (Crosses X)).card

end Energy
end NestedFilter
end TNLean.PEPS.Approximation.Pinned
