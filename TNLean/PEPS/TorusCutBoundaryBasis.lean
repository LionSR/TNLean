/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutBoundary

/-!
# Fixed cut boundaries as products of matrix units

Every arbitrary joint boundary tensor is a linear combination of fixed
endpoint tensors. Each fixed endpoint tensor is a product of matrix units
on the actual cut bonds. This supplies a spanning family of literal cut
networks without assuming that general boundaries factorize.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V Phys : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A fixed horizontal endpoint pair is the corresponding matrix unit. -/
def torusCutHorizontalUnit (η : TorusCutBoundaryConfig width height V)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  Matrix.single (η.1 v.2).2 (η.1 v.2).1 1

/-- A fixed vertical endpoint pair is the corresponding matrix unit. -/
def torusCutVerticalUnit (η : TorusCutBoundaryConfig width height V)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  Matrix.single (η.2 v.1).2 (η.2 v.1).1 1

omit [Fintype V] in
/-- Matrix units on all cut bonds fix exactly one full endpoint configuration. -/
theorem torusCutBondBoundary_units (c : ZMod width) (r : ZMod height)
    (η : TorusCutBoundaryConfig width height V) :
    torusCutBondBoundary c r (torusCutHorizontalUnit η) (torusCutVerticalUnit η) =
      Pi.single η 1 := by
  classical
  funext θ
  simp only [torusCutBondBoundary, torusCutHorizontalUnit, torusCutVerticalUnit,
    Matrix.single_apply, and_comm, ← Prod.ext_iff, Fintype.prod_boole, ← funext_iff]
  by_cases h₁ : η.1 = θ.1 <;> by_cases h₂ : η.2 = θ.2 <;>
    simp [Pi.single_apply, Prod.ext_iff, h₁, h₂, eq_comm]

/-- An actual cut-map column is the original native network with matrix units
on cut bonds and identity matrices on the other bonds. -/
theorem torusCutMap_single_eq_bondNetwork
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (η : TorusCutBoundaryConfig width height V)
    (σ : TorusVertex width height → Phys) :
    torusCutMap a c r (Pi.single η 1) σ =
      torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
        (fun v ↦ if v.1 + 1 = c then torusCutHorizontalUnit η v else 1)
        (fun v ↦ if v.2 + 1 = r then torusCutVerticalUnit η v else 1) := by
  rw [← torusCutBondBoundary_units c r η, torusCutMap_apply, torusCutCoeff_bondBoundary]

end TNLean.PEPS
