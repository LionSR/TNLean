/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Absorbing a scalar into one party matrix

A common scalar multiplying a product of party matrices can be placed at one
specified party. No division is used, so the identity includes a zero scalar.
For distributed constructions, the chosen party is supplied by the original
nonempty-party convention.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.Lattice.PartyCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {I O : P → Type}

/-- Scaling one specified party matrix scales the product matrix once.
The scalar may vanish. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 565–588. -/
theorem partyProductMatrix_smul_at_party
    (M : (p : P) → Matrix (O p) (I p) ℂ) (p₀ : P) (μ : ℂ) :
    dependentPhysicalProductFamilyMatrix
      (fun p ↦ (if p = p₀ then μ else 1) • M p) =
      μ • dependentPhysicalProductFamilyMatrix M := by
  exact funext fun x ↦ funext fun y ↦
    (Finset.prod_mul_distrib
      (s := Finset.univ) (f := fun p ↦ if p = p₀ then μ else 1)
      (g := fun p ↦ M p (x p) (y p))).trans
      (congrArg (fun c ↦ c * ∏ p, M p (x p) (y p))
        (Fintype.prod_ite_eq' p₀ (fun _ ↦ μ)))

end TNLean.Lattice.PartyCircuit
