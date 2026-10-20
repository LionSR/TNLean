/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedFamilyPhysicalBasis
import TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport
import Mathlib.Data.Fintype.BigOperators

/-! # Original physical configurations after selecting all parties

The exterior physical memory has its single scalar coordinate. Removing this
coordinate identifies the remaining configurations with the original physical
configurations, retaining every original local dimension. Under this
identification, the exterior matrix entry multiplies the product of the original
party matrices. Its value may be zero, and the original party type may be empty.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–151, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- Removing the canonical exterior singleton coordinate leaves precisely the
original physical configurations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 565–588. -/
def selectedFamilyPhysicalConfigEquiv (d : P → ℕ) :
    ((q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q) ≃
      ((p : P) → Fin (d p)) where
  toFun x p := x (some ⟨p, rfl⟩)
  invFun x
    | none => PUnit.unit
    | some p => x p.val
  left_inv x := by
    funext q
    cases q with
    | none => exact Subsingleton.elim (α := PUnit) _ _
    | some p => rfl
  right_inv x := rfl

/-- In the original physical configurations, the exterior scalar is retained
as one factor multiplying the original party product. No scalar is cancelled.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem partyProductMatrix_selectedFamilyPhysicalConfig [Fintype P]
    (d : P → ℕ)
    (M : (q : Option {_p : P // true = true}) →
      Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ) :
    (dependentPhysicalProductFamilyMatrix M).submatrix
        (selectedFamilyPhysicalConfigEquiv d).symm
        (selectedFamilyPhysicalConfigEquiv d).symm =
      M none PUnit.unit PUnit.unit • dependentPhysicalProductFamilyMatrix
        (fun p : P ↦ M (some ⟨p, rfl⟩)) := by
  classical
  ext x y
  change (∏ q, M q ((selectedFamilyPhysicalConfigEquiv d).symm x q)
      ((selectedFamilyPhysicalConfigEquiv d).symm y q)) =
    M none PUnit.unit PUnit.unit * ∏ p : P, M (some ⟨p, rfl⟩) (x p) (y p)
  rw [Fintype.prod_option]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun _ : P ↦ (rfl : true = true)))
    _ _ (fun _ ↦ rfl)

end TNLean.PEPS.PairEffect
