/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Defs
import TNLean.MPS.Symmetry.MPOSymmetry.IntegerFusion

/-!
# Integer matrix form of a NIM-representation

Source: arXiv:2203.12563, lines 564–565. The source indexes a multiplicity
by its input block followed by its output block. Ordinary matrix multiplication
therefore represents the action using the transpose of this array.

The unit condition below is additional to the current `IsNIMRep` predicate.
The zero action satisfies that predicate and need not preserve the unit.
This module does not construct a Ring instance on integer combinations.
-/

noncomputable section

namespace MPOTensor

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Integer action matrix, with output block as row and input block as column.
Source: arXiv:2203.12563, lines 564–565, in ordinary matrix convention. -/
def integerNIMRepMatrix (M : ι → κ → κ → ℕ) (a : ι) : Matrix κ κ ℤ :=
  fun y x ↦ (M a x y : ℤ)

/-- The old NIM-rep equation gives multiplication in the ordinary matrix order
after transposing the source's input/output indices. -/
theorem IsNIMRep.integerNIMRepMatrix_mul {N : ι → ι → ι → ℕ}
    {M : ι → κ → κ → ℕ} (h : IsNIMRep N M) (a b : ι) :
    integerNIMRepMatrix M a * integerNIMRepMatrix M b =
      ∑ c, (N a b c : ℤ) • integerNIMRepMatrix M c := by
  ext y x
  have hxy :
      (∑ c, (N a b c : ℤ) * (M c x y : ℤ)) =
        ∑ z, (M b x z : ℤ) * (M a z y : ℤ) := by
    exact_mod_cast h a b x y
  simpa [integerNIMRepMatrix, Matrix.mul_apply, mul_comm] using hxy.symm

/-- A unit-preserving action has identity matrix at the unit label.
The hypothesis is deliberately separate from `IsNIMRep`. -/
theorem integerNIMRepMatrix_unit [DecidableEq κ] {M : ι → κ → κ → ℕ} {e : ι}
    (hunit : ∀ x y, M e x y = if x = y then 1 else 0) :
    integerNIMRepMatrix M e = 1 := by
  ext y x
  simp [integerNIMRepMatrix, hunit, Matrix.one_apply, eq_comm]

/-- The additive extension of the transposed integer matrices. -/
def integerNIMRepEval (M : ι → κ → κ → ℕ) :
    (ι →₀ ℤ) →+ Matrix κ κ ℤ :=
  integerFusionEval (integerNIMRepMatrix M)

/-- A ring homomorphism with the specified basis multiplication and transposed
natural basis images restricts to the old NIM-rep predicate.
Project result: this is the restriction direction of the proposed bridge. -/
theorem isNIMRep_of_ringHom [DecidableEq κ] {R : Type*} [Ring R]
    (N : ι → ι → ι → ℕ) (basis : ι → R)
    (hmul : ∀ a b, basis a * basis b = ∑ c, (N a b c : ℤ) • basis c)
    (ρ : R →+* Matrix κ κ ℤ) (M : ι → κ → κ → ℕ)
    (himage : ∀ a, ρ (basis a) = integerNIMRepMatrix M a) : IsNIMRep N M := by
  intro a b x y
  have hmat : integerNIMRepMatrix M a * integerNIMRepMatrix M b =
      ∑ c, (N a b c : ℤ) • integerNIMRepMatrix M c := by
    simpa only [map_mul, map_sum, map_zsmul, himage] using congrArg ρ (hmul a b)
  have hxy := congrArg (fun A : Matrix κ κ ℤ ↦ A y x) hmat
  have hcast : (∑ c, (N a b c : ℤ) * (M c x y : ℤ)) =
      ∑ z, (M b x z : ℤ) * (M a z y : ℤ) := by
    simpa [integerNIMRepMatrix, Matrix.mul_apply, mul_comm] using hxy.symm
  exact_mod_cast hcast

/-- Restriction of a unital ring homomorphism also supplies the missing unit
condition, provided the distinguished basis element is the source unit. -/
theorem nimRep_unit_of_ringHom [DecidableEq κ] {R : Type*} [Ring R]
    (basis : ι → R) (e : ι) (he : basis e = 1)
    (ρ : R →+* Matrix κ κ ℤ) (M : ι → κ → κ → ℕ)
    (himage : ∀ a, ρ (basis a) = integerNIMRepMatrix M a) :
    ∀ x y, M e x y = if x = y then 1 else 0 := by
  intro x y
  have hm : integerNIMRepMatrix M e = 1 := by
    rw [← himage, he, map_one]
  have hxy := congrArg (fun A : Matrix κ κ ℤ ↦ A y x) hm
  have hcast : (M e x y : ℤ) = if x = y then 1 else 0 := by
    simpa [integerNIMRepMatrix, Matrix.one_apply, eq_comm] using hxy
  exact_mod_cast hcast

end MPOTensor
