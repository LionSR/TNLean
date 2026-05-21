/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Irreducible.FormII
import TNLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary

/-!
# Scalar fixed points for irreducible unital MPS transfer maps

This file records the MPS formulation of the fixed-point endpoint used in the
translation-invariant canonical-form proof.

## Main result

* `MPSTensor.fixed_eq_scalar_of_isIrreducibleTensor_unital`: if an MPS tensor is
  irreducible and its transfer map is unital, then every fixed point of the
  transfer map is a scalar multiple of the identity.

## References

* Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`,
  proof lines 816--826.
* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

/-- For an irreducible unital MPS tensor, every transfer-map fixed point is a
scalar multiple of the identity.

This is the MPS formulation of the endpoint in the proof of
PGVWC07 Theorem `Th:TIcanonical`, lines 816--826: after all invariant
subspace splittings have been exhausted, a further non-scalar fixed point
would give another split, so the fixed-point space of the unital block is the
scalar line.  The channel-theoretic input is Wolf Theorem 6.6, formalized as
`fixed_eq_scalar_of_irreducible_unital`. -/
theorem fixed_eq_scalar_of_isIrreducibleTensor_unital
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hUnital : transferMap (d := d) (D := D) A 1 = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hfix : transferMap (d := d) (D := D) A X = X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  have hUnitalKraus : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) A := by
    simpa [transferMap_apply, Matrix.mul_one, KadisonSchwarz.IsUnitalKraus]
      using hUnital
  exact fixed_eq_scalar_of_irreducible_unital A hUnitalKraus
    (isIrreducibleCP_transferMap_of_isIrreducibleTensor A hIrr) X hfix

end MPSTensor
