/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit
import QICLean.Analysis.MatrixFramePerturbation

/-!
# Coherent conversion of encoders through a common seed

Two genuine local unitaries acting on the same seed matrix give one local unitary
converting their approximate encoders. The operator-norm error is the sum of the two
encoding errors. The same estimate holds for inputs entangled with any finite external
reference, without a factor depending on the reference dimension.

The seed is an algebraic intermediary. No preparation of that seed from a product state
is asserted or charged, and no measurement procedure is inverted.

## Main results

* `QuantumCircuit.IsLocalCircuitOfDepth.norm_encoder_conversion_le` bounds the error of
  composing one local unitary with the adjoint of another.
* `Matrix.norm_encoder_conversion_reference_le` from QICLean retains an arbitrary reference.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, discussion and outlook. These
  operator-norm statements make the coherent content of common-seed conversion explicit;
  they do not identify a phase equivalence relation.
-/

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {d N : ℕ} [NeZero d] [NeZero N] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If two local unitaries approximately encode the same logical seed, their relative
unitary converts the whole encoders with the sum of the two operator-norm errors.
The circuit acts simultaneously on all logical amplitudes. -/
theorem IsLocalCircuitOfDepth.norm_encoder_conversion_le
    {UA UB : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} {TA TB : ℕ}
    (hUA : IsLocalCircuitOfDepth UA TA) (hUB : IsLocalCircuitOfDepth UB TB)
    (F G J : Matrix (Fin N → Fin d) ι ℂ) :
    IsLocalCircuitOfDepth (UB * UAᴴ) (TA + TB) ∧
      ‖UB * UAᴴ * F - G‖ ≤ ‖F - UA * J‖ + ‖G - UB * J‖ := by
  have hU : IsLocalCircuitOfDepth (UB * UAᴴ) (TA + TB) := hUA.star.mul hUB
  refine ⟨hU, ?_⟩
  have heq : UB * UAᴴ * F - G =
      (UB * UAᴴ) * (F - UA * J) + (UB * J - G) := by
    rw [Matrix.mul_sub]
    have hcancel : (UB * UAᴴ) * (UA * J) = UB * J := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (UAᴴ),
        (show UAᴴ * UA = 1 from Unitary.star_mul_self_of_mem hUA.mem_unitary), Matrix.one_mul]
    rw [hcancel]
    abel
  rw [heq]
  calc
    _ ≤ ‖(UB * UAᴴ) * (F - UA * J)‖ + ‖UB * J - G‖ := norm_add_le _ _
    _ ≤ ‖UB * UAᴴ‖ * ‖F - UA * J‖ + ‖UB * J - G‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) le_rfl
    _ = _ := by rw [CStarRing.norm_of_mem_unitary hU.mem_unitary, one_mul, norm_sub_rev (UB * J)]

end QuantumCircuit
