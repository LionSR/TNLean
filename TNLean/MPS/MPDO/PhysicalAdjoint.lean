/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs

/-!
# Physical adjoint of an MPO tensor

This file defines the physical adjoint, which exchanges and conjugates the
physical indices of an MPO tensor without reversing its virtual chain, and
proves the corresponding word and periodic-operator identities.

## Main definition

* `MPOTensor.physicalAdjointTensor` — physical adjoint without virtual reflection.

## Main results

* `MPOTensor.evalWord_physicalAdjointTensor` — word evaluation under physical adjoint.
* `MPOTensor.mpo_physicalAdjointTensor` — the periodic family is conjugate-transposed.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The physical adjoint of an MPO tensor swaps its ket and bra indices and conjugates each
virtual matrix entry, without transposing the virtual indices:
$$(K^\sharp)^{ij}_{\beta\alpha} = \overline{K^{ji}_{\beta\alpha}}.$$

This local adjoint relates layer annihilation to the two-sided support condition in equation
`PjKiPj`; unlike `adjointTensor`, it does not reverse virtual multiplication.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`--`PjKiPj`,
lines 1634--1689. -/
def physicalAdjointTensor (K : MPOTensor d D) : MPOTensor d D :=
  fun i j β α ↦ star (K j i β α)

/-- Evaluating the physical adjoint swaps the physical indices and conjugates the entry. -/
@[simp] theorem physicalAdjointTensor_apply (K : MPOTensor d D)
    (i j : Fin d) (β α : Fin D) :
    physicalAdjointTensor K i j β α = star (K j i β α) := rfl

/-- Physical slices of the physical adjoint are the conjugate transposes of the original
physical slices.  Only physical indices are transposed.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem physicalSlice_physicalAdjointTensor (K : MPOTensor d D) (β α : Fin D) :
    physicalSlice (physicalAdjointTensor K) β α = (physicalSlice K β α)ᴴ := by
  ext i j
  rfl

/-- Closed words of the physical adjoint are entrywise conjugates of the words with ket and
bra configurations exchanged. -/
theorem evalWord_physicalAdjointTensor (K : MPOTensor d D)
    (is js : List (Fin d)) (hlen : is.length = js.length) :
    evalWord (physicalAdjointTensor K) is js =
      (evalWord K js is).map (starRingEnd ℂ) := by
  induction is generalizing js with
  | nil =>
      simp only [List.length_nil, eq_comm, List.length_eq_zero_iff] at hlen
      subst js
      exact (starRingEnd ℂ).mapMatrix.map_one.symm
  | cons i is ih =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [evalWord_cons, ih js hlen]
          exact ((starRingEnd ℂ).mapMatrix.map_mul (K j i) (evalWord K js is)).symm

/-- The physical adjoint generates the conjugate-transposed periodic operator family without
spatial reflection.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem mpo_physicalAdjointTensor (K : MPOTensor d D) (N : ℕ)
    (σ τ : Fin N → Fin d) :
    mpo (physicalAdjointTensor K) N σ τ = star (mpo K N τ σ) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_physicalAdjointTensor K _ _ (by simp),
    ← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

end MPOTensor
