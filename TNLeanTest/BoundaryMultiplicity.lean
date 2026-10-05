/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryMultiplicity

/-!
# Source fusion and action multiplicity regressions

These signatures use the original physical alphabet. Neither an independent
length, a fusion law, nor a NIM relation is an input to the final source test.
-/

-- These regressions intentionally inspect declaration and kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace BoundaryMultiplicityTest

example {d g : ℕ} {D : Fin g → ℕ} {A : ∀ c, MPSTensor d (D c)}
    {L : ℕ} (hSpan : MPSTensor.WordTupleSpanTop A L) (hD : ∀ c, 0 < D c) :
    LinearIndependent ℂ (fun c ↦ fun w : Fin L → Fin d ↦ MPSTensor.mpv (A c) w) :=
  hSpan.linearIndependent_mpv hD

example {d r : ℕ} {χ : Fin r → ℕ} {O : ∀ a, MPOTensor d (χ a)}
    {N : Fin r → Fin r → Fin r → ℕ} (hfus : MPOTensor.IsMPOFusionAlgebra O N)
    (hInj : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (a b c q : Fin r) :
    ∑ e, N a b e * N e c q = ∑ f, N b c f * N a f q :=
  hfus.associative_of_isInjective hInj hχ hne a b c q

example {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
    (T : MPOTensor d (∑ a : Fin r, χ a))
    (B : MPSTensor d (∑ x : Fin s, D x)) (hT : MPOTensor.IsBoundaryClosed T)
    (hB : MPOTensor.IsBoundaryCompatible T B)
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hOp : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (O a).toMPSTensor))
    (hState : B = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    (hInjOp : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneOp : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hInjState : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
    (hneState : MPSTensor.BlocksNotGaugePhaseEquiv A) :
    ∃ (N : Fin r → Fin r → Fin r → ℕ) (M : Fin r → Fin s → Fin s → ℕ),
      MPOTensor.IsMPOFusionAlgebra O N ∧
      MPOTensor.IsMPOSymmetricFamily O A (fun a x y ↦ (M a x y : ℂ)) ∧
      MPOTensor.IsNIMRep N M ∧
      ∀ a b c q, ∑ e, N a b e * N e c q = ∑ f, N b c f * N a f q :=
  hT.exists_isNIMRep_of_isBoundaryCompatible hB O A hOp hState
    hInjOp hχ hneOp hInjState hD hneState

/--
info: 'MPSTensor.WordTupleSpanTop.linearIndependent_mpv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.WordTupleSpanTop.linearIndependent_mpv
/--
info: 'MPOTensor.IsMPOFusionAlgebra.associative_of_isInjective'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsMPOFusionAlgebra.associative_of_isInjective
/--
info: 'MPOTensor.IsBoundaryClosed.exists_isNIMRep_of_isBoundaryCompatible'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryClosed.exists_isNIMRep_of_isBoundaryCompatible

end BoundaryMultiplicityTest
