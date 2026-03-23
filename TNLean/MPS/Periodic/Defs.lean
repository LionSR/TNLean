/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Chain.Defs

/-!
# Periodic MPS definitions

This module provides a lightweight vocabulary layer for **periodic**
(translation-covariant up to a period) MPS data.

The current formal overlap machinery for normal tensors is developed in
`TNLean/MPS/Overlap/*`, while chain-level equalities live in
`TNLean/MPS/Chain/Defs`.  The present file intentionally stays minimal and
sorry-free: it introduces aliases and coercion-free wrappers used by the
periodic-overlap development.
-/

open scoped Matrix

/-- A periodic MPS with physical dimension `d`, bond dimension `D`, and period `m`.

Concretely this is an `m`-tuple of local tensors indexed cyclically by `Fin m`. -/
abbrev PeriodicMPSTensor (d D m : ℕ) := Fin m → MPSTensor d D

namespace PeriodicMPSTensor

variable {d D m : ℕ}

/-- Interpret a periodic tensor as a fixed-length chain tensor of length `m`. -/
abbrev toChain (A : PeriodicMPSTensor d D m) : MPSChainTensor d D m := A

/-- Configuration coefficient for one full period. -/
abbrev coeff (A : PeriodicMPSTensor d D m) (σ : Fin m → Fin d) : ℂ :=
  MPSChainTensor.coeff A σ

/-- Equality of the generated `m`-site periodic-chain states. -/
abbrev SameState (A B : PeriodicMPSTensor d D m) : Prop :=
  MPSChainTensor.SameState A B

/-- Cyclic gauge equivalence for period-`m` tensors. -/
abbrev GaugeEquiv (A B : PeriodicMPSTensor d D m) : Prop :=
  MPSChainTensor.GaugeEquiv A B

@[simp] lemma coeff_def (A : PeriodicMPSTensor d D m) (σ : Fin m → Fin d) :
    coeff A σ = Matrix.trace (MPSChainTensor.eval A σ) := rfl

@[simp] lemma sameState_iff_chain (A B : PeriodicMPSTensor d D m) :
    SameState A B ↔ MPSChainTensor.SameState A B := Iff.rfl

@[simp] lemma gaugeEquiv_iff_chain (A B : PeriodicMPSTensor d D m) :
    GaugeEquiv A B ↔ MPSChainTensor.GaugeEquiv A B := Iff.rfl

lemma SameState.refl (A : PeriodicMPSTensor d D m) : SameState A A :=
  MPSChainTensor.SameState.refl A

lemma SameState.symm {A B : PeriodicMPSTensor d D m} (h : SameState A B) :
    SameState B A :=
  MPSChainTensor.SameState.symm h

lemma SameState.trans {A B C : PeriodicMPSTensor d D m}
    (hAB : SameState A B) (hBC : SameState B C) :
    SameState A C :=
  MPSChainTensor.SameState.trans hAB hBC

lemma GaugeEquiv.refl (A : PeriodicMPSTensor d D m) : GaugeEquiv A A :=
  MPSChainTensor.GaugeEquiv.refl A

lemma GaugeEquiv.symm {A B : PeriodicMPSTensor d D m} (h : GaugeEquiv A B) :
    GaugeEquiv B A :=
  MPSChainTensor.GaugeEquiv.symm h

lemma GaugeEquiv.trans {A B C : PeriodicMPSTensor d D m}
    (hAB : GaugeEquiv A B) (hBC : GaugeEquiv B C) :
    GaugeEquiv A C :=
  MPSChainTensor.GaugeEquiv.trans hAB hBC

end PeriodicMPSTensor
