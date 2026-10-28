/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalPhysicalSymmetry

/-! Axiom and hypothesis checks for normal physical symmetries. -/

set_option linter.hashCommand false

open TNLean.PEPS TNLean.Lattice

/-- info: 'TNLean.PEPS.regionBlockedTensorInjective_of_sameState_of_bondDim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regionBlockedTensorInjective_of_sameState_of_bondDim_eq

/-- info: 'TNLean.PEPS.gaugeEquiv_physicalTensorAction_of_normal_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.gaugeEquiv_physicalTensorAction_of_normal_symmetry

-- The symmetry matrix is arbitrary; transformed normality and d > 0 are derived.
example {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) g ↔ g = e)
    (hconn : G.Connected) (U : Matrix (Fin d) (Fin d) ℂ)
    (hSym : dependentPhysicalProductFamilyMap (fun _ : V => U) (stateCoeff A) =
      stateCoeff A) :
    GaugeEquiv A (physicalTensorAction A U) :=
  gaugeEquiv_physicalTensorAction_of_normal_symmetry A hA hsingle hconn U hSym
