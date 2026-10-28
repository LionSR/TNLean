/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalVirtualRepresentation

/-! Axiom and hypothesis checks for projective bond representations. -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.exists_virtualRepresentation_of_normal_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_virtualRepresentation_of_normal_symmetry

open scoped Matrix

open TNLean.PEPS TNLean.Lattice

-- The projective homomorphisms and their actual implementing lifts are derived.
example {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {H : Type} [Group H]
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e f : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) f ↔ f = e)
    (hconn : G.Connected) (U : H →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ g : H,
      dependentPhysicalProductFamilyMap (fun _ : V => U g) (stateCoeff A) =
        stateCoeff A) :
    ∃ X : H → (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
      ∃ R : (e : Edge G) → H →* Matrix.ProjGenLinGroup (Fin (A.bondDim e)) ℂ,
        (∀ (e : Edge G) (g : H), R e g = Matrix.ProjGenLinGroup.mk (X g e)) ∧
        ∀ (g : H) (v : V)
          (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
          (physicalTensorAction A (U g)).component v η σ =
            gaugeVertex A (fun e => X (g⁻¹) e) v η σ := by
  obtain ⟨_ω, X, R, hR, hTensor, _hMul, _hCocycle⟩ :=
    exists_virtualRepresentation_of_normal_symmetry A hA hsingle hconn U hSym
  exact ⟨X, R, hR, hTensor⟩
