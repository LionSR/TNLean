/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.LabelledOpenCoefficient
import TNLean.PEPS.TorusLabelledBondGeometry

/-!
# Native torus coordinates for open coefficients

The labelled endpoint sum agrees with the native four-leg contraction,
including parallel bonds and both incidences of self bonds. This coordinate
identity supplies the delta-exterior bridge used for the collared rectangular
specialization of SCP10, arXiv:1001.3807v3, Lemma 6.14.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS
open DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "X" => TorusVertex width height
local notation "E" => TorusLabelledBond width height

open Classical in
/-- Four native legs in top, right, down, left order, with incidence labels retained. -/
def torusLocalTupleEquiv (v : X) :
    LocalConfig torusLabelledBondTail torusLabelledBondHead (fun _ ↦ V) v ≃
      V × V × V × V where
  toFun η := (η (torusIncidentEndpoint v (true, true)),
    η (torusIncidentEndpoint v (false, false)),
    η (torusIncidentEndpoint v (true, false)),
    η (torusIncidentEndpoint v (false, true)))
  invFun c p := match (torusIncidentEndpointEquiv v) p with
    | (true, true) => c.1
    | (false, false) => c.2.1
    | (true, false) => c.2.2.1
    | (false, true) => c.2.2.2
  left_inv η := by
    funext p
    obtain ⟨⟨d, b⟩, rfl⟩ := (torusIncidentEndpointEquiv v).symm.surjective p
    cases d <;> cases b <;> rfl
  right_inv c := rfl

open Classical in
/-- Group the four independent bond-end labels anchored at each native vertex. -/
def torusEndpointTupleEquiv :
    EndpointConfig (fun _ : E ↦ V) ≃ (X → V × V × V × V) where
  toFun β v := (β ((v, false), false), β ((v, false), true),
    β ((v, true), false), β ((v, true), true))
  invFun γ p := if p.1.2 then if p.2 then (γ p.1.1).2.2.2 else (γ p.1.1).2.2.1
    else if p.2 then (γ p.1.1).2.1 else (γ p.1.1).1
  left_inv β := by
    funext p
    rcases p with ⟨⟨v, d⟩, b⟩
    cases d <;> cases b <;> rfl
  right_inv γ := rfl

omit [DecidableEq V] in
open Classical in
/-- Exact equality of native and independently labelled contractions. -/
theorem labelledNetwork_eq_torusBondNetwork
    (A : X → (V × V × V × V) → ℂ) (O : E → Matrix V V ℂ) :
    network torusLabelledBondTail torusLabelledBondHead (fun _ ↦ V)
      (fun v η (_ : PUnit.{1}) ↦ A v (torusLocalTupleEquiv v η)) O (fun _ ↦ PUnit.unit.{1}) =
    torusBondNetwork A (fun v ↦ O (v, false)) (fun v ↦ O (v, true)) := by
  unfold network
  rw [← (torusEndpointTupleEquiv (width := width) (height := height) (V := V)).symm.sum_comp]
  unfold torusBondNetwork
  apply Finset.sum_congr rfl
  intro γ _
  apply congrArg₂ (· * ·)
  · unfold bondWeight
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro v _
    rw [Fintype.prod_bool]
    exact mul_comm _ _
  · apply Finset.prod_congr rfl
    intro v _
    rfl

open Classical in
/-- Native open coefficient with fixed region site coefficients and arbitrary
internal matrices. Boundary indices are only the actual crossing incidences. -/
def torusOpenCoefficient (R : Set X) (A : R → (V × V × V × V) → ℂ)
    (O : E → Matrix V V ℂ)
    (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V) : ℂ :=
  openCoefficient torusLabelledBondTail torusLabelledBondHead R
    (fun v η ↦ A v (torusLocalTupleEquiv v.1 η)) O θ

open Classical in
/-- Delta completion in the native four-leg coordinates, after fixing all
physical indices of the region tensors. -/
def torusDeltaCompletedTensor (R : Set X) (A : R → (V × V × V × V) → ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V)
    (v : X) (c : V × V × V × V) : ℂ :=
  deltaCompletedTensor torusLabelledBondTail torusLabelledBondHead R
    (fun w η ↦ A w (torusLocalTupleEquiv w.1 η)) v₀ θ v
    ((torusLocalTupleEquiv v).symm c) PUnit.unit.{1}

open Classical in
/-- The exact delta-exterior bridge in native torus coordinates. -/
theorem torusBondNetwork_deltaCompletedTensor
    (R : Set X) (A : R → (V × V × V × V) → ℂ) (O : E → Matrix V V ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V) :
    torusBondNetwork (torusDeltaCompletedTensor R A v₀ θ)
      (fun v ↦ internalBondMatrices torusLabelledBondTail torusLabelledBondHead R O (v, false))
      (fun v ↦ internalBondMatrices torusLabelledBondTail torusLabelledBondHead R O (v, true)) =
        torusOpenCoefficient R A O θ := by
  rw [← labelledNetwork_eq_torusBondNetwork]
  simpa only [torusDeltaCompletedTensor, Equiv.symm_apply_apply, torusOpenCoefficient] using
    network_deltaCompletedTensor torusLabelledBondTail torusLabelledBondHead R
      (fun v η ↦ A v (torusLocalTupleEquiv v.1 η)) O v₀ θ

end TNLean.PEPS
