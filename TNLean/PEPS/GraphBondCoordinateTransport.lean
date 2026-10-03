/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphAveragingBondState
import TNLean.PEPS.BondCoordinateTransport
import TNLean.PEPS.PhysicalCoherentTransport

/-!
# Fourier coordinate transport of actual graph states

A rectangular virtual coordinate change induces an operation on each physical
bond pair. The product of these operations carries the actual averaging graph
contraction to its coordinate-transformed contraction. The hypothesis concerns
only the representation matrices; the global state identity is derived.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G In Out : Type*} [Group G] [Fintype G]
variable [Fintype In] [DecidableEq In] [Fintype Out] [DecidableEq Out]

/-- A representation intertwiner transports the actual regrouped graph contraction.
Source: SCP10, Section 7, lines 2938–3019. -/
theorem physicalProductMap_bondCoordinateMatrix_graphAveragingSite
    (Q : Matrix Out In ℂ) (U : G →* Matrix In In ℂ) (L : G →* Matrix Out Out ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) :
    physicalProductMap (Edge Γ) (bondCoordinateMatrix Q)
      (graphBondRegrouping (Γ := Γ) (graphBondNetwork (graphAveragingSite U))) =
      graphBondRegrouping (graphBondNetwork (graphAveragingSite L)) := by
  classical
  rw [graphBondRegrouping_averagingSite_coherent,
    graphBondRegrouping_averagingSite_coherent]
  apply physicalProductMap_sum_prod_eq
    (bondCoordinateMatrix Q)
    (fun _ : V → G => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V)
    (fun (e : Edge Γ) (q : V → G) (a : In × In) => U (q e.1.2 * (q e.1.1)⁻¹) a.1 a.2)
    (fun (e : Edge Γ) (q : V → G) (a : Out × Out) => L (q e.1.2 * (q e.1.1)⁻¹) a.1 a.2)
  intro e q
  rw [bondCoordinateMatrix_mulVec, ← hL]
end TNLean.PEPS
