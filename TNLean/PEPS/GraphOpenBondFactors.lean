/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenSemiRegularSupport

/-!
# Actual boundary and internal factors in open bond coordinates

The existing open contraction splits into crossing-endpoint factors and
internal head-tail pairs. These definitions retain every virtual boundary
label and both edge orientations.

Source: SCP10, arXiv:1001.3807, regional contractions and Section 7,
lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]

/-- The actual one-ended boundary factor, with its orientation retained. -/
def graphOpenBoundaryFactor (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R) (θ x : X) : ℂ :=
  if h : e.1.1.1 ∈ R then (W * U (q ⟨e.1.1.1, h⟩)⁻¹) θ x
  else (U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩) * W) x θ

/-- The actual two-ended internal factor. -/
def graphOpenInternalFactor (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) (x : X × X) : ℂ :=
  (W ^ 2 * U (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹)) x.1 x.2

/-- The derived open contraction in crossing-endpoint and internal-pair coordinates. -/
def graphOpenBondCoordinates (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    ((RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) → ℂ :=
  fun β => graphOpenAveragingBondState U W R θ
    (β.1, (fun e => (β.2 e).2), fun e => (β.2 e).1)

/-- The open contraction is a coherent product with independent boundary
and internal factors. -/
theorem graphOpenBondCoordinates_eq_sum_prod
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    graphOpenBondCoordinates U W R θ = fun β => ∑ q : RV R → G,
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        (∏ e : RB (Γ := Γ) R, graphOpenBoundaryFactor U W R q e (θ e) (β.1 e)) *
        ∏ e : RI (Γ := Γ) R, graphOpenInternalFactor U W R q e (β.2 e) := by
  funext β
  unfold graphOpenBondCoordinates graphOpenAveragingBondState
    graphOpenBoundaryFactor graphOpenInternalFactor
  apply Finset.sum_congr rfl
  intro q _
  exact (mul_assoc _ _ _).symm.trans (mul_right_comm _ _ _)

end TNLean.PEPS
