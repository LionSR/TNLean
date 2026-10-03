/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusActualRouteFluxMove
import TNLean.PEPS.TorusSweptRouteBondAssignments
/-!
# Fixed original-spin operations in the four plaquette directions

Each actual target vacancy makes the literal one-bond update a fixed physical
operation. The continuing partner strings and all exterior and crossing
operators remain part of the arbitrary input. No tree background or state
identity is supplied.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305, and the
four-endpoint route in Section 6.6, lines 2340–2423.

**Scope restriction (finite torus and regular action):** This consumer uses the
route's width at least eight and height at least seven. All positions and both
periodic seams are allowed. It is an elementary-operation statement, not the
complete braid. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance vacantMoveWidthFour : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance vacantMoveHeightFour : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance vacantMoveWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance vacantMoveHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance vacantMoveWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance vacantMoveHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private def horizontal (direction : Fin 4) : Bool := direction = 0 ∨ direction = 2
private def reverse (direction : Fin 4) : Bool := direction = 2 ∨ direction = 3
private def tile (direction : Fin 4) (p : X) : X :=
  if direction = 2 then (p.1 - 1, p.2)
  else if direction = 3 then (p.1, p.2 - 1) else p

/-- The actual six-site tile for motion from the given source plaquette.
Directions are right, up, left and down. Source: SCP10, lines 2340–2423. -/
def torusVacantPlaquetteMoveRegion (direction : Fin 4) (p : X) : Finset X :=
  torusRouteStepRegion (horizontal direction) (tile direction p)

/-- The actual neighbouring target of the elementary move.
Source: SCP10, the physical endpoint route, lines 2340–2423. -/
def torusVacantPlaquetteMoveTarget (direction : Fin 4) (p : X) : X :=
  if direction = 0 then (p.1 + 1, p.2)
  else if direction = 1 then (p.1, p.2 + 1)
  else if direction = 2 then (p.1 - 1, p.2) else (p.1, p.2 - 1)

variable {G : Type*} [Group G] [Fintype G]
omit [Fintype G] in
private theorem update_eq (direction : Fin 4) (p : X) (u : Edge Γₜ → G) :
    torusActualRouteFluxUpdate (horizontal direction) (reverse direction) (tile direction p) u =
      torusVacatingPlaquetteMove direction p u := by
  rw [torusActualRouteFluxUpdate_formula]
  fin_cases direction <;>
    simp [horizontal, reverse, tile, torusVacatingPlaquetteMove, sub_eq_add_neg, add_assoc] <;>
    norm_num

omit [Fintype G] in
private theorem vacancy (direction : Fin 4) (p : X) (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u
      (torusPlaquetteWalk (torusVacantPlaquetteMoveTarget direction p)).reverse = 1) :
    regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse direction then tile direction p else if horizontal direction then
        ((tile direction p).1 + 1, (tile direction p).2)
      else ((tile direction p).1, (tile direction p).2 + 1))) = 1 := by
  have H := congrArg Inv.inv hv
  rw [regularWalkHolonomy_reverse, inv_inv, inv_one] at H
  fin_cases direction <;> simpa [horizontal, reverse, tile, torusVacantPlaquetteMoveTarget] using H

/-- One fixed six-spin operation implements the actual literal update for each
direction, before every input, boundary configuration and actual vacancy proof.
Its identity extension gives the same action on the actual closed state.
Source: SCP10, Theorem 6.16 and Section 6.6, lines 2271–2305 and 2340–2423. -/
theorem IsGIsometric.exists_unitary_torusVacantPlaquetteMove {d : ℕ}
    {a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ}
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (direction : Fin 4) (p : X) :
    ∃ W : Matrix ({v : X // v ∈ torusVacantPlaquetteMoveRegion direction p} → Fin d)
        ({v : X // v ∈ torusVacantPlaquetteMoveRegion direction p} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup
        ({v : X // v ∈ torusVacantPlaquetteMoveRegion direction p} → Fin d) ℂ ∧
      (if reverse direction then
        (regionLocalTerm (torusVacantPlaquetteMoveRegion direction p) W).conjTranspose
        else regionLocalTerm (torusVacantPlaquetteMoveRegion direction p) W) ∈
          Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (u : Edge Γₜ → G), regularWalkHolonomy u
          (torusPlaquetteWalk (torusVacantPlaquetteMoveTarget direction p)).reverse = 1 →
        ∀ θ : {e : Edge Γₜ // IsRegionBoundaryEdge
          (torusVacantPlaquetteMoveRegion direction p) e} → G,
        (if reverse direction then W.conjTranspose else W) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite a u))
            (torusVacantPlaquetteMoveRegion direction p) (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (torusVacatingPlaquetteMove direction p u)))
          (torusVacantPlaquetteMoveRegion direction p) (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (u : Edge Γₜ → G), regularWalkHolonomy u
          (torusPlaquetteWalk (torusVacantPlaquetteMoveTarget direction p)).reverse = 1 →
        (if reverse direction then
          (regionLocalTerm (torusVacantPlaquetteMoveRegion direction p) W).conjTranspose
          else regionLocalTerm (torusVacantPlaquetteMoveRegion direction p) W) *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (torusVacatingPlaquetteMove direction p u))) := by
  obtain ⟨W, hW, hG, hl, hg⟩ := IsGIsometric.exists_unitary_torusActualRouteFluxUpdate ha
    (horizontal direction) (tile direction p)
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · split_ifs
    · exact Unitary.star_mem hG
    · exact hG
  · intro u hv θ
    have Hv := (torusActualRouteVacancy_iff (horizontal direction) (reverse direction)
      (tile direction p) u).mpr (vacancy direction p u hv)
    have H := hl (reverse direction) u Hv θ
    rw [update_eq direction p u] at H
    exact H
  · intro u hv
    have Hv := (torusActualRouteVacancy_iff (horizontal direction) (reverse direction)
      (tile direction p) u).mpr (vacancy direction p u hv)
    have H := hg (reverse direction) u Hv
    rw [update_eq direction p u] at H
    exact H
end TNLean.PEPS
