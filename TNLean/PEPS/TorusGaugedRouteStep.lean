/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGaugedHorizontalFluxMove
import TNLean.PEPS.TorusGaugedVerticalFluxMove

/-!
# All four elementary original-spin route operations

A fixed family of original-spin operations moves neighboring plaquette fluxes
while both internal assignments are reconstructed from the same vertex gauge.
Its adjoint reverses the movement. All exterior and crossing operators remain
literally unchanged, so the same boundary transport applies on both sides.

Source: SCP10, arXiv:1001.3807, accessible coordinates, lines 1765–1920, and
Theorem 6.16, lines 2271–2305.

**Scope restriction (finite torus and regular action):** The actual horizontal
and vertical
six-site blocks require both periods at least four. Both periodic
seams are included. This common-background operation does not compare distinct
crossing presentations or establish the prescribed four-endpoint braid. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (3 < height)]
local instance routeStepWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance routeStepWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance routeStepHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance routeStepHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- Select the actual horizontal or vertical six-site movement tile.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusRouteStepRegion (horizontal : Bool) (p : X) : Finset X :=
  if horizontal then translatedTwoPlaquetteRegion p else verticalTwoPlaquetteRegion p

/-- The native internal assignment reconstructed by a common vertex gauge.
Source: SCP10, accessible coordinates and Theorem 6.16,
lines 1765–1920 and 2271–2305. -/
def torusRouteStepAssignment (horizontal : Bool) (p : X) :
    ({x : X // x ∈ torusRouteStepRegion horizontal p} → G) → Bool → G → Edge Γₜ → G :=
  match horizontal with
  | false => torusGaugedVerticalFluxAssignment p
  | true => torusGaugedHorizontalFluxAssignment p

private abbrev R (horizontal : Bool) (p : X) := torusRouteStepRegion horizontal p
private abbrev RV (horizontal : Bool) (p : X) := {x : X // x ∈ R horizontal p}

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- One family of original-spin unitaries implements all four directed elementary
steps before every common vertex gauge, insertion, boundary and literal exterior
assignment. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusRouteSteps
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ W : (horizontal : Bool) → (p : X) →
        Matrix (RV horizontal p → Fin d)
          (RV horizontal p → Fin d) ℂ,
      ∀ (horizontal : Bool) (p : X),
        W horizontal p ∈
        Matrix.unitaryGroup (RV horizontal p → Fin d) ℂ ∧
      regionLocalTerm (R horizontal p) (W horizontal p) ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (k : RV horizontal p → G) (reverse : Bool) (g : G) (u : Edge Γₜ → G)
        (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R horizontal p) e} → G),
        (if reverse then (W horizontal p).conjTranspose else W horizontal p) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R horizontal p)
              (torusRouteStepAssignment horizontal p k reverse g) u))) (R horizontal p)
            (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R horizontal p)
            (torusRouteStepAssignment horizontal p k (!reverse) g) u))) (R horizontal p)
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (k : RV horizontal p → G) (reverse : Bool) (g : G) (u : Edge Γₜ → G),
        (if reverse then (regionLocalTerm (R horizontal p) (W horizontal p)).conjTranspose
          else regionLocalTerm (R horizontal p) (W horizontal p)) *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R horizontal p)
              (torusRouteStepAssignment horizontal p k reverse g) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R horizontal p)
            (torusRouteStepAssignment horizontal p k (!reverse) g) u))) := by
  classical
  choose WH hWH hHglobal hHlocal hHact using
    fun p : X => ha.exists_unitary_torusGaugedHorizontalFluxMove p
  choose WV hWV hVglobal hVlocal hVact using
    fun p : X => ha.exists_unitary_torusGaugedVerticalFluxMove p
  let W (horizontal : Bool) (p : X) :
      Matrix (RV horizontal p → Fin d)
        (RV horizontal p → Fin d) ℂ := by
    cases horizontal
    · exact WV p
    · exact WH p
  refine ⟨W, ?_⟩
  intro horizontal p
  cases horizontal
  · exact ⟨hWV p, hVglobal p, hVlocal p, hVact p⟩
  · exact ⟨hWH p, hHglobal p, hHlocal p, hHact p⟩

end TNLean.PEPS
