/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusInitialStringRightPhysicalStep
import TNLean.PEPS.TorusSecondStringPhysicalCrossing
/-!
# Two physical endpoint steps in the four-flux configuration

The first rightward movement is followed by an upward crossing. Both original
spin operations are selected before the two flux labels. Their product acts on
the actual closed contraction, with every other bond operator retained.
Source: SCP10, arXiv:1001.3807, Theorem 6.16 and Section 6.6, lines 2271–2305
and 2361–2415. This is an auxiliary two-step route, not the full braid or its
partner-reunion operation.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance routeWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]
/-- The first literal update is internal to its actual six-site tile.
Source: SCP10, the elementary movement in lines 2271–2305. -/
theorem torusSweptStringRightStep_extension_initial (v : X) (g h : G) :
    regularRegionBondExtension (translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1))
      (torusSweptStringRightStepOperators v g h) (torusSweptStringInitialOperators v g h) =
      torusSweptStringRightStepOperators v g h := by
  classical
  let p : X := (v.1 + 1, v.2 + 1)
  let R := translatedTwoPlaquetteRegion p
  have hv (i : Fin 6) : (translatedTwoPlaquetteIso p i).1 =
      (p.1 + ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod width),
       p.2 + ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod height)) := by
    change (((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod width) + p.1,
      ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod height) + p.2) = _
    simp only [add_comm]
  have hx : (v.1 + 2, v.2 + 1) ∈ R := by
    have H := (translatedTwoPlaquetteIso p 1).2
    rw [hv 1] at H
    norm_num [p, add_assoc] at H
    exact H
  have hy : (v.1 + 2, v.2 + 1 + 1) ∈ R := by
    have H := (translatedTwoPlaquetteIso p 4).2
    rw [hv 4] at H
    norm_num [p, add_assoc] at H
    simpa only [add_assoc, one_add_one_eq_two] using H
  have he : (torusUpEdge ((v.1 + 2, v.2 + 1) : X)).1.1 ∈ R ∧
      (torusUpEdge ((v.1 + 2, v.2 + 1) : X)).1.2 ∈ R := by
    change (Edge.ofAdj (torusGraph_adj_up (v.1 + 2) (v.2 + 1))).1.1 ∈ R ∧
      (Edge.ofAdj (torusGraph_adj_up (v.1 + 2) (v.2 + 1))).1.2 ∈ R
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up (v.1 + 2) (v.2 + 1)) with
      ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simpa only [ha, hb] using And.intro hx hy
    · simpa only [ha, hb] using And.intro hy hx
  funext e
  change (if _he : e.1.1 ∈ R ∧ e.1.2 ∈ R then _ else _) = _
  split_ifs with hi
  · rfl
  · have hn : e ≠ torusUpEdge ((v.1 + 2, v.2 + 1) : X) := by
      rintro rfl
      exact hi he
    simp only [torusSweptStringRightStepOperators, ite_eq_right hn]
variable [Fintype G] [DecidableEq G] {d : ℕ}
/-- Two fixed original-spin operations give the actual composed closed-state
identity. No holonomy or contraction identity is supplied. Source: SCP10,
Theorem 6.16 and the four-endpoint route, lines 2271–2415. -/
theorem IsGIsometric.exists_unitary_torusTwoStepStringRoute
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R₁ := translatedTwoPlaquetteRegion ((v.1 + 1, v.2 + 1) : X)
    let R₂ := verticalTwoPlaquetteRegion (torusSecondStringCrossingBase v)
    ∃ W₁ : Matrix ({x : X // x ∈ R₁} → Fin d) ({x : X // x ∈ R₁} → Fin d) ℂ,
    ∃ W₂ : Matrix ({x : X // x ∈ R₂} → Fin d) ({x : X // x ∈ R₂} → Fin d) ℂ,
      W₁ ∈ Matrix.unitaryGroup ({x : X // x ∈ R₁} → Fin d) ℂ ∧
      W₂ ∈ Matrix.unitaryGroup ({x : X // x ∈ R₂} → Fin d) ℂ ∧
      regionLocalTerm R₁ W₁ ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      regionLocalTerm R₂ W₂ ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      regionLocalTerm R₂ W₂ * regionLocalTerm R₁ W₁ ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      ∀ g h : G,
        let ψ₀ := stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusSweptStringInitialOperators v g h)))
        let ψ₁ := stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusSweptStringRightStepOperators v g h)))
        let ψ₂ := stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusSecondStringCrossingOutput v g h)))
        regionLocalTerm R₁ W₁ *ᵥ ψ₀ = ψ₁ ∧
        regionLocalTerm R₂ W₂ *ᵥ ψ₁ = ψ₂ ∧
        (regionLocalTerm R₂ W₂ * regionLocalTerm R₁ W₁) *ᵥ ψ₀ = ψ₂ := by
  obtain ⟨W₁, hW₁, hT₁, _, hact₁⟩ :=
    ha.exists_unitary_torusInitialStringRightPhysicalStep v
  obtain ⟨W₂, hW₂, hT₂, _, hact₂⟩ :=
    ha.exists_unitary_torusSecondStringCrossing v
  refine ⟨W₁, W₂, hW₁, hW₂, hT₁, hT₂, mul_mem hT₂ hT₁, ?_⟩
  intro g h
  have H := hact₁ g h (torusSweptStringInitialOperators v g h)
  have hid : regularRegionBondExtension
      (translatedTwoPlaquetteRegion ((v.1 + 1, v.2 + 1) : X))
      (torusSweptStringInitialOperators v g h) (torusSweptStringInitialOperators v g h) =
      torusSweptStringInitialOperators v g h := by
    classical
    funext e
    simp [regularRegionBondExtension]
  rw [hid, torusSweptStringRightStep_extension_initial v g h] at H
  refine ⟨H, hact₂ g h, ?_⟩
  rw [← Matrix.mulVec_mulVec, H]
  exact hact₂ g h
end TNLean.PEPS
