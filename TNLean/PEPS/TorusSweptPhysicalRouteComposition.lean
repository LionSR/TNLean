/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusVacantPlaquettePhysicalMove
/-!
# Actual twelve-step original-spin endpoint motion

The literal recursive bond assignments have vacant targets at every step.
The fixed six-spin elementary operations therefore compose on the actual
closed state. Every operation is chosen before both initial flux labels.
Source: SCP10, arXiv:1001.3807, Section 6.6, lines 2340–2423.
This auxiliary finite-torus route does not assert an unrestricted braid or
an annihilation operation on the final partners.
**Scope restriction (finite torus and regular action):** The width is at least
eight and the height at least seven. Every position and both periodic seams
are allowed. The results concern the displayed endpoint route and its original
physical contractions. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance routeCompositionWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeCompositionHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeCompositionWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeCompositionHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeCompositionWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeCompositionHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private theorem target_eq (v : X) (i : Fin 12) :
    torusVacantPlaquetteMoveTarget (sweptPhysicalBRouteDirection i)
      (torusSweptPhysicalBRouteVertex v i.castSucc) =
        torusSweptPhysicalBRouteVertex v i.succ := by
  fin_cases i <;>
    simp [torusVacantPlaquetteMoveTarget, sweptPhysicalBRouteDirection,
      torusSweptPhysicalBRouteVertex, sweptPhysicalBRouteCoordinate,
      torusSweptPatchCoordinate, translate_apply] <;>
    ring_nf
variable {d : ℕ}
/-- Chronological products of the twelve physical operations, with the latest
operation acting on the left. Auxiliary to SCP10, lines 2340–2423. -/
def torusSweptPhysicalRouteProduct
    (M : Fin 12 → Matrix (X → Fin d) (X → Fin d) ℂ) :
    ℕ → Matrix (X → Fin d) (X → Fin d) ℂ
  | 0 => 1
  | n + 1 => if hn : n < 12 then M ⟨n,hn⟩ * torusSweptPhysicalRouteProduct M n
    else torusSweptPhysicalRouteProduct M n
variable {G : Type*} [Group G] [Fintype G]
private abbrev stepRegion (v : X) (i : Fin 12) :=
  torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
    (torusSweptPhysicalBRouteVertex v i.castSucc)
private theorem step_exists
    (a : (x : X) → (IncidentEdge Γₜ x → G) → Fin d → ℂ)
    (ha : ∀ x, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ x))
      (regularSiteMap (a x))) (v : X) (i : Fin 12) :
    ∃ M : Matrix (X → Fin d) (X → Fin d) ℂ,
      M ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∃ W : Matrix ({x : X // x ∈ stepRegion v i} → Fin d)
          ({x : X // x ∈ stepRegion v i} → Fin d) ℂ,
        W ∈ Matrix.unitaryGroup ({x : X // x ∈ stepRegion v i} → Fin d) ℂ ∧
          (M = regionLocalTerm (stepRegion v i) W ∨
            M = (regionLocalTerm (stepRegion v i) W).conjTranspose)) ∧
      ∀ g h : G,
        M *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (torusSweptPhysicalRouteOperators v g h i.val))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (torusSweptPhysicalRouteOperators v g h (i.val + 1)))) := by
  obtain ⟨W,hW,hM,_,hact⟩ := IsGIsometric.exists_unitary_torusVacantPlaquetteMove ha
    (sweptPhysicalBRouteDirection i) (torusSweptPhysicalBRouteVertex v i.castSucc)
  refine ⟨_,hM,⟨W,hW,?_⟩,?_⟩
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro g h
    have hv := regularWalkHolonomy_torusSweptPhysicalRoute_target_vacancy v g h i
    rw [← target_eq v i] at hv
    have H := hact (torusSweptPhysicalRouteOperators v g h i.val) hv
    have hrec : torusSweptPhysicalRouteOperators v g h (i.val + 1) =
        torusVacatingPlaquetteMove (sweptPhysicalBRouteDirection i)
          (torusSweptPhysicalBRouteVertex v i.castSucc)
          (torusSweptPhysicalRouteOperators v g h i.val) := by
      rw [torusSweptPhysicalRouteOperators, dite_eq_left i.isLt]
      rfl
    rw [hrec]
    exact H
/-- Twelve fixed elementary operations implement the literal route on the
actual original-spin state. Each factor is supported on its derived six-site
patch; all factors precede both initial flux labels. Source: SCP10,
Section 6.6, lines 2340–2423. This does not assert partner annihilation. -/
theorem IsGIsometric.exists_unitary_torusSweptPhysicalRoute
    (a : (x : X) → (IncidentEdge Γₜ x → G) → Fin d → ℂ)
    (ha : ∀ x, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ x))
      (regularSiteMap (a x))) (v : X) :
    ∃ M : Fin 12 → Matrix (X → Fin d) (X → Fin d) ℂ,
      (∀ i, M i ∈ Matrix.unitaryGroup (X → Fin d) ℂ) ∧
      (∀ i, ∃ W : Matrix
          ({x : X // x ∈ torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
            (torusSweptPhysicalBRouteVertex v i.castSucc)} → Fin d)
          ({x : X // x ∈ torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
            (torusSweptPhysicalBRouteVertex v i.castSucc)} → Fin d) ℂ,
        W ∈ Matrix.unitaryGroup _ ℂ ∧
          (M i = regionLocalTerm (torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
              (torusSweptPhysicalBRouteVertex v i.castSucc)) W ∨
            M i = (regionLocalTerm (torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
              (torusSweptPhysicalBRouteVertex v i.castSucc)) W).conjTranspose)) ∧
      (∀ (i : Fin 12) (g h : G),
        M i *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (torusSweptPhysicalRouteOperators v g h i.val))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (torusSweptPhysicalRouteOperators v g h (i.val + 1))))) ∧
      ∀ n ≤ 12,
        torusSweptPhysicalRouteProduct M n ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
        ∀ g h : G,
          torusSweptPhysicalRouteProduct M n *ᵥ
            stateCoeff (groupBondTensor (regularTwistedSite a
              (torusSweptStringInitialOperators v g h))) =
          stateCoeff (groupBondTensor (regularTwistedSite a
            (torusSweptPhysicalRouteOperators v g h n))) := by
  classical
  choose M hM hlocal hact using fun i => step_exists a ha v i
  refine ⟨M,hM,hlocal,hact,?_⟩
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨one_mem _,?_⟩
    intro g h
    simp [torusSweptPhysicalRouteProduct, torusSweptPhysicalRouteOperators]
  | succ n ih =>
    intro hn
    have hlt : n < 12 := by omega
    have HI := ih (by omega)
    rw [torusSweptPhysicalRouteProduct, dite_eq_left hlt]
    refine ⟨mul_mem (hM ⟨n,hlt⟩) HI.1,?_⟩
    intro g h
    rw [← Matrix.mulVec_mulVec, HI.2 g h]
    exact hact ⟨n,hlt⟩ g h
end TNLean.PEPS
