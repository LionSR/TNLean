/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.VerticalTwoPlaquetteGeometry
import TNLean.PEPS.RegularCycleGlobalPermutation
import TNLean.PEPS.RegularTorusEntropy
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Vertical movement of a flux on the original six spins

The actual two-by-three induced block supplies the tree, root and horizontal
chords. A rightward transport g on the lower chord is extended to the middle
chord; the adjoint reverses this movement. Native sorting assigns g⁻¹ at the
horizontal seam. The two actual
counterclockwise plaquette holonomies change from (g,1) to (1,g).

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305.
This finite-torus regular-action realization assumes width at least three and
height at least four. Every position and both seams are included; no
parent-Hamiltonian conclusion is asserted. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance verticalMoveWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance verticalMoveHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance verticalMoveHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

private def verticalFluxInsertionElement (v : X) (g : G) : G :=
  if v.1.val < (v.1+1).val then g else g⁻¹

/-- Literal rightward insertion on the lower horizontal bond, optionally extended
onto the middle horizontal bond. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusVerticalFluxAssignment (v : X) (extend : Bool) (g : G) (e : Edge Γₜ) : G :=
  if e = Edge.ofAdj (torusGraph_adj_right v.1 v.2) ∨
    (extend = true ∧ e = Edge.ofAdj (torusGraph_adj_right v.1 (v.2+1)))
  then verticalFluxInsertionElement v g else 1

/-- The literal native insertion is the internally derived cycle assignment.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusVerticalFluxAssignment_eq_treeCycleAssignment
    (v : X) (extend : Bool) (g : G) :
    torusVerticalFluxAssignment v extend g =
      regularTreeCycleAssignment (verticalTwoPlaquetteRegion v) (verticalTwoPlaquetteTree v)
        (fun e => if e = verticalTwoPlaquetteCycleBond v 0 ∨
          (extend = true ∧ e = verticalTwoPlaquetteCycleBond v 1)
          then verticalFluxInsertionElement v g else 1) := by
  classical
  rw [regularTreeCycleAssignment_twoSupport]
  funext e
  simp [verticalTwoPlaquetteCycleBond_eq_right, torusVerticalFluxAssignment]

omit [Fact (2 < width)] [Fact (3 < height)] in
private theorem right_lt_iff (x : ZMod width) (y : ZMod height) :
    ((x,y) : X) < (x+1,y) ↔ x.val < (x+1).val := by
  change toLex (x.val,y.val) < toLex ((x+1).val,y.val) ↔ _
  simp [Prod.Lex.toLex_lt_toLex]

/-- Directed transport cancels sorting inversions, including the horizontal seam.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusVerticalFluxAssignment_right_transport (v : X) (extend : Bool) (g : G) :
    regularDirectedTransport (torusVerticalFluxAssignment v extend g)
      (torusGraph_adj_right v.1 v.2) = g ∧
    regularDirectedTransport (torusVerticalFluxAssignment v extend g)
      (torusGraph_adj_right v.1 (v.2+1)) = (if extend then g else 1) := by
  have hne : Edge.ofAdj (torusGraph_adj_right v.1 (v.2+1)) ≠
      Edge.ofAdj (torusGraph_adj_right v.1 v.2) := by
    simp [Edge.ofAdj_eq_iff_endpoints]
  simp only [regularDirectedTransport, right_lt_iff, torusVerticalFluxAssignment,
    hne, false_or, and_true, verticalFluxInsertionElement]
  by_cases h : v.1.val < (v.1+1).val <;> cases extend <;> simp [h]

/-- The actual two counterclockwise plaquette holonomies move vertically.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularWalkHolonomy_torusVerticalFluxAssignment
    (v : X) (extend : Bool) (g : G) :
    regularWalkHolonomy (torusVerticalFluxAssignment v extend g) (torusPlaquetteWalk v) =
        (if extend then 1 else g) ∧
      regularWalkHolonomy (torusVerticalFluxAssignment v extend g)
        (torusPlaquetteWalk (v.1,v.2+1)) = (if extend then g else 1) := by
  let u := torusVerticalFluxAssignment v extend g
  have hV (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport u (torusGraph_adj_up x y) = 1 := by
    have hn (b : ZMod height) : Edge.ofAdj (torusGraph_adj_up x y) ≠
        Edge.ofAdj (torusGraph_adj_right v.1 b) := by
      intro h
      simp only [Edge.ofAdj_eq_iff_endpoints, Prod.mk.injEq] at h
      rcases h with ⟨⟨h₀,_⟩,⟨h₁,_⟩⟩ | ⟨⟨h₀,_⟩,⟨h₁,_⟩⟩ <;> simp_all
    simp [u, regularDirectedTransport, torusVerticalFluxAssignment, hn]
  have htwo : (2 : ZMod height) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [show (2 : ZMod height) = ((2 : ℕ) : ZMod height) by rfl,
      ZMod.val_natCast_of_lt (by have := Fact.out (p := 3 < height); omega),
      ZMod.val_zero] at hh
    omega
  have hy₂ : v.2+1+1 ≠ v.2 := by
    intro h
    have h' : v.2 + (2 : ZMod height) = v.2 + 0 := by
      simpa only [add_assoc, one_add_one_eq_two, add_zero] using h
    exact htwo (add_left_cancel h')
  have hTop : regularDirectedTransport u
      (torusGraph_adj_right v.1 (v.2+1+1)) = 1 := by
    have h₀ : Edge.ofAdj (torusGraph_adj_right v.1 (v.2+1+1)) ≠
        Edge.ofAdj (torusGraph_adj_right v.1 v.2) := by
      simp [Edge.ofAdj_eq_iff_endpoints, hy₂]
    have h₁ : Edge.ofAdj (torusGraph_adj_right v.1 (v.2+1+1)) ≠
        Edge.ofAdj (torusGraph_adj_right v.1 (v.2+1)) := by
      simp [Edge.ofAdj_eq_iff_endpoints]
    simp [u, regularDirectedTransport, torusVerticalFluxAssignment, h₀, h₁]
  obtain ⟨hL,hM⟩ := torusVerticalFluxAssignment_right_transport v extend g
  change regularDirectedTransport u (torusGraph_adj_right v.1 v.2) = g at hL
  change regularDirectedTransport u (torusGraph_adj_right v.1 (v.2+1)) =
    (if extend then g else 1) at hM
  constructor
  · rw [regularWalkHolonomy_torusPlaquetteWalk, hV, hM, hV, hL]
    cases extend <;> simp
  · rw [regularWalkHolonomy_torusPlaquetteWalk, hV, hTop, hV, hM]
    simp

variable [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev R (v : X) := verticalTwoPlaquetteRegion v
private abbrev T (v : X) := verticalTwoPlaquetteTree v
private abbrev RV (v : X) := {x : X // x ∈ R v}

/-- A fixed original six-spin unitary moves flux upward; its adjoint moves it
downward. Both identities hold locally and in every global contraction, before
all flux, boundary and exterior labels.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusVerticalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix (RV v → Fin d) (RV v → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV v → Fin d) ℂ ∧
      regionLocalTerm (R v) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (reverse : Bool) (g : G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G),
        (if reverse then W.conjTranspose else W) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusVerticalFluxAssignment v reverse g))) (R v)
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusVerticalFluxAssignment v (!reverse) g))) (R v)
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (reverse : Bool) (g : G) (u : Edge Γₜ → G),
        (if reverse then (regionLocalTerm (R v) W).conjTranspose
          else regionLocalTerm (R v) W) *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v) (torusVerticalFluxAssignment v reverse g) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v)
            (torusVerticalFluxAssignment v (!reverse) g) u))) := by
  classical
  let e₀ := verticalTwoPlaquetteCycleBond v 0
  let e₁ := verticalTwoPlaquetteCycleBond v 1
  have hne : e₀ ≠ e₁ := (verticalTwoPlaquetteCycleBond_injective v).ne (by decide)
  let ω := fun b : Bool => fun g : G => fun e =>
    if e = e₀ ∨ (b = true ∧ e = e₁) then verticalFluxInsertionElement v g else 1
  have hm (g : G) : regularTwoCycleMove e₀ e₁ hne (ω false g) = ω true g := by
    simpa [ω] using regularTwoCycleMove_single e₀ e₁ hne (verticalFluxInsertionElement v g)
  have hc (b : Bool) (g : G) :
      regularTreeCycleAssignment (R v) (T v) (ω b g) =
        torusVerticalFluxAssignment v b g :=
    (torusVerticalFluxAssignment_eq_treeCycleAssignment v b g).symm
  obtain ⟨W, hW, hglobal, hlocal, hact⟩ := exists_unitary_regularCycleGlobalPermutation
    (R v) (T v) (torusIncidentSite (width := width) (height := height) a)
    (fun x => ha.isGIsometric_torusIncidentSite x)
    (verticalTwoPlaquetteTree_le v) (verticalTwoPlaquetteTree_isTree v)
    (verticalTwoPlaquetteIso v 0) (regularTwoCycleMove e₀ e₁ hne)
    (regularTwoCycleMove_conjugation e₀ e₁ hne)
  have hWgram : W.conjTranspose * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  have hUgram : (regionLocalTerm (R v) W).conjTranspose *
      regionLocalTerm (R v) W = 1 := Matrix.mem_unitaryGroup_iff'.mp hglobal
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro reverse g θ
    have h := hlocal (ω false g) θ
    rw [hm, hc, hc] at h
    cases reverse
    · exact h
    · change W.conjTranspose *ᵥ _ = _
      rw [← h, Matrix.mulVec_mulVec, hWgram, Matrix.one_mulVec]
      rfl
  · intro reverse g u
    have h := hact (ω false g) u
    rw [hm, hc, hc] at h
    cases reverse
    · exact h
    · change (regionLocalTerm (R v) W).conjTranspose *ᵥ _ = _
      rw [← h, Matrix.mulVec_mulVec, hUgram, Matrix.one_mulVec]
      rfl

end TNLean.PEPS
