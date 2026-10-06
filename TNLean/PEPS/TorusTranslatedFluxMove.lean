/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TranslatedTwoPlaquetteGeometry
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.RegularTorusEntropy
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# A six-spin flux movement at every torus position

The translated two-plaquette geometry supplies the actual region, spanning tree,
root and two distinct non-tree bonds. The literal insertion gives directed
upward transport `g` on the left bond and extends that transport to the middle
bond. At the vertical seam both native ordered bonds reverse together, so both
receive `g⁻¹`; this is proved from the native endpoint order. The actual
counterclockwise plaquette holonomies change from `(g⁻¹, 1)` to `(1, g⁻¹)`.

One fixed original-spin unitary effects this change for every group label and
boundary column. Its identity extension effects the corresponding change in the
actual globally contracted torus state for every common exterior and crossing
assignment. Translation invariance of the state is not a hypothesis.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, local source lines 2271–2305.

**Scope restriction (finite-torus regular flux movement):** The horizontal
period is at least four and the vertical period at least three, and the virtual
action is regular. All starting positions, including both periodic seams, are
allowed. No parent-Hamiltonian ground-space assertion is made. The remaining
unrestricted lattice scope is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance translatedFluxMoveWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance translatedFluxMoveWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance translatedFluxMoveHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

private def translatedFluxInsertionElement (v : X) (g : G) : G :=
  if v.2.val < (v.2 + 1).val then g else g⁻¹

/-- The literal upward insertion on the left vertical bond, with optional extension
to the middle bond. Its ordered operator is inverted at the vertical seam.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusTranslatedFluxAssignment (v : X) (extend : Bool) (g : G) (e : Edge Γₜ) : G :=
  if e = Edge.ofAdj (torusGraph_adj_up v.1 v.2) ∨
    (extend = true ∧ e = Edge.ofAdj (torusGraph_adj_up (v.1 + 1) v.2))
  then translatedFluxInsertionElement v g else 1

/-- The actual directed insertion is the derived tree-cycle assignment, using
the same ordered operator on both selected bonds.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusTranslatedFluxAssignment_eq_treeCycleAssignment
    (v : X) (extend : Bool) (g : G) :
    torusTranslatedFluxAssignment v extend g =
      regularTreeCycleAssignment (translatedTwoPlaquetteRegion v) (translatedTwoPlaquetteTree v)
        (fun e => if e = translatedTwoPlaquetteCycleBond v 0 ∨
          (extend = true ∧ e = translatedTwoPlaquetteCycleBond v 1)
          then translatedFluxInsertionElement v g else 1) := by
  classical
  rw [regularTreeCycleAssignment_twoSupport]
  funext e
  simp [translatedTwoPlaquetteCycleBond_eq_up, torusTranslatedFluxAssignment]

omit [Fact (3 < width)] [Fact (2 < height)] in
private theorem up_lt_iff (x : ZMod width) (y : ZMod height) :
    ((x,y) : X) < (x,y+1) ↔ y.val < (y+1).val := by
  change toLex (x.val,y.val) < toLex (x.val,(y+1).val) ↔ _
  simp [Prod.Lex.toLex_lt_toLex]

/-- The literal assignment has directed upward transports `g` and either `g`
or the identity, including the vertical seam.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusTranslatedFluxAssignment_up_transport (v : X) (extend : Bool) (g : G) :
    regularDirectedTransport (torusTranslatedFluxAssignment v extend g)
      (torusGraph_adj_up v.1 v.2) = g ∧
    regularDirectedTransport (torusTranslatedFluxAssignment v extend g)
      (torusGraph_adj_up (v.1+1) v.2) = (if extend then g else 1) := by
  classical
  have hne : Edge.ofAdj (torusGraph_adj_up (v.1+1) v.2) ≠
      Edge.ofAdj (torusGraph_adj_up v.1 v.2) := by
    intro h
    have hc : translatedTwoPlaquetteCycleBond v 1 = translatedTwoPlaquetteCycleBond v 0 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa only [translatedTwoPlaquetteCycleBond_eq_up, Fin.val_zero, Fin.val_one,
        Nat.cast_zero, Nat.cast_one, add_zero] using h
    exact (translatedTwoPlaquetteCycleBond_injective v).ne (by decide) hc
  simp only [regularDirectedTransport, up_lt_iff, torusTranslatedFluxAssignment,
    hne, false_or, and_true, translatedFluxInsertionElement]
  by_cases h : v.2.val < (v.2+1).val <;> cases extend <;> simp [h]

private theorem horizontal_ne_vertical (x a : ZMod width) (y b : ZMod height) :
    Edge.ofAdj (torusGraph_adj_right x y) ≠ Edge.ofAdj (torusGraph_adj_up a b) := by
  apply Edge.ofAdj_ne_of_endpoint_coordinates (torusGraph_adj_right x y)
    (torusGraph_adj_up a b) Prod.fst rfl
  by_cases hx : x = a
  · exact Or.inr (by rw [← hx]; simp)
  · exact Or.inl hx

/-- The actual counterclockwise plaquette holonomies move from `(g⁻¹, 1)` to
`(1, g⁻¹)` at every starting position, including both seams.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularWalkHolonomy_torusTranslatedFluxAssignment
    (v : X) (extend : Bool) (g : G) :
    regularWalkHolonomy (torusTranslatedFluxAssignment v extend g) (torusPlaquetteWalk v) =
        (if extend then 1 else g⁻¹) ∧
      regularWalkHolonomy (torusTranslatedFluxAssignment v extend g)
        (torusPlaquetteWalk (v.1+1,v.2)) = (if extend then g⁻¹ else 1) := by
  classical
  let u := torusTranslatedFluxAssignment v extend g
  have hH (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport u (torusGraph_adj_right x y) = 1 := by
    simp [u, regularDirectedTransport, torusTranslatedFluxAssignment,
      horizontal_ne_vertical x v.1 y v.2, horizontal_ne_vertical x (v.1+1) y v.2]
  have htwo : (2 : ZMod width) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [show (2 : ZMod width) = ((2 : ℕ) : ZMod width) by rfl,
      ZMod.val_natCast_of_lt (by have := Fact.out (p := 3 < width); omega),
      ZMod.val_zero] at hh
    omega
  have hx₂ : v.1+1+1 ≠ v.1 := by
    intro h
    have h' : v.1 + (2 : ZMod width) = v.1 + 0 := by
      simpa only [add_assoc, one_add_one_eq_two, add_zero] using h
    exact htwo (add_left_cancel h')
  have hx₂₁ : v.1+1+1 ≠ v.1+1 := by simp
  have hV : regularDirectedTransport u (torusGraph_adj_up (v.1+1+1) v.2) = 1 := by
    have h₀ : Edge.ofAdj (torusGraph_adj_up (v.1+1+1) v.2) ≠
        Edge.ofAdj (torusGraph_adj_up v.1 v.2) :=
      Edge.ofAdj_ne_of_endpoint_coordinates _ _ Prod.fst rfl (Or.inl hx₂)
    have h₁ : Edge.ofAdj (torusGraph_adj_up (v.1+1+1) v.2) ≠
        Edge.ofAdj (torusGraph_adj_up (v.1+1) v.2) :=
      Edge.ofAdj_ne_of_endpoint_coordinates _ _ Prod.fst rfl (Or.inl hx₂₁)
    simp [u, regularDirectedTransport, torusTranslatedFluxAssignment, h₀, h₁]
  obtain ⟨hL,hM⟩ := torusTranslatedFluxAssignment_up_transport v extend g
  change regularDirectedTransport u (torusGraph_adj_up v.1 v.2) = g at hL
  change regularDirectedTransport u (torusGraph_adj_up (v.1+1) v.2) =
    (if extend then g else 1) at hM
  constructor
  · rw [regularWalkHolonomy_torusPlaquetteWalk, hL, hH, hM, hH]
    cases extend <;> simp
  · rw [regularWalkHolonomy_torusPlaquetteWalk, hM, hH, hV, hH]
    cases extend <;> simp

variable [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev R (v : X) := translatedTwoPlaquetteRegion v
private abbrev T (v : X) := translatedTwoPlaquetteTree v
private abbrev RV (v : X) := {x : X // x ∈ R v}
/-- One six-spin unitary at any torus position extends the actual upward insertion
uniformly in its group element and every boundary column.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusTranslatedPhysicalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix (RV v → Fin d)
        (RV v → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV v → Fin d) ℂ ∧
      ∀ (g : G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusTranslatedFluxAssignment v false g))) (R v)
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusTranslatedFluxAssignment v true g))) (R v)
          (fun f => Fintype.equivFin G (θ f)) := by
  classical
  obtain ⟨W, hW, hact⟩ := exists_unitary_regularTwoCyclePhysicalFluxMove
    (R v) (T v)
    (torusIncidentSite (width := width) (height := height) a)
    (fun x => ha.isGIsometric_torusIncidentSite x)
    (translatedTwoPlaquetteTree_le v) (translatedTwoPlaquetteTree_isTree v)
    (translatedTwoPlaquetteVertexEquiv v 0)
    (translatedTwoPlaquetteCycleBond v 0) (translatedTwoPlaquetteCycleBond v 1)
    ((translatedTwoPlaquetteCycleBond_injective v).ne (by decide))
  refine ⟨W, hW, fun g θ => ?_⟩
  have h₀ := torusTranslatedFluxAssignment_eq_treeCycleAssignment v false g
  have h₁ := torusTranslatedFluxAssignment_eq_treeCycleAssignment v true g
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h₀ h₁
  rw [h₀, h₁]
  exact hact (translatedFluxInsertionElement v g) θ

/-- One six-spin unitary at any torus position, extended by the complementary
identity, moves the actual global torus insertion for every group element and
every common exterior and crossing assignment.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusTranslatedGlobalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix (RV v → Fin d)
        (RV v → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV v → Fin d) ℂ ∧
      regionLocalTerm (R v) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      ∀ (g : G) (u : Edge Γₜ → G),
        regionLocalTerm (R v) W *ᵥ stateCoeff
          (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R v)
              (torusTranslatedFluxAssignment v false g) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v)
            (torusTranslatedFluxAssignment v true g) u))) := by
  classical
  obtain ⟨W, hW, hglobal, hact⟩ := exists_unitary_regularTwoCycleGlobalFluxMove_bondOperators
    (R v) (T v)
    (torusIncidentSite (width := width) (height := height) a)
    (fun x => ha.isGIsometric_torusIncidentSite x)
    (translatedTwoPlaquetteTree_le v) (translatedTwoPlaquetteTree_isTree v)
    (translatedTwoPlaquetteVertexEquiv v 0)
    (translatedTwoPlaquetteCycleBond v 0) (translatedTwoPlaquetteCycleBond v 1)
    ((translatedTwoPlaquetteCycleBond_injective v).ne (by decide))
  refine ⟨W, hW, hglobal, fun g u => ?_⟩
  have h₀ := torusTranslatedFluxAssignment_eq_treeCycleAssignment v false g
  have h₁ := torusTranslatedFluxAssignment_eq_treeCycleAssignment v true g
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h₀ h₁
  rw [h₀, h₁]
  exact hact (translatedFluxInsertionElement v g) u
end TNLean.PEPS
