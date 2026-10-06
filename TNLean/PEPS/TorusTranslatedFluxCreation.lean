/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTranslatedFluxMove
import TNLean.PEPS.RegularCyclePhysicalFluxCreation
import TNLean.PEPS.RegularCycleGlobalFluxCreation
/-!
# Creating an opposite flux pair at every torus position

The shared upward side of two adjacent plaquettes carries g, so the actual
counterclockwise holonomies are (g, g⁻¹). Its ordered coefficient is inverted
at the vertical seam. The translated six-site geometry derives this shared
bond as the middle chord of its spanning tree.

For each conjugacy class, one unitary on the six original spins creates the
normalized sum of actual conjugate insertions. It is chosen before every
boundary label. Its complementary identity extension has the same action on
actual global contractions for arbitrary common exterior and crossing operators.
The centralizer of g⁻¹ equals that of g, so the seam changes no normalization.

Source: SCP10, arXiv:1001.3807, Theorem 6.17,
`eq:anyons:make-chargeless-fluxon`, lines 2304–2340.

**Local fix (conjugacy-sum normalization):** The printed sum is multiplied by
(|G| |C_G(g)|)^(-1/2), as derived from its exact norm; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

**Scope restriction (finite-torus regular creation):** The horizontal period
is at least four and the vertical period at least three, and the virtual action
is regular. Every translated position, including both seams, is covered.
The statements concern actual contractions; the parent-Hamiltonian interpretation
and unrestricted geometry remain separate, as recorded in the same paper-gap note.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance translatedFluxCreationWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance translatedFluxCreationWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance translatedFluxCreationHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G]
private theorem shared_side_insertion (v : TorusVertex width height) (g : G) :
    torusPlaquetteSideInsertion v 1 g =
      torusPlaquetteSideInsertion (v.1+1,v.2) 3 g⁻¹ := by
  classical
  funext e
  change (if e = Edge.ofAdj (torusGraph_adj_up (v.1+1) v.2) then
    if (v.1+1,v.2) < (v.1+1,v.2+1) then g else g⁻¹ else 1) =
    (if e = Edge.ofAdj (torusGraph_adj_up (v.1+1) v.2).symm then
      if (v.1+1,v.2+1) < (v.1+1,v.2) then g⁻¹ else (g⁻¹)⁻¹ else 1)
  have hne : (v.1+1,v.2) ≠ (v.1+1,v.2+1) := by simp
  rcases lt_or_gt_of_ne hne with h | h
  · rw [Edge.ofAdj_of_lt _ h, Edge.ofAdj_of_gt _ h]
    simp [h, not_lt_of_gt h]
  · rw [Edge.ofAdj_of_gt _ h, Edge.ofAdj_of_lt _ h]
    simp [h, not_lt_of_gt h]

/-- A literal shared-bond insertion has opposite adjacent plaquette holonomies.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularWalkHolonomy_torusSharedPlaquetteInsertion
    (v : TorusVertex width height) (g : G) :
    regularWalkHolonomy (torusPlaquetteSideInsertion v 1 g) (torusPlaquetteWalk v) = g ∧
    regularWalkHolonomy (torusPlaquetteSideInsertion v 1 g)
      (torusPlaquetteWalk (v.1+1,v.2)) = g⁻¹ := by
  refine ⟨regularWalkHolonomy_torusPlaquetteSideInsertion v 1 g, ?_⟩
  rw [shared_side_insertion]
  exact regularWalkHolonomy_torusPlaquetteSideInsertion (v.1+1,v.2) 3 g⁻¹

/-- The ordered operator for an upward shared-bond transport, including the seam.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def torusSharedFluxOrderedElement (v : TorusVertex width height) (g : G) : G :=
  if (v.1+1,v.2) < (v.1+1,v.2+1) then g else g⁻¹
private abbrev R (v : TorusVertex width height) := translatedTwoPlaquetteRegion v
private abbrev T (v : TorusVertex width height) := translatedTwoPlaquetteTree v
private theorem treeCycleAssignment_single
    {V : Type*} [LinearOrder V] {Γ : SimpleGraph V} (S : Finset V)
    (F : SimpleGraph {v : V // v ∈ S}) [DecidableRel F.Adj]
    (e₁ : RegionCycleEdge (Γ := Γ) S F) (g : G) :
    regularTreeCycleAssignment S F (fun e => if e = e₁ then g else 1) =
      (fun e => if e = e₁.1.1 then g else 1) := by
  classical
  funext e
  by_cases h : e = e₁.1.1
  · subst e
    simp [regularTreeCycleAssignment, e₁.1.2.1, e₁.1.2.2, e₁.2]
  · simp only [regularTreeCycleAssignment]
    split_ifs <;> simp_all [Subtype.ext_iff]

/-- The actual directed insertion occupies the derived middle non-tree bond.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem torusSharedPlaquetteInsertion_eq_treeCycleAssignment
    (v : TorusVertex width height) (g : G) :
    torusPlaquetteSideInsertion v 1 g =
      regularTreeCycleAssignment (R v) (T v)
        (fun e => if e = translatedTwoPlaquetteCycleBond v 1
          then torusSharedFluxOrderedElement v g else 1) := by
  classical
  rw [treeCycleAssignment_single]
  funext e
  simp only [translatedTwoPlaquetteCycleBond_eq_up, Fin.val_one, Nat.cast_one]
  rfl

omit [Fact (3 < width)] [Fact (2 < height)] in
private theorem torusSharedFluxOrderedElement_conjugation
    (v : TorusVertex width height) (g z : G) :
    torusSharedFluxOrderedElement v (z*g*z⁻¹) = z * torusSharedFluxOrderedElement v g * z⁻¹ := by
  unfold torusSharedFluxOrderedElement
  split_ifs <;> simp [mul_inv_rev, mul_assoc]

private theorem centralizer_inv (g : G) :
    Subgroup.centralizer ({g⁻¹} : Set G) = Subgroup.centralizer ({g} : Set G) := by
  ext x
  simpa only [Subgroup.mem_centralizer_singleton_iff, ← commute_iff_eq] using
    (Commute.inv_right_iff (a := x) (b := g))

variable [Fintype G] [DecidableEq G] {d : ℕ}
/-- A six-spin unitary creates the normalized actual conjugacy sum at every position,
uniformly in the boundary columns. Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem IsGIsometric.exists_unitary_torusTranslatedPhysicalFluxCreation
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) (g : G) :
    ∃ W : Matrix ({x : TorusVertex width height // x ∈ R v} → Fin d)
        ({x : TorusVertex width height // x ∈ R v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({x : TorusVertex width height // x ∈ R v} → Fin d) ℂ ∧
      ∀ θ : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge (R v) e} → G,
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a) (fun _ => 1)))
          (R v) (fun f => Fintype.equivFin G (θ f)) =
        (Real.sqrt ((Fintype.card G : ℝ) *
          Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
          ∑ z : G, openRegionWeight (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (torusPlaquetteSideInsertion v 1 (z*g*z⁻¹))))
            (R v) (fun f => Fintype.equivFin G (θ f)) := by
  classical
  obtain ⟨W,hW,hact⟩ := exists_unitary_regularCyclePhysicalFluxCreation
    (R v) (T v) (torusIncidentSite (width := width) (height := height) a)
    (fun x => ha.isGIsometric_torusIncidentSite x)
    (translatedTwoPlaquetteTree_le v) (translatedTwoPlaquetteTree_isTree v)
    (translatedTwoPlaquetteVertexEquiv v 0) (translatedTwoPlaquetteCycleBond v 1)
    (torusSharedFluxOrderedElement v g)
  have hone : regularTreeCycleAssignment (Γ := torusGraph width height)
      (R v) (T v) (fun _ => (1 : G)) =
      (fun _ => 1) := by
    funext e
    simp [regularTreeCycleAssignment]
  have hc : Subgroup.centralizer ({torusSharedFluxOrderedElement v g} : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
    unfold torusSharedFluxOrderedElement
    split_ifs
    · rfl
    · exact centralizer_inv g
  refine ⟨W,hW,fun θ => ?_⟩
  have h := hact θ
  rw [hone,hc] at h
  have hi (z : G) : regularTreeCycleAssignment (R v) (T v)
      (fun f => if f = translatedTwoPlaquetteCycleBond v 1
        then z * torusSharedFluxOrderedElement v g * z⁻¹ else 1) =
      torusPlaquetteSideInsertion v 1 (z*g*z⁻¹) := by
    rw [torusSharedPlaquetteInsertion_eq_treeCycleAssignment,
      torusSharedFluxOrderedElement_conjugation]
  refine h.trans (congrArg (fun ψ =>
    (Real.sqrt ((Fintype.card G : ℝ) *
      Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ • ψ) ?_)
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun u => openRegionWeight (groupBondTensor
    (regularTwistedSite (torusIncidentSite (width := width) (height := height) a) u))
    (R v) (fun f => Fintype.equivFin G (θ f))) (hi z)

/-- The six-spin identity extension creates the actual global conjugacy sum,
uniformly in common exterior operators. Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem IsGIsometric.exists_unitary_torusTranslatedGlobalFluxCreation
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) (g : G) :
    ∃ W : Matrix ({x : TorusVertex width height // x ∈ R v} → Fin d)
        ({x : TorusVertex width height // x ∈ R v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({x : TorusVertex width height // x ∈ R v} → Fin d) ℂ ∧
      regionLocalTerm (R v) W ∈ Matrix.unitaryGroup
        (TorusVertex width height → Fin d) ℂ ∧
      ∀ u : Edge (torusGraph width height) → G,
        regionLocalTerm (R v) W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v) (fun _ => 1) u))) =
        (Real.sqrt ((Fintype.card G : ℝ) *
          Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
          ∑ z : G, stateCoeff (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R v)
              (torusPlaquetteSideInsertion v 1 (z*g*z⁻¹)) u))) := by
  classical
  obtain ⟨W,hW,hglobal,hact⟩ := exists_unitary_regularCycleGlobalFluxCreation_bondOperators
    (R v) (T v) (torusIncidentSite (width := width) (height := height) a)
    (fun x => ha.isGIsometric_torusIncidentSite x)
    (translatedTwoPlaquetteTree_le v) (translatedTwoPlaquetteTree_isTree v)
    (translatedTwoPlaquetteVertexEquiv v 0) (translatedTwoPlaquetteCycleBond v 1)
    (torusSharedFluxOrderedElement v g)
  have hone : regularTreeCycleAssignment (Γ := torusGraph width height)
      (R v) (T v) (fun _ => (1 : G)) =
      (fun _ => 1) := by
    funext e
    simp [regularTreeCycleAssignment]
  have hc : Subgroup.centralizer ({torusSharedFluxOrderedElement v g} : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
    unfold torusSharedFluxOrderedElement
    split_ifs
    · rfl
    · exact centralizer_inv g
  refine ⟨W,hW,hglobal,fun u => ?_⟩
  have h := hact u
  rw [hone,hc] at h
  have hi (z : G) : regularTreeCycleAssignment (R v) (T v)
      (fun f => if f = translatedTwoPlaquetteCycleBond v 1
        then z * torusSharedFluxOrderedElement v g * z⁻¹ else 1) =
      torusPlaquetteSideInsertion v 1 (z*g*z⁻¹) := by
    rw [torusSharedPlaquetteInsertion_eq_treeCycleAssignment,
      torusSharedFluxOrderedElement_conjugation]
  refine h.trans (congrArg (fun ψ =>
    (Real.sqrt ((Fintype.card G : ℝ) *
      Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ • ψ) ?_)
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun w => stateCoeff (groupBondTensor
    (regularTwistedSite (torusIncidentSite (width := width) (height := height) a)
      (regularRegionBondExtension (R v) w u)))) (hi z)

end TNLean.PEPS
