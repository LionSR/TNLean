/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularPhysicalChargeMotion
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Charge movement across an actual translated plaquette

The diagonal charge on the upper horizontal bond of a four-site square moves
to its lower horizontal bond by one unitary on the original four spins. Its
character, internal parameter and arbitrary actual boundary labels are retained.
All spanning-tree data is derived from the actual plaquette walk. No identity
of states, Gram matrices or coefficient factorizations is supplied.

Source: SCP10, arXiv:1001.3807, `eq:anyons:chargeon-move-setting`, lines 2489–2507.
**Scope restriction (finite simple tori):** Both periods are at least three.
The operation is a four-spin unitary; its factorization into two column
unitaries is not asserted. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance torusChargeMotionWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance torusChargeMotionHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The actual upper or lower horizontal bond of the four-site motion diagram.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
def torusPlaquetteChargeMotionBond (v : X) (upper : Bool) :
    {e : Edge Γₜ // e.1.1 ∈ torusPlaquetteRegion v ∧ e.1.2 ∈ torusPlaquetteRegion v} := by
  let y := if upper then v.2 + 1 else v.2
  let e := Edge.ofAdj (torusGraph_adj_right v.1 y)
  have hleft : (v.1,y) ∈ torusPlaquetteRegion v := by
    cases upper <;>
      simp [y, torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support]
  have hright : (v.1 + 1,y) ∈ torusPlaquetteRegion v := by
    cases upper <;>
      simp [y, torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support]
  refine ⟨e,?_⟩
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 y) with h | h
  · exact ⟨by simpa only [e,h.1] using hleft, by simpa only [e,h.2] using hright⟩
  · exact ⟨by simpa only [e,h.1] using hright, by simpa only [e,h.2] using hleft⟩

/-- The motion bonds are the native right edges, even when endpoint sorting
reverses a periodic seam. Source: SCP10, lines 2489–2507. -/
theorem torusPlaquetteChargeMotionBond_val (v : X) (upper : Bool) :
    (torusPlaquetteChargeMotionBond v upper).val =
      Edge.ofAdj (torusGraph_adj_right v.1 (if upper then v.2 + 1 else v.2)) := rfl

/-- The two bonds of the charge-motion square are genuinely distinct.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
theorem torusPlaquetteChargeMotionBond_ne (v : X) :
    torusPlaquetteChargeMotionBond v true ≠ torusPlaquetteChargeMotionBond v false := by
  intro h
  have he := congrArg Subtype.val h
  change Edge.ofAdj (torusGraph_adj_right v.1 (v.2 + 1)) =
    Edge.ofAdj (torusGraph_adj_right v.1 v.2) at he
  have hn : v.2 + 1 ≠ v.2 := by simp
  exact (Edge.ofAdj_ne_of_endpoint_coordinates
    (torusGraph_adj_right v.1 (v.2 + 1)) (torusGraph_adj_right v.1 v.2)
    Prod.snd rfl (Or.inl hn)) he

/-- A fixed original four-spin unitary moves the actual upper-bond charge to the
lower bond at every translated position, including both seams. It is chosen
before the character, parameter and arbitrary original boundary labels.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
theorem IsGIsometric.exists_unitary_torusPhysicalChargeMotion
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
        (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      W ∈ Matrix.unitaryGroup (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ ∧
      ∀ (χ : G → ℂ) (p : G)
        (θ : {b : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) b} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularEdgeCharacterSite
          (torusIncidentSite a) (torusPlaquetteChargeMotionBond v true).1 χ p))
          (torusPlaquetteRegion v) (fun b => Fintype.equivFin G (θ b)) =
        openRegionWeight (groupBondTensor (regularEdgeCharacterSite
          (torusIncidentSite a) (torusPlaquetteChargeMotionBond v false).1 χ p))
          (torusPlaquetteRegion v) (fun b => Fintype.equivFin G (θ b)) := by
  have hR : ((Γₜ).induce (torusPlaquetteRegion v : Set X)).Connected := by
    have hs : (torusPlaquetteRegion v : Set X) =
        {w | w ∈ (torusPlaquetteWalk v).support} := by
      ext w
      simp only [torusPlaquetteRegion, Finset.mem_coe, List.mem_toFinset, Set.mem_ofPred_eq]
    rw [hs]
    exact (torusPlaquetteWalk v).connected_induce_support
  exact exists_unitary_regularPhysicalChargeMotion_of_connected (torusPlaquetteRegion v)
    (torusIncidentSite a) (fun w => ha.isGIsometric_torusIncidentSite w) hR
    (torusPlaquetteChargeMotionBond v true) (torusPlaquetteChargeMotionBond v false)
end TNLean.PEPS
