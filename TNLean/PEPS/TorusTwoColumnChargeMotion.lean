/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoPartChargeMotion
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Charge movement by the two original column operations

The upper horizontal charge of an actual translated four-site square moves to
its lower bond by the product of independent two-spin unitaries on its columns.
The operations precede the character, internal parameter and every external
boundary configuration. Both local Gram forms and the joining formula are
derived from the original tensors, not supplied.

Source: SCP10, arXiv:1001.3807, `eq:anyons:chargeon-move-setting`, lines 2489–2507.
**Scope restriction (finite simple tori):** Both periods are at least three.
The actual two-column factorization includes either periodic seam; no claim
about other lattice geometries is made. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance torusColumnChargeMotionWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance torusColumnChargeMotionHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The left or right column consists of its two actual torus sites.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
def torusChargeMotionColumn (v : X) (right : Bool) : Finset X :=
  let x := if right then v.1 + 1 else v.1
  {(x,v.2),(x,v.2 + 1)}

omit [NeZero width] [NeZero height] [Fact (2 < width)] in
/-- Each column is a genuine two-spin region, including at a seam.
Source: SCP10, independent column blocking, lines 2489–2507. -/
theorem torusChargeMotionColumn_card (v : X) (right : Bool) :
    (torusChargeMotionColumn v right).card = 2 := by
  have hy : v.2 + 1 ≠ v.2 := by simp
  simp [torusChargeMotionColumn, Prod.mk.injEq, Ne.symm hy]

omit [NeZero width] [NeZero height] [Fact (2 < height)] in
/-- The two column regions are disjoint.
Source: SCP10, independent column blocking, lines 2489–2507. -/
theorem torusChargeMotionColumn_disjoint (v : X) :
    Disjoint (torusChargeMotionColumn v false) (torusChargeMotionColumn v true) := by
  have hx : v.1 + 1 ≠ v.1 := by simp
  apply Finset.disjoint_left.mpr
  intro w hwL hwR
  simp only [torusChargeMotionColumn, ite_true,
    Finset.mem_insert, Finset.mem_singleton] at hwL hwR
  rcases hwL with rfl | rfl <;> rcases hwR with h | h <;>
    exact hx (congrArg Prod.fst h).symm

/-- The union of the two columns is the original plaquette region.
Source: SCP10, the charge-motion square, lines 2489–2507. -/
theorem torusChargeMotionColumn_union (v : X) :
    torusChargeMotionColumn v false ∪ torusChargeMotionColumn v true =
      torusPlaquetteRegion v := by
  ext w
  simp only [torusChargeMotionColumn, ite_true,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, torusPlaquetteRegion,
    List.mem_toFinset, torusPlaquetteWalk, SimpleGraph.Walk.support,
    List.mem_cons, List.not_mem_nil]
  tauto

/-- The actual induced graph on either column is connected.
Source: SCP10, independent column blocking, lines 2489–2507. -/
theorem torusChargeMotionColumn_connected (v : X) (right : Bool) :
    ((Γₜ).induce (torusChargeMotionColumn v right : Set X)).Connected := by
  let x := if right then v.1 + 1 else v.1
  let p : X := (x,v.2)
  let q : X := (x,v.2 + 1)
  let w : (Γₜ).Walk p q := .cons (torusGraph_adj_up x v.2) .nil
  have hs : (torusChargeMotionColumn v right : Set X) = {z | z ∈ w.support} := by
    ext z
    simp only [torusChargeMotionColumn, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, Set.mem_ofPred_eq, w, SimpleGraph.Walk.support,
      List.mem_cons, List.not_mem_nil, or_false, x, p, q]
  rw [hs]
  exact w.connected_induce_support

/-- The upper or lower horizontal bond genuinely joins the two actual columns.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
def torusColumnChargeMotionBond (v : X) (upper : Bool) :
    RegionJoiningEdge (Γ := Γₜ) (torusChargeMotionColumn v false)
      (torusChargeMotionColumn v true) := by
  let y := if upper then v.2 + 1 else v.2
  have hL : (v.1,y) ∈ torusChargeMotionColumn v false := by
    cases upper <;> simp [torusChargeMotionColumn,y]
  have hR : (v.1 + 1,y) ∈ torusChargeMotionColumn v true := by
    cases upper <;> simp [torusChargeMotionColumn,y]
  exact regionJoiningEdge_ofAdj _ _ (torusChargeMotionColumn_disjoint v)
    (torusGraph_adj_right v.1 y) hL hR

/-- The actual joining bond is the native right edge in either ordering.
Source: SCP10, lines 2489–2507. -/
theorem torusColumnChargeMotionBond_val (v : X) (upper : Bool) :
    (torusColumnChargeMotionBond v upper).val =
      Edge.ofAdj (torusGraph_adj_right v.1 (if upper then v.2 + 1 else v.2)) := rfl

/-- Independent unitaries on the two original two-spin columns move the literal
charge insertion from the upper horizontal bond to the lower one, uniformly
before its character, parameter and every actual exterior boundary label.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
theorem IsGIsometric.exists_unitary_torusTwoColumnChargeMotion
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let L := torusChargeMotionColumn v false
    let S := torusChargeMotionColumn v true
    ∃ (Wₗ : Matrix (RegionPhysicalConfig (d := d) L) (RegionPhysicalConfig (d := d) L) ℂ)
      (Wᵣ : Matrix (RegionPhysicalConfig (d := d) S) (RegionPhysicalConfig (d := d) S) ℂ),
      Wₗ ∈ Matrix.unitaryGroup (RegionPhysicalConfig (d := d) L) ℂ ∧
      Wᵣ ∈ Matrix.unitaryGroup (RegionPhysicalConfig (d := d) S) ℂ ∧
      ∀ (χ : G → ℂ) (p : G)
        (θ : {b : Edge Γₜ // IsRegionBoundaryEdge (L ∪ S) b} → G),
        (Wₗ ⊗ₖ Wᵣ) *ᵥ (fun s => openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite (torusIncidentSite a)
            (torusColumnChargeMotionBond v true).1 χ p)) (L ∪ S)
          (fun b => Fintype.equivFin G (θ b))
          (Equiv.piFinsetUnion (fun _ : X => Fin d) (torusChargeMotionColumn_disjoint v) s)) =
        (fun s => openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite (torusIncidentSite a)
            (torusColumnChargeMotionBond v false).1 χ p)) (L ∪ S)
          (fun b => Fintype.equivFin G (θ b))
          (Equiv.piFinsetUnion (fun _ : X => Fin d) (torusChargeMotionColumn_disjoint v) s)) := by
  classical
  dsimp only
  obtain ⟨Wₗ,Wᵣ,hWₗ,hWᵣ,hact⟩ := exists_unitary_regularTwoPartChargeMotion
    (torusIncidentSite a) (fun w => ha.isGIsometric_torusIncidentSite w)
    (torusChargeMotionColumn v false) (torusChargeMotionColumn v true)
    (torusChargeMotionColumn_disjoint v) (torusChargeMotionColumn_connected v false)
    (torusChargeMotionColumn_connected v true)
    (torusColumnChargeMotionBond v true) (torusColumnChargeMotionBond v false)
  refine ⟨Wₗ,Wᵣ,hWₗ,hWᵣ,?_⟩
  intro χ p θ
  have heq (b : RegionJoiningEdge (Γ := Γₜ) (torusChargeMotionColumn v false)
      (torusChargeMotionColumn v true)) :
      (fun s => openRegionWeight (groupBondTensor
        (regularEdgeCharacterSite (torusIncidentSite a) b.1 χ p))
        (torusChargeMotionColumn v false ∪ torusChargeMotionColumn v true)
        (fun b => Fintype.equivFin G (θ b))
        (Equiv.piFinsetUnion (fun _ : X => Fin d) (torusChargeMotionColumn_disjoint v) s)) =
      (fun s => graphOpenRegionNetwork (regularEdgeCharacterSite (torusIncidentSite a) b.1 χ p)
        (torusChargeMotionColumn v false ∪ torusChargeMotionColumn v true) θ
        (Equiv.piFinsetUnion (fun _ : X => Fin d) (torusChargeMotionColumn_disjoint v) s)) := by
    funext s
    exact openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork _ _ _ _
  rw [heq,heq]
  exact hact χ p θ
end TNLean.PEPS
