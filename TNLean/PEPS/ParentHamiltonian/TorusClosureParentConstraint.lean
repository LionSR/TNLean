/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusParentFlatness
import TNLean.PEPS.RegularGInjectiveTorus
import TNLean.PEPS.GInjectiveTorusSectorCount
import TNLean.PEPS.TorusRegionRealization

/-!
# Commuting closure labels and regular torus parent constraints

The parent constraint at the plaquette where the two native seams meet forces
commutativity of the two closure labels. Nonvanishing is derived from regular
G-injectivity, including for noncommuting closure pairs. Conversely, a commuting
closure satisfies every regional parent condition whose actual closed-cell
realization is simply connected: its integer lift removes all internal seam
operators, and crossing operators only relabel the boundary condition.

These statements prove the necessity of the commuting-pair condition and the
local sufficiency of the corresponding closure vectors. They do not establish
that these vectors span the entire torus parent kernel.

**Scope restriction (regular native closures):** Both periods are at least
three and the virtual representation is regular. The source restrictions are
recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
Source: SCP10, arXiv:1001.3807, Theorem 5.5 and its proof, lines 1440–1514,
and seam deformation, lines 1622–1647. No G-isometry is required.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local notation "R₀" => torusPlaquetteRegion ((-1, -1) : X)

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

omit [Fintype G] [DecidableEq G] in
private theorem directedTransport_of_head_eq {W : Type*} [LinearOrder W]
    {H : SimpleGraph W} (u : Edge H → G) {x y : W} (hxy : H.Adj x y)
    (hhead : (Edge.ofAdj hxy).1.2 = x) :
    regularDirectedTransport u hxy = (u (Edge.ofAdj hxy))⁻¹ := by
  have hyx : y < x := by
    rcases Edge.ofAdj_endpoints hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact (hxy.ne (hhead.symm.trans hh)).elim
    · simpa only [ht, hhead] using (Edge.ofAdj hxy).2.1
  simp only [regularDirectedTransport, ite_eq_right (not_lt.mpr hyx.le)]

omit [Fintype G] [DecidableEq G] in
private theorem closure_transport_right_wrap (g h : G) (v : X) (hv : v.1 + 1 = 0) :
    regularDirectedTransport (torusClosureEdgeAssignment g h)
      (torusGraph_adj_right v.1 v.2) = h := by
  rw [directedTransport_of_head_eq _ _ (torusRightEdge_head_of_wrap v hv)]
  change (torusClosureEdgeAssignment g h (torusRightEdge v))⁻¹ = h
  rw [torusClosureEdgeAssignment_right]
  simp only [torusHorizontalClosureElement, hv, ↓reduceIte, inv_inv]

omit [Fintype G] [DecidableEq G] in
private theorem closure_transport_up_wrap (g h : G) (v : X) (hv : v.2 + 1 = 0) :
    regularDirectedTransport (torusClosureEdgeAssignment g h)
      (torusGraph_adj_up v.1 v.2) = g⁻¹ := by
  rw [directedTransport_of_head_eq _ _ (torusUpEdge_head_of_wrap v hv)]
  change (torusClosureEdgeAssignment g h (torusUpEdge v))⁻¹ = g⁻¹
  rw [torusClosureEdgeAssignment_up]
  simp only [torusVerticalClosureElement, hv, ↓reduceIte]

/-- The original parent constraint at the seam-intersection plaquette forces
the native closure elements to commute. Nonzero closure vectors are derived
from regular G-injectivity. Source: SCP10, the final closure constraint in
the proof of Theorem 5.5, lines 1440–1514. -/
theorem IsGInjective.commute_of_cornerParent_annihilates_torusGClosure
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (g h : G)
    (Q : Matrix (RegionPhysicalConfig (d := d) (R₀))
      (RegionPhysicalConfig (d := d) (R₀)) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (R₀) Q)
    (hground : regionLocalTerm (R₀) Q *ᵥ
      torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h = 0) :
    Commute g h := by
  classical
  let u := torusClosureEdgeAssignment (width := width) (height := height) g h
  have hc : torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h =
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) :=
    funext (torusGClosure_eq_stateCoeff_twisted a g h)
  have hne : stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ≠ 0 := by
    rw [← hc]
    exact ha.torusGClosure_ne_zero g h
  rw [hc] at hground
  have hhol := ha.torusPlaquetteHolonomy_eq_one_of_parent_annihilates
    (-1, -1) u Q hQ hne hground
  have hs := (torusPlaquetteHolonomy_eq_one_iff_squareTransport u (-1, -1)).mp hhol
  dsimp only [u] at hs
  rw [closure_transport_up_wrap (width := width) (height := height)
      g h ((-1 : ZMod width) + 1, -1) (by simp),
    closure_transport_right_wrap (width := width) (height := height)
      g h (-1, -1) (by simp),
    closure_transport_right_wrap (width := width) (height := height)
      g h (-1, (-1 : ZMod height) + 1) (by simp),
    closure_transport_up_wrap (width := width) (height := height)
      g h (-1, -1) (by simp)] at hs
  exact Commute.inv_left_iff.mp hs

/-- A commuting closure satisfies the original parent condition on every
connected region with simply connected actual closed-cell realization.
Source: SCP10, Theorem 5.5 and seam deformation, lines 1440–1514 and
1622–1647; auxiliary regular local sufficiency, without G-isometry. -/
theorem IsGInjective.regionParent_annihilates_torusGClosure_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (g h : G) (hgh : Commute g h)
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) R Q) :
    regionLocalTerm R Q *ᵥ
      torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h = 0 := by
  classical
  obtain ⟨o⟩ := hR.nonempty
  obtain ⟨L, hL⟩ := exists_isTorusRegionIntegerLift_of_isSimplyConnected R hSC o
  have hspaces := regionGroundSpace_regularTwisted_eq_of_internalGaugeFlat
    (torusIncidentSite a)
    (fun z v η s => (ha.isGInjective_torusIncidentSite v).regularSiteMap_translation z η s)
    R (torusRegionLiftGauge R L g h) (torusClosureEdgeAssignment g h)
    (regularRegionGaugeResidual_torusRegionLiftGauge hL g h hgh)
  have hc : torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h =
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a)
        (torusClosureEdgeAssignment g h))) := funext (torusGClosure_eq_stateCoeff_twisted a g h)
  rw [hc]
  apply (regionLocalTerm_mulVec_eq_zero_iff (groupBondTensor (torusIncidentSite a)) R hQ _).mpr
  intro τ
  rw [← hspaces]
  exact stateCoeff_slice_mem_regionGroundSpace _ R τ


variable {ι : Type*} [Fintype ι]

/-- Every commuting regular closure is killed by a finite family of parents
on connected, simply connected regions. Source: SCP10, the inclusion
component of Theorem 5.5, lines 1440–1514; no spanning assertion is made. -/
theorem IsGInjective.regionParentHamiltonian_annihilates_torusGClosure
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : ι → Finset X) (hR : ∀ i, ((Γₜ).induce (R i : Set X)).Connected)
    (hSC : ∀ i, IsSimplyConnected (torusRegionRealization (R i)))
    (Q : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hQ : ∀ i, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) (R i) (Q i))
    (g h : G) (hgh : Commute g h) :
    regionParentHamiltonian R Q *ᵥ
      torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h = 0 := by
  apply (regionParentHamiltonian_mulVec_eq_zero_iff R Q (fun i => (hQ i).1) _).mpr
  intro i
  exact ha.regionParent_annihilates_torusGClosure_of_isSimplyConnected
    (R i) (hR i) (hSC i) g h hgh (Q i) (hQ i)

/-- The actual commuting closure span is contained in the parent kernel.
Source: SCP10, the inclusion component of Theorem 5.5, lines 1440–1514. -/
theorem IsGInjective.span_torusGClosure_commuting_le_parentKernel
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : ι → Finset X) (hR : ∀ i, ((Γₜ).induce (R i : Set X)).Connected)
    (hSC : ∀ i, IsSimplyConnected (torusRegionRealization (R i)))
    (Q : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hQ : ∀ i, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) (R i) (Q i)) :
    Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
      torusGClosure (width := width) (height := height) (leftRegularMatrix G) a p.1.1 p.1.2)) ≤
      (Matrix.mulVecLin (regionParentHamiltonian R Q)).ker := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨p, rfl⟩
  exact ha.regionParentHamiltonian_annihilates_torusGClosure R hR hSC Q hQ p.1.1 p.1.2 p.2

/-- The number of commuting pair-conjugacy classes is a lower bound for
the parent-kernel dimension. Source: SCP10, Theorems 5.5 and 5.9,
lines 1440–1514 and 1582–1621. Equality requires the missing converse
identification of the full kernel with the closure span. -/
theorem IsGInjective.card_commutingPairConjugacyClass_le_finrank_parentKernel
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : ι → Finset X) (hR : ∀ i, ((Γₜ).induce (R i : Set X)).Connected)
    (hSC : ∀ i, IsSimplyConnected (torusRegionRealization (R i)))
    (Q : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hQ : ∀ i, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) (R i) (Q i)) :
    Nat.card (CommutingPairConjugacyClass G) ≤
      Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian R Q)).ker := by
  classical
  have hr := range_torusGClosure_commuting_eq_range_torusGClosureClass
    (width := width) (height := height) (leftRegularMatrix G) a ha.invariant
  have hs : Submodule.span ℂ (Set.range (fun C : CommutingPairConjugacyClass G =>
      torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant C.1)) ≤
      (Matrix.mulVecLin (regionParentHamiltonian R Q)).ker := by
    rw [← hr]
    exact ha.span_torusGClosure_commuting_le_parentKernel R hR hSC Q hQ
  have hc := ha.finrank_span_torusGClosureClass_commuting_of_isSemiRegular
    (width := width) (height := height) (isSemiRegular_leftRegularMatrix (G := G))
  exact hc.symm.trans_le (Submodule.finrank_mono hs)

end TNLean.PEPS
