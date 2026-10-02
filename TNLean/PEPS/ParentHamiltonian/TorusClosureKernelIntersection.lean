/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionHolonomyFilter
import TNLean.PEPS.ParentHamiltonian.TorusClosureParentConstraint

/-!
# Parent constraints within the full regular torus closure span

A linear filter on the plaquette at the intersection of the two closure seams
fixes every commuting native closure and removes every noncommuting one. It
also fixes every vector satisfying the original parent condition on that
plaquette. Thus, within the span of all native pair-conjugacy-class closures,
a parent family containing the corner plaquette has precisely the commuting
closure span as its kernel. Arbitrary coherent sums are covered.

**Scope restriction (finite closure span):** Both periods are at least three,
the virtual representation is regular, and the remaining regional terms have
connected, simply connected actual closed-cell realizations. This result
identifies the intersection of the parent kernel with the full closure span;
it does not assume or prove that every parent-kernel vector belongs to that
span. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
Source: SCP10, arXiv:1001.3807, the final closure constraint in Theorem 5.5,
lines 1440–1514. No G-isometry is required.
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

variable {G : Type*} [Group G]

private theorem transport_from_ordered_head (u : Edge Γₜ → G) {x y : X}
    (hxy : (Γₜ).Adj x y) (hh : (Edge.ofAdj hxy).1.2 = x) :
    regularDirectedTransport u hxy = (u (Edge.ofAdj hxy))⁻¹ := by
  have hyx : y < x := by
    rcases Edge.ofAdj_endpoints hxy with ⟨ht, he⟩ | ⟨ht, he⟩
    · exact (hxy.ne (hh.symm.trans he)).elim
    · simpa only [ht, hh] using (Edge.ofAdj hxy).2.1
  simp only [regularDirectedTransport, ite_eq_right (not_lt.mpr hyx.le)]

/-- The seam-intersection plaquette has identity closure holonomy exactly
when the two native closure labels commute. Source: SCP10, the final
closure constraint in Theorem 5.5, lines 1440–1514. -/
theorem torusPlaquetteHolonomy_closure_corner_eq_one_iff_commute (g h : G) :
    regularWalkHolonomy (torusClosureEdgeAssignment g h)
      (torusPlaquetteWalk ((-1, -1) : X)) = 1 ↔ Commute g h := by
  have hr (v : X) (hv : v.1 + 1 = 0) :
      regularDirectedTransport (torusClosureEdgeAssignment g h)
        (torusGraph_adj_right v.1 v.2) = h := by
    rw [transport_from_ordered_head _ _ (torusRightEdge_head_of_wrap v hv)]
    change (torusClosureEdgeAssignment g h (torusRightEdge v))⁻¹ = h
    rw [torusClosureEdgeAssignment_right]
    simp only [torusHorizontalClosureElement, hv, ↓reduceIte, inv_inv]
  have hu (v : X) (hv : v.2 + 1 = 0) :
      regularDirectedTransport (torusClosureEdgeAssignment g h)
        (torusGraph_adj_up v.1 v.2) = g⁻¹ := by
    rw [transport_from_ordered_head _ _ (torusUpEdge_head_of_wrap v hv)]
    change (torusClosureEdgeAssignment g h (torusUpEdge v))⁻¹ = g⁻¹
    rw [torusClosureEdgeAssignment_up]
    simp only [torusVerticalClosureElement, hv, ↓reduceIte]
  rw [torusPlaquetteHolonomy_eq_one_iff_squareTransport,
    hu ((-1 : ZMod width) + 1, -1) (by simp), hr (-1, -1) (by simp),
    hr (-1, (-1 : ZMod height) + 1) (by simp), hu (-1, -1) (by simp)]
  exact Commute.inv_left_iff

variable [Fintype G] [DecidableEq G] {d : ℕ}

open Classical in
/-- A corner linear filter fixes all states satisfying the original corner
parent condition, fixes commuting closures, and kills noncommuting closures.
Source: SCP10, Theorem 5.5, lines 1440–1514; no G-isometry is assumed. -/
theorem IsGInjective.exists_torusClosureCommutationFilter
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ Q : Matrix (RegionPhysicalConfig (d := d) R₀) (RegionPhysicalConfig (d := d) R₀) ℂ,
      (∀ (P : Matrix (RegionPhysicalConfig (d := d) R₀)
          (RegionPhysicalConfig (d := d) R₀) ℂ) (Ψ : (X → Fin d) → ℂ),
        IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) R₀ P →
        regionLocalTerm R₀ P *ᵥ Ψ = 0 → regionLocalTerm R₀ Q *ᵥ Ψ = Ψ) ∧
      ∀ g h : G, regionLocalTerm R₀ Q *ᵥ
        torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h =
          if Commute g h then
            torusGClosure (width := width) (height := height)
              (leftRegularMatrix G) a g h else 0 := by
  classical
  let v : X := (-1, -1)
  have hs : ∀ x ∈ (torusPlaquetteWalk v).support, x ∈ (R₀ : Set X) := by
    intro x hx
    exact List.mem_toFinset.mpr hx
  have hR : ((Γₜ).induce (R₀ : Set X)).Connected := by
    have he : (R₀ : Set X) = {x | x ∈ (torusPlaquetteWalk v).support} := by
      ext x
      simp [v, torusPlaquetteRegion]
    rw [he]
    exact (torusPlaquetteWalk v).connected_induce_support
  let o : {x : X // x ∈ R₀} := ⟨v, hs _ (torusPlaquetteWalk v).start_mem_support⟩
  let p : ((Γₜ).induce (R₀ : Set X)).Walk o o :=
    (torusPlaquetteWalk v).induce (R₀ : Set X) hs
  obtain ⟨Q, hfix, heigen⟩ := exists_regularClosedWalkGlobalIdentityFilter
    (torusIncidentSite a) (fun w => ha.isGInjective_torusIncidentSite w) R₀ hR o p
  refine ⟨Q, hfix, ?_⟩
  intro g h
  have he := heigen (torusClosureEdgeAssignment g h)
  have hhol : regularWalkHolonomy (regularRegionInternalOperators R₀
      (torusClosureEdgeAssignment g h)) p =
      regularWalkHolonomy (torusClosureEdgeAssignment g h) (torusPlaquetteWalk v) := by
    dsimp only [p]
    rw [regularWalkHolonomy_inducedWalk, SimpleGraph.Walk.map_induce]
    rfl
  rw [hhol] at he
  have hc : torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h =
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a)
        (torusClosureEdgeAssignment g h))) := funext (torusGClosure_eq_stateCoeff_twisted a g h)
  rw [← hc] at he
  have hcomm : regularWalkHolonomy (torusClosureEdgeAssignment g h)
      (torusPlaquetteWalk v) = 1 ↔ Commute g h :=
    torusPlaquetteHolonomy_closure_corner_eq_one_iff_commute
      (width := width) (height := height) g h
  by_cases hgh : Commute g h
  · simpa only [ite_eq_left (hcomm.mpr hgh), ite_eq_left hgh] using he
  · simpa only [ite_eq_right (mt hcomm.mp hgh), ite_eq_right hgh] using he

variable {ι : Type*} [Fintype ι]

/-- Within the full pair-class closure span, the parent kernel is exactly
the commuting closure span. The regional family contains the corner
plaquette and all its actual closed-cell regions are connected and simply
connected. Source: SCP10, final closure constraints in Theorem 5.5,
lines 1440–1514; the separate global spanning step is not asserted. -/
theorem IsGInjective.inf_parentKernel_span_torusGClosureClass_eq_commutingSpan
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : ι → Finset X) (hR : ∀ i, ((Γₜ).induce (R i : Set X)).Connected)
    (hSC : ∀ i, IsSimplyConnected (torusRegionRealization (R i)))
    (Q : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hQ : ∀ i, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) (R i) (Q i))
    (i₀ : ι) (hi₀ : R i₀ = R₀) :
    (Matrix.mulVecLin (regionParentHamiltonian R Q)).ker ⊓
      Submodule.span ℂ (Set.range (torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant)) =
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height)
          (leftRegularMatrix G) a p.1.1 p.1.2)) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
    torusGClosure (width := width) (height := height) (leftRegularMatrix G) a p.1.1 p.1.2))
  obtain ⟨P, hfix, heigen⟩ := ha.exists_torusClosureCommutationFilter
    (width := width) (height := height)
  let E := Matrix.mulVecLin (regionLocalTerm R₀ P)
  have hmap : Submodule.span ℂ (Set.range (torusGClosureClass
      (width := width) (height := height) (leftRegularMatrix G) a ha.invariant)) ≤ S.comap E := by
    apply Submodule.span_le.mpr
    rintro Ψ ⟨C, rfl⟩
    refine Quotient.inductionOn C (fun p => ?_)
    change regionLocalTerm R₀ P *ᵥ torusGClosure
      (width := width) (height := height) (leftRegularMatrix G) a p.1 p.2 ∈ S
    rw [heigen]
    split_ifs with hp
    · exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
    · exact S.zero_mem
  apply le_antisymm
  · intro Ψ hΨ
    have hlocal := (regionParentHamiltonian_mulVec_eq_zero_iff R Q
      (fun i => (hQ i).1) Ψ).mp hΨ.1 i₀
    have hslices := (regionLocalTerm_mulVec_eq_zero_iff
      (groupBondTensor (torusIncidentSite a)) (R i₀) (hQ i₀) Ψ).mp hlocal
    rw [hi₀] at hslices
    have hcorner := (regionLocalTerm_mulVec_eq_zero_iff
      (groupBondTensor (torusIncidentSite a)) R₀
      (isRegionParentInteraction_canonical _ R₀) Ψ).mpr hslices
    have hfixed := hfix _ Ψ (isRegionParentInteraction_canonical _ R₀) hcorner
    have hmem := hmap hΨ.2
    change E Ψ ∈ S at hmem
    change regionLocalTerm R₀ P *ᵥ Ψ ∈ S at hmem
    rwa [hfixed] at hmem
  · refine le_inf (ha.span_torusGClosure_commuting_le_parentKernel R hR hSC Q hQ) ?_
    apply Submodule.span_le.mpr
    rintro Ψ ⟨p, rfl⟩
    exact Submodule.subset_span ⟨pairConjugacyClass G p.1, rfl⟩


/-- The parent kernel within the full native closure span has exactly the
commuting pair-class dimension. Source: SCP10, Theorems 5.5 and 5.9,
lines 1440–1514 and 1582–1621; finite closure-span statement. -/
theorem IsGInjective.finrank_parentKernel_inf_closureSpan
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : ι → Finset X) (hR : ∀ i, ((Γₜ).induce (R i : Set X)).Connected)
    (hSC : ∀ i, IsSimplyConnected (torusRegionRealization (R i)))
    (Q : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hQ : ∀ i, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) (R i) (Q i))
    (i₀ : ι) (hi₀ : R i₀ = R₀) :
    Module.finrank ℂ ↥((Matrix.mulVecLin (regionParentHamiltonian R Q)).ker ⊓
      Submodule.span ℂ (Set.range (torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant))) =
      Nat.card (CommutingPairConjugacyClass G) := by
  rw [ha.inf_parentKernel_span_torusGClosureClass_eq_commutingSpan R hR hSC Q hQ i₀ hi₀,
    range_torusGClosure_commuting_eq_range_torusGClosureClass _ _ ha.invariant]
  exact ha.finrank_span_torusGClosureClass_commuting_of_isSemiRegular
    (isSemiRegular_leftRegularMatrix (G := G))

end TNLean.PEPS
