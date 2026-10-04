/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionReducedDensity
import TNLean.PEPS.RegularRegionInjectivity
import TNLean.PEPS.GInjectiveCutRange
import TNLean.PEPS.NormalPairBlocking

/-!
# Physical support recovers regular G-injective region spaces

For a cut of a regular G-injective PEPS with both induced regions connected,
the physical reduced density has exactly the regional ground space as its
range. The proof derives G-injectivity of the two actual open-region maps,
uses their common regular boundary labels, and recovers the first map's
range from the closed coefficient matrix.

Consequently equality of two closed regular G-injective PEPS vectors forces
equality of their regional ground spaces across every such cut. This is a
local necessary condition toward a G-injective Fundamental Theorem; no
factorization into virtual gauges is asserted.

**Scope restriction (regular virtual spaces):** The tensors use one finite
group's regular basis on every virtual bond. Both induced regions are
connected, and the cut has a crossing edge. The semi-regular case and more
general disconnected cuts are not included; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1,
Lemma 5.2, and the regular boundary cut in Theorem 6.9, local source lines
1278–1358 and 2043–2076. The statements below are consequences of those
constructions, rather than a formalization of a general G-injective
Fundamental Theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

omit [Group G] in
/-- Numbering the regular crossing labels preserves the actual regional
physical range. Source: SCP10, the regular-basis boundary cut, lines 2043–2076. -/
theorem range_regularOpenRegionMatrix_eq_regionGroundSpace
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (Matrix.mulVecLin (regularOpenRegionMatrix a R e)).range =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  have hmap : Matrix.mulVecLin (regularOpenRegionMatrix a R e) =
      Fintype.linearCombination ℂ (fun x => openRegionWeight (groupBondTensor a) R
        (regularRegionBoundaryConfigEquiv a R e x)) := by
    ext x σ
    simp [Matrix.mulVec, dotProduct, regularOpenRegionMatrix,
      Fintype.linearCombination_apply, mul_comm]
  rw [hmap, Fintype.range_linearCombination, regionGroundSpace_eq_span]
  congr 1
  change Set.range (openRegionWeight (groupBondTensor a) R ∘
    regularRegionBoundaryConfigEquiv a R e) = _
  rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

/-- A connected regular G-injective region has one invariant degree of
freedom per relative boundary label. This is the regular-basis dimension
calculation used in SCP10, Corollary 6.10, lines 2074–2090. -/
theorem finrank_regionGroundSpace_of_regular_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    Module.finrank ℂ (regionGroundSpace (groupBondTensor a) R) = Fintype.card G ^ n := by
  classical
  rw [← range_regularOpenRegionMatrix_eq_regionGroundSpace a R e]
  exact (isGInjective_regularOpenRegionMatrix_of_connected a ha R hR e).finrank_range.trans
    (finrank_regularBoundaryInvariants_succ n)

/-- Across a nonempty regular boundary, connected G-injective regions have
physical reduced density supported on their entire regional ground space.
This is an auxiliary consequence of SCP10, Lemma 5.2 and the boundary cut,
lines 1318–1358 and 2043–2076. -/
theorem range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (Matrix.mulVecLin (regionReducedDensity (groupBondTensor a) R)).range =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  let T := Matrix.mulVecLin (regularOpenRegionMatrix a R e)
  let S := Matrix.mulVecLin (regularOpenComplementMatrix a R e)
  have hT := isGInjective_regularOpenRegionMatrix_of_connected a ha R hR e
  have hS' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S := by
    dsimp only [S]
    rw [regularOpenComplementMatrix_eq_regularOpenRegionMatrix]
    exact isGInjective_regularOpenRegionMatrix_of_connected a ha _ hS _
  have hcut : regularBoundaryCutMatrix n T S = regularPhysicalCutMatrix a R := by
    rw [regularBoundaryCutMatrix]
    simp only [T, S, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    exact (regularPhysicalCutMatrix_eq_mul_transpose a R e).symm
  rw [range_regionReducedDensity_eq_cutRange]
  change (Matrix.mulVecLin (regularPhysicalCutMatrix a R)).range = _
  rw [← hcut, hT.range_regularBoundaryCutMatrix n hS']
  exact range_regularOpenRegionMatrix_eq_regionGroundSpace a R e

/-- The actual reduced density across a connected regular G-injective cut
has the invariant boundary rank. This is an auxiliary untwisted-cut
consequence of SCP10, Corollary 6.10, lines 2074–2090. -/
theorem rank_regionReducedDensity_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regionReducedDensity (groupBondTensor a) R).rank = Fintype.card G ^ n := by
  change Module.finrank ℂ (Matrix.mulVecLin
    (regionReducedDensity (groupBondTensor a) R)).range = _
  rw [range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected_cut a ha R hR hS n e]
  exact finrank_regionGroundSpace_of_regular_connected a ha R hR n e

/-- On a connected ambient graph, connected nonempty sides have a crossing
edge, and the closed physical reduced density recovers the regional ground
space. This is an auxiliary consequence of SCP10, Lemma 5.2 and the regular
cut, lines 1318–1358 and 2043–2076. -/
theorem range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (hΓ : Γ.Connected) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected) :
    (Matrix.mulVecLin (regionReducedDensity (groupBondTensor a) R)).range =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  obtain ⟨r⟩ := hR.nonempty
  obtain ⟨s⟩ := hS.nonempty
  have htop : R ≠ Finset.univ := by
    intro h
    simpa [h] using s.2
  let β := {f : Edge Γ // IsRegionBoundaryEdge R f}
  let : Nonempty β := nonempty_regionBoundaryEdge_of_connected hΓ ⟨r.1, r.2⟩ htop
  have hcard : 1 ≤ Fintype.card β := Fintype.card_pos
  let e : β ≃ Fin (Fintype.card β - 1 + 1) :=
    Fintype.equivFinOfCardEq (Nat.sub_add_cancel hcard).symm
  exact range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected_cut
    a ha R hR hS _ e

/-- Equality of two regular G-injective closed PEPS vectors forces equality
of their regional ground spaces across any connected cut of a connected
finite graph. This is a local necessary condition toward a G-injective
Fundamental Theorem, derived from SCP10, Definition 5.1 and Lemma 5.2,
lines 1278–1358. -/
theorem regionGroundSpace_eq_of_sameState_regular_connected
    (a b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (b v)))
    (hAB : SameState (groupBondTensor a) (groupBondTensor b))
    (hΓ : Γ.Connected) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected) :
    regionGroundSpace (groupBondTensor a) R = regionGroundSpace (groupBondTensor b) R := by
  have hρ := hAB.regionReducedDensity_eq R
  rw [← range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected a ha hΓ R hR hS,
    hρ, range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected b hb hΓ R hR hS]

/-- The genuine closed vector of a regular G-injective PEPS is nonzero
whenever both regions of a nonempty cut are connected. This follows from
the positive invariant boundary rank in SCP10, Corollary 6.10,
lines 2074–2090, for the untwisted closed contraction. -/
theorem stateCoeff_groupBondTensor_ne_zero_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    stateCoeff (groupBondTensor a) ≠ 0 := by
  intro hzero
  have hρzero : regionReducedDensity (groupBondTensor a) R = 0 := by
    ext σ θ
    simp [regionReducedDensity, Matrix.partialTraceRight_apply, hzero]
  have hrank := rank_regionReducedDensity_of_regular_connected_cut a ha R hR hS n e
  rw [hρzero, Matrix.rank_zero] at hrank
  exact (pow_ne_zero n Fintype.card_ne_zero) hrank.symm

/-- A connected cut with at least two crossing bonds determines the order
of a finite regular virtual group from the physical state. Thus two regular
G-injective descriptions with distinct virtual groups but the same closed
coefficient vector have groups of equal order. This is an auxiliary rigidity
consequence of SCP10, Corollary 6.10, lines 2074–2090. It does not identify
the groups or their multiplication laws. -/
theorem card_group_eq_of_sameState_regular_connected_cut
    {H : Type*} [Group H] [Fintype H]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → H) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (b v)))
    (hAB : SameState (groupBondTensor a) (groupBondTensor b))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (hboundary : 2 ≤ Fintype.card {f : Edge Γ // IsRegionBoundaryEdge R f}) :
    Fintype.card G = Fintype.card H := by
  classical
  let β := {f : Edge Γ // IsRegionBoundaryEdge R f}
  have hcard : 1 ≤ Fintype.card β := le_trans (by decide) hboundary
  let e : β ≃ Fin (Fintype.card β - 1 + 1) :=
    Fintype.equivFinOfCardEq (Nat.sub_add_cancel hcard).symm
  have hn : Fintype.card β - 1 ≠ 0 := by
    have hboundary' : 2 ≤ Fintype.card β := hboundary
    omega
  apply Nat.pow_left_injective hn
  calc
    Fintype.card G ^ (Fintype.card β - 1) =
        (regionReducedDensity (groupBondTensor a) R).rank :=
      (rank_regionReducedDensity_of_regular_connected_cut a ha R hR hS _ e).symm
    _ = (regionReducedDensity (groupBondTensor b) R).rank :=
      congrArg Matrix.rank (hAB.regionReducedDensity_eq R)
    _ = Fintype.card H ^ (Fintype.card β - 1) :=
      rank_regionReducedDensity_of_regular_connected_cut b hb R hR hS _ e

end TNLean.PEPS
