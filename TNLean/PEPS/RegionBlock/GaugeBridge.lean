/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.GaugeBridgeExpansion

/-!
# General-matrix double-global-configuration form of the region-inserted coefficient

This file gives the general-matrix double-global-configuration form of the
region-inserted coefficient (`regionInsertedCoeff_eq_doubleSum`): inserting a matrix
`M` on a boundary edge `f` of a region `R` and contracting `R` against its set
complement equals a sum over pairs of global virtual configurations agreeing on every
boundary edge of `R` other than `f`, weighted by the matrix entry of `M` on the two
`f`-values.

This generalizes `regionInsertedCoeff_identity_eq_doubleSum`, the `M = 1` case where
the identity forces agreement on `f` too. It is the region-granularity analogue of
the open-bond expansion `edgeInsertedCoeff_eq_pairSum`, and the starting point for
porting the open-edge gauge cancellation `edgeInsertedCoeff_applyGauge` to the region
granularity: the two boundary configurations decouple only on `f`, where the gauge
on the open edge survives and conjugates the inserted matrix, while every other
boundary edge and every interior edge cancels pairwise.

The file proves the corresponding gauge-absorption equality.  The region weight of a gauged tensor
against the complement weight of an agreeing pair is one global gauge-vertex product over all
vertices (`regionComplProd_gauge_eq`), reading the first configuration on the region and the
second on the complement (`pairOuter`), with the physical legs assembled.  The region/complement
contraction is the single-bond cut at the boundary edge `f`, up to the non-boundary
bond-dimension multiplicity that is gauge-invariant; this is the region-to-edge identity
`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`, proved by the `pairOuter` fiber collapse
(`pairOuterFiber_card`, `sum_pairOuter_fiber_collapse`).  The edge gauge cancellation
`edgeInsertedCoeff_applyGauge` then transports across, giving the edgewise region
gauge-absorption equality `regionInsertedCoeff_applyGauge`: every interior edge and every boundary
edge other than `f` cancels its gauge pairwise, while the two endpoint gauges on `f` conjugate
the inserted matrix (transposed per the orientation convention of `edgeGaugeAt`, recorded by
`regionEdgeOrient`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--586 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The edgewise gauge-absorption equality

The region/complement contraction is the single-bond cut at the boundary edge `f`, up to the
non-boundary bond-dimension multiplicity, which is gauge-invariant.  Reading the outer reading
`pairOuter` of an agreeing pair at the in-region and complement endpoints of an edge
(`pairOuterReadFst`, `pairOuterReadSnd`), the agreeing pairs over a fixed consistent-off-`f`
configuration are parameterised by the free non-boundary legs (`pairOuterFiber_card`), so the
region-inserted coefficient is that multiplicity times the edge-inserted coefficient of the
assembled physical configuration (`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`).  The edge
gauge cancellation `edgeInsertedCoeff_applyGauge` then transports across, giving the region
gauge-absorption equality `regionInsertedCoeff_applyGauge`.  The map `regionEdgeOrient` records
the boundary-edge orientation forced by the edge convention of `edgeInsertedCoeff`. -/

/-- Read an outer config `ξ` at the in-region endpoint of an R-incident edge. -/
noncomputable def pairOuterReadFst (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B) (e : Edge G) : Fin (B.bondDim e) :=
  if _ : e.1.1 ∈ R then ξ e.1.1 (edgeLeftIncident (G := G) e)
  else ξ e.1.2 (edgeRightIncident (G := G) e)

/-- Read an outer config `ξ` at the complement endpoint of a complement-incident edge. -/
noncomputable def pairOuterReadSnd (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B) (e : Edge G) : Fin (B.bondDim e) :=
  if _ : e.1.1 ∈ R then ξ e.1.2 (edgeRightIncident (G := G) e)
  else ξ e.1.1 (edgeLeftIncident (G := G) e)

open scoped Classical in
/-- Rebuild a pair from an outer config and ghost legs on the non-boundary edges. -/
noncomputable def pairOuterFiberPair (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B)
    (h : (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (B.bondDim e.1)) :
    VirtualConfig B × VirtualConfig B :=
  (fun e => if hinc : IsRegionIncidentEdge (G := G) R e then pairOuterReadFst (G := G) B R ξ e
              else h ⟨e, not_boundary_of_not_incident (G := G) R hinc⟩,
   fun e => if hb : IsRegionBoundaryEdge (G := G) R e then pairOuterReadSnd (G := G) B R ξ e
              else if _ : IsRegionIncidentEdge (G := G) R e then h ⟨e, hb⟩
              else pairOuterReadSnd (G := G) B R ξ e)

omit [Fintype V] in
/-- Reading `ξ` at the in-region endpoint of an edge incident to a vertex `v ∈ R`, when `ξ`
is consistent off `f` and the edge is not `f`, gives `ξ v ie`. -/
theorem pairOuterReadFst_eq (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    {v : V} (hv : v ∈ R) (ie : IncidentEdge G v) :
    pairOuterReadFst (G := G) B R ξ ie.1 = ξ v ie := by
  obtain ⟨e, hinc⟩ := ie
  -- `v` is `e.1.1` or `e.1.2`.
  rcases hinc with hL | hR
  · subst hL
    exact dite_eq_left hv
  · subst hR
    by_cases h1 : e.1.1 ∈ R
    · -- both endpoints in R; e is not boundary; if e ≠ f, consistency gives equality.
      by_cases hef : e = f.1
      · -- e = f but both endpoints in R contradicts f being a boundary edge.
        exfalso
        have hb := f.2
        rw [← hef] at hb
        rcases hb with ⟨_, h2⟩ | ⟨h1', _⟩
        · exact h2 (by exact ‹e.1.2 ∈ R›)
        · exact h1' h1
      · exact (dite_eq_left h1).trans (hξ e hef)
    · exact dite_eq_right h1

omit [Fintype V] in
/-- Reading `ξ` at the complement endpoint of an edge incident to a vertex `v ∉ R`, when `ξ`
is consistent off `f` and the edge is not `f`, gives `ξ v ie`. -/
theorem pairOuterReadSnd_eq (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    {v : V} (hv : v ∉ R) (ie : IncidentEdge G v) :
    pairOuterReadSnd (G := G) B R ξ ie.1 = ξ v ie := by
  obtain ⟨e, hinc⟩ := ie
  rcases hinc with hL | hR
  · subst hL
    exact dite_eq_right hv
  · subst hR
    by_cases h1 : e.1.1 ∈ R
    · exact dite_eq_left h1
    · -- both endpoints not in R; e not boundary; if e ≠ f consistency gives equality.
      by_cases hef : e = f.1
      · exfalso
        have hb := f.2
        rw [← hef] at hb
        rcases hb with ⟨h1', _⟩ | ⟨_, h2⟩
        · exact h1 h1'
        · exact hv h2
      · exact (dite_eq_right h1).trans (hξ e hef)

omit [Fintype V] in
/-- The rebuilt pair's `pairOuter` recovers `ξ` (when `ξ` is consistent off `f`). -/
theorem pairOuter_pairOuterFiberPair (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    (h : (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (B.bondDim e.1)) :
    pairOuter (G := G) B R (pairOuterFiberPair (G := G) B R ξ h) = ξ := by
  classical
  funext v ie
  rw [pairOuter]
  by_cases hv : v ∈ R
  · rw [ite_eq_left hv]
    -- first component: edge ie.1 is R-incident (v ∈ R is an endpoint), reads pairOuterReadFst.
    have hinc : IsRegionIncidentEdge (G := G) R ie.1 := by
      rcases ie.2 with hie | hie
      · exact Or.inl (by rw [hie]; exact hv)
      · exact Or.inr (by rw [hie]; exact hv)
    simp only [pairOuterFiberPair, dite_eq_left hinc]
    exact pairOuterReadFst_eq (G := G) B R f ξ hξ hv ie
  · rw [ite_eq_right hv]
    -- second component.
    simp only [pairOuterFiberPair]
    by_cases hb : IsRegionBoundaryEdge (G := G) R ie.1
    · rw [dite_eq_left hb]
      exact pairOuterReadSnd_eq (G := G) B R f ξ hξ hv ie
    · by_cases hinc : IsRegionIncidentEdge (G := G) R ie.1
      · -- ie.1 R-incident but v ∉ R, so the other endpoint ∈ R, hence ie.1 is boundary: contra hb.
        exfalso
        apply hb
        -- v is an endpoint of ie.1 and v ∉ R; the other endpoint is in R by incidence.
        rcases ie.2 with hie | hie
        · -- v = ie.1.1.
          have hv1 : ie.1.1.1 ∉ R := by rw [hie]; exact hv
          rcases hinc with h1 | h2
          · exact absurd h1 hv1
          · exact Or.inr ⟨hv1, h2⟩
        · -- v = ie.1.1.2.
          have hv2 : ie.1.1.2 ∉ R := by rw [hie]; exact hv
          rcases hinc with h1 | h2
          · exact Or.inl ⟨h1, hv2⟩
          · exact absurd h2 hv2
      · rw [dite_eq_right hb, dite_eq_right hinc]
        exact pairOuterReadSnd_eq (G := G) B R f ξ hξ hv ie

open scoped Classical in
/-- The `ξ`-fiber of the agreeing-off-`f` pairs under `pairOuter` has cardinality
`regionInteriorBondProd B R`. -/
theorem pairOuterFiber_card (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ) :
    (Finset.univ.filter (fun p : VirtualConfig B × VirtualConfig B =>
        (∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1)
          ∧ pairOuter (G := G) B R p = ξ)).card =
      regionInteriorBondProd (G := G) B R := by
  classical
  rw [show regionInteriorBondProd (G := G) B R =
      (Finset.univ : Finset ((e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e})
        → Fin (B.bondDim e.1))).card from ?_]
  · refine Finset.card_nbij'
      (regionFiberLegs (G := G) B R) (pairOuterFiberPair (G := G) B R ξ) ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · -- The reconstruction lands in the `ξ`-fiber of agreeing-off-`f` pairs.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, pairOuter_pairOuterFiberPair (G := G) B R f ξ hξ h⟩
      -- agreement off `f` on boundary edges.
      intro c hc
      have hcb : IsRegionBoundaryEdge (G := G) R c.1 := c.2
      have hcinc : IsRegionIncidentEdge (G := G) R c.1 :=
        isRegionBoundaryEdge_touches (G := G) R hcb
      simp only [pairOuterFiberPair, dite_eq_left hcinc, dite_eq_left hcb]
      -- read-fst = read-snd on a boundary edge ≠ f, by consistency.
      have hcf : c.1 ≠ f.1 := fun h => hc (Subtype.ext h)
      by_cases h1 : c.1.1.1 ∈ R
      · have h2 : c.1.1.2 ∉ R := by
          rcases hcb with ⟨_, h2⟩ | ⟨h1', _⟩
          · exact h2
          · contradiction
        exact (pairOuterReadFst_eq B R f ξ hξ h1 (edgeLeftIncident c.1)).trans
          ((hξ c.1 hcf).trans
            (pairOuterReadSnd_eq B R f ξ hξ h2 (edgeRightIncident c.1)).symm)
      · have h2 : c.1.1.2 ∈ R := by
          rcases hcb with ⟨h1', _⟩ | ⟨_, h2⟩
          · contradiction
          · exact h2
        exact (pairOuterReadFst_eq B R f ξ hξ h2 (edgeRightIncident c.1)).trans
          ((hξ c.1 hcf).symm.trans
            (pairOuterReadSnd_eq B R f ξ hξ h1 (edgeLeftIncident c.1)).symm)
    · -- Reconstructing from the fiber legs of a fiber pair recovers the pair.
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hagree, hmerge⟩ := hp
      refine Prod.ext ?_ ?_
      · funext e
        simp only [pairOuterFiberPair, regionFiberLegs]
        by_cases hinc : IsRegionIncidentEdge (G := G) R e
        · rw [dite_eq_left hinc]
          -- pairOuterReadFst ξ e = p.1 e because pairOuter p = ξ and e is R-incident.
          subst hmerge
          by_cases h1 : e.1.1 ∈ R
          · exact (pairOuterReadFst_eq B R f (pairOuter B R p) hξ h1
              (edgeLeftIncident e)).trans (ite_eq_left h1)
          · -- e R-incident, e.1.1 ∉ R, so e.1.2 ∈ R.
            have h2 : e.1.2 ∈ R := by
              rcases hinc with h | h
              · exact absurd h h1
              · exact h
            exact (pairOuterReadFst_eq B R f (pairOuter B R p) hξ h2
              (edgeRightIncident e)).trans (ite_eq_left h2)
        · rw [dite_eq_right hinc, ite_eq_right hinc]
      · funext e
        simp only [pairOuterFiberPair, regionFiberLegs]
        by_cases hb : IsRegionBoundaryEdge (G := G) R e
        · rw [dite_eq_left hb]
          -- boundary edge: pairOuterReadSnd ξ e = p.2 e.
          subst hmerge
          rw [pairOuterReadSnd]
          by_cases h1 : e.1.1 ∈ R
          · -- e.1.1 ∈ R; boundary ⇒ e.1.2 ∉ R.
            have h2 : e.1.2 ∉ R := by
              rcases hb with ⟨_, hr⟩ | ⟨hl, _⟩
              · exact hr
              · exact absurd h1 hl
            exact (dite_eq_left h1).trans (ite_eq_right h2)
          · -- e.1.1 ∉ R; boundary ⇒ e.1.2 ∈ R, so the left endpoint is the complement side.
            exact (dite_eq_right h1).trans (ite_eq_right h1)
        · rw [dite_eq_right hb]
          by_cases hinc : IsRegionIncidentEdge (G := G) R e
          · rw [dite_eq_left hinc, ite_eq_left hinc]
          · rw [dite_eq_right hinc]
            -- e not incident: pairOuterReadSnd ξ e = p.2 e.
            subst hmerge
            rw [pairOuterReadSnd]
            have h1 : e.1.1 ∉ R := fun h => hinc (Or.inl h)
            exact (dite_eq_right h1).trans (ite_eq_right h1)
    · -- Reading the fiber legs of a reconstruction recovers them.
      intro h _
      funext e
      simp only [regionFiberLegs, pairOuterFiberPair]
      have hb : ¬ IsRegionBoundaryEdge (G := G) R e.1 := e.2
      by_cases hinc : IsRegionIncidentEdge (G := G) R e.1
      · -- R-incident non-boundary edge: legs read the second component, which is `h e`.
        rw [ite_eq_left hinc, dite_eq_right hb, dite_eq_left hinc]
      · -- non-incident edge: legs read the first component, which is `h e`.
        rw [ite_eq_right hinc, dite_eq_right hinc]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [regionInteriorBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e))
        (fun e => by simp [Finset.mem_filter]) (fun e => B.bondDim e)]

open scoped Classical in
/-- **The `pairOuter` fiber collapse.** Summing a function of `pairOuter p` over the agreeing-
off-`f` pairs equals the bond-dimension product over the non-boundary edges times the sum over
configurations consistent off `f`. Each fiber of `pairOuter` over a consistent-off-`f`
configuration has `regionInteriorBondProd B R` agreeing pairs (the free non-boundary legs);
no agreeing pair lies over an inconsistent-off-`f` configuration. -/
theorem sum_pairOuter_fiber_collapse (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (g : OpenLocalConfig (G := G) B → ℂ) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
      g (pairOuter (G := G) B R p)) =
      regionInteriorBondProd (G := G) B R •
        ∑ ξ ∈ Finset.univ.filter (fun ξ : OpenLocalConfig (G := G) B =>
            IsConsistentOff (G := G) B f.1 ξ),
          g ξ := by
  classical
  -- Group the agreeing pairs by their `pairOuter` value.
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p => pairOuter (G := G) B R p)
    (t := Finset.univ.filter (fun ξ : OpenLocalConfig (G := G) B =>
      IsConsistentOff (G := G) B f.1 ξ))
    (f := fun p => g (pairOuter (G := G) B R p))
    (s := Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1)) ?_]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    rw [Finset.mem_filter] at hξ
    -- On each fiber the summand is constant `g ξ`, with the bond product as count.
    rw [Finset.filter_filter,
      Finset.sum_congr rfl (g := fun _ => g ξ)
        (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
      Finset.sum_const]
    rw [show (Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          (∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
              p.1 c.1 = p.2 c.1)
            ∧ pairOuter (G := G) B R p = ξ)).card =
        regionInteriorBondProd (G := G) B R from
      pairOuterFiber_card (G := G) B R f ξ hξ.2]
  · -- Every agreeing pair's `pairOuter` is consistent off `f`.
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, pairOuter_isConsistentOff (G := G) B R f p hp.2⟩

/-- The orientation matrix sending the region-side/complement-side reading of a boundary edge
to its left/right reading: the identity when the left endpoint of `f` lies in `R`, the
transpose otherwise. -/
noncomputable def regionEdgeOrient (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then N else Nᵀ

open scoped Classical in
/-- **Region-to-edge identity.** The region-inserted coefficient on a boundary edge `f` of `R`
equals the bond-dimension product over the non-boundary edges times the edge-inserted
coefficient at `f` of the assembled physical configuration, with the inserted matrix oriented
by `regionEdgeOrient` (identity when `f`'s left endpoint lies in `R`, transpose otherwise).

The region/complement contraction overcounts the single-bond cut at `f` by the free non-boundary
legs (`sum_pairOuter_fiber_collapse`); the cut form is `edgeInsertedCoeff` read through
`edgeInsertedCoeff_eq_sum_local`, whose consistency deltas restrict to the configurations
consistent off `f`. -/
theorem regionInsertedCoeff_eq_smul_edgeInsertedCoeff (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) B R f N σ τ =
      regionInteriorBondProd (G := G) B R •
        edgeInsertedCoeff (G := G) B f.1 (assembleRegionσ (V := V) (d := d) R σ τ)
          (regionEdgeOrient (G := G) B R f N) := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum_vertex B R f N σ τ]
  -- Recognise the summand as `g (pairOuter p)` and collapse the fiber.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
      N (p.1 f.1) (p.2 f.1) *
        ∏ v : V, B.component v (pairOuter (G := G) B R p v)
          (assembleRegionσ (V := V) (d := d) R σ τ v)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
        (fun ξ : OpenLocalConfig (G := G) B =>
          N (pairOuterReadFst (G := G) B R ξ f.1) (pairOuterReadSnd (G := G) B R ξ f.1) *
            ∏ v : V, B.component v (ξ v)
              (assembleRegionσ (V := V) (d := d) R σ τ v)) (pairOuter (G := G) B R p) from ?_]
  · refine (sum_pairOuter_fiber_collapse B R f
      (fun ξ : OpenLocalConfig (G := G) B =>
        N (pairOuterReadFst (G := G) B R ξ f.1) (pairOuterReadSnd (G := G) B R ξ f.1) *
          ∏ v : V, B.component v (ξ v)
            (assembleRegionσ (V := V) (d := d) R σ τ v))).trans ?_
    congr 1
    set H : OpenLocalConfig (G := G) B → ℂ := fun ξ =>
      (regionEdgeOrient (G := G) B R f N)
          (ξ f.1.1.1 (edgeLeftIncident (G := G) f.1))
          (ξ f.1.1.2 (edgeRightIncident (G := G) f.1)) *
        ∏ v : V, B.component v (ξ v)
          (assembleRegionσ (V := V) (d := d) R σ τ v) with hH
    have hcollapse :
        edgeInsertedCoeff (G := G) B f.1
            (assembleRegionσ (V := V) (d := d) R σ τ)
            (regionEdgeOrient (G := G) B R f N) =
          ∑ ξ : {ξ : OpenLocalConfig (G := G) B //
            IsConsistentOff (G := G) B f.1 ξ}, H ξ.1 := by
      rw [edgeInsertedCoeff_eq_sum_local]
      calc
        _ = ∑ ξ : OpenLocalConfig (G := G) B,
              if IsConsistentOff (G := G) B f.1 ξ then H ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) B f.1 ξ <;> simp [h, hH]
        _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) B //
              IsConsistentOff (G := G) B f.1 ξ}, H ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (OpenLocalConfig (G := G) B)))
              (f := H) (p := IsConsistentOff (G := G) B f.1)]
            simp
    rw [hcollapse]
    have hHfilter :
        (∑ ξ ∈ Finset.univ.filter
            (fun ξ : OpenLocalConfig (G := G) B =>
              IsConsistentOff (G := G) B f.1 ξ), H ξ) =
          ∑ ξ : {ξ : OpenLocalConfig (G := G) B //
            IsConsistentOff (G := G) B f.1 ξ}, H ξ.1 := by
      rw [← Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (OpenLocalConfig (G := G) B)))
        (f := H) (p := IsConsistentOff (G := G) B f.1)]
      simp
    refine Eq.trans ?_ hHfilter
    refine Finset.sum_congr rfl (fun ξ hξmem => ?_)
    have hξ : IsConsistentOff (G := G) B f.1 ξ := (Finset.mem_filter.mp hξmem).2
    simp only [H]
    congr 1
    by_cases h1 : f.1.1.1 ∈ R
    · have h2 : f.1.1.2 ∉ R := by
        rcases f.2 with ⟨_, hr⟩ | ⟨hl, _⟩
        · exact hr
        · contradiction
      have hf := pairOuterReadFst_eq B R f ξ hξ h1 (edgeLeftIncident f.1)
      have hs := pairOuterReadSnd_eq B R f ξ hξ h2 (edgeRightIncident f.1)
      have hN := congrArg₂ N hf hs
      have horient : regionEdgeOrient (G := G) B R f N = N := ite_eq_left h1
      exact hN.trans (congrArg (fun M => M
        (ξ f.1.1.1 (edgeLeftIncident f.1))
        (ξ f.1.1.2 (edgeRightIncident f.1))) horient).symm
    · have h2 : f.1.1.2 ∈ R := by
        rcases f.2 with ⟨hl, _⟩ | ⟨_, hr⟩
        · contradiction
        · exact hr
      have hf := pairOuterReadFst_eq B R f ξ hξ h2 (edgeRightIncident f.1)
      have hs := pairOuterReadSnd_eq B R f ξ hξ h1 (edgeLeftIncident f.1)
      have hN := congrArg₂ N hf hs
      have horient : regionEdgeOrient (G := G) B R f N = Nᵀ := ite_eq_right h1
      exact hN.trans ((Matrix.transpose_apply N
        (ξ f.1.1.1 (edgeLeftIncident f.1))
        (ξ f.1.1.2 (edgeRightIncident f.1))).symm.trans
          (congrArg (fun M => M
            (ξ f.1.1.1 (edgeLeftIncident f.1))
            (ξ f.1.1.2 (edgeRightIncident f.1))) horient).symm)
  · -- The summand rewrite: `N (p.1 f)(p.2 f) = N (readFst (pairOuter p))(readSnd (pairOuter p))`.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hcons := pairOuter_isConsistentOff (G := G) B R f p hp.2
    simp only
    congr 2
    · -- `pairOuterReadFst (pairOuter p) f = p.1 f`.
      by_cases h1 : f.1.1.1 ∈ R
      · exact (ite_eq_left h1).symm.trans
          (pairOuterReadFst_eq B R f (pairOuter B R p) hcons h1
            (edgeLeftIncident f.1)).symm
      · -- f.1.1 ∉ R, boundary ⇒ f.1.2 ∈ R; readFst reads the right (in-region) endpoint = p.1 f.
        have h2 : f.1.1.2 ∈ R := by
          rcases f.2 with ⟨hl, _⟩ | ⟨_, hr⟩
          · exact absurd hl h1
          · exact hr
        exact (ite_eq_left h2).symm.trans
          (pairOuterReadFst_eq B R f (pairOuter B R p) hcons h2
            (edgeRightIncident f.1)).symm
    · -- `pairOuterReadSnd (pairOuter p) f = p.2 f`.
      by_cases h1 : f.1.1.1 ∈ R
      · -- f.1.1 ∈ R, boundary ⇒ f.1.2 ∉ R; readSnd reads the right (complement) endpoint = p.2 f.
        have h2 : f.1.1.2 ∉ R := by
          rcases f.2 with ⟨_, hr⟩ | ⟨hl, _⟩
          · exact hr
          · exact absurd h1 hl
        exact (ite_eq_right h2).symm.trans
          (pairOuterReadSnd_eq B R f (pairOuter B R p) hcons h2
            (edgeRightIncident f.1)).symm
      · exact (ite_eq_right h1).symm.trans
          (pairOuterReadSnd_eq B R f (pairOuter B R p) hcons h1
            (edgeLeftIncident f.1)).symm

/-- `regionEdgeOrient` does not depend on the tensor's components, only on the region and the
boundary edge. -/
theorem regionEdgeOrient_applyGauge (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    regionEdgeOrient (G := G) (applyGauge B Z) R f N = regionEdgeOrient (G := G) B R f N := rfl

omit [Fintype V] in
/-- `regionEdgeOrient` is an involution. -/
theorem regionEdgeOrient_regionEdgeOrient (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    regionEdgeOrient (G := G) B R f (regionEdgeOrient (G := G) B R f N) = N := by
  rw [regionEdgeOrient, regionEdgeOrient]
  by_cases h1 : f.1.1.1 ∈ R
  · simp only [ite_eq_left h1]
  · simp only [ite_eq_right h1, Matrix.transpose_transpose]

/-- **The edgewise region gauge-absorption equality.** Applying an oriented edge-gauge family `Z`
to a PEPS tensor and inserting `M` on a boundary edge `f` of `R` equals inserting, on the
ungauged tensor, the matrix obtained by orienting `M` to the edge convention, conjugating by the
open-edge gauge transpose, and orienting back: every interior edge and every boundary edge other
than `f` cancels its gauge pairwise, while the two endpoint gauges on `f` conjugate the inserted
matrix.

This is the region-granularity port of `edgeInsertedCoeff_applyGauge`.  The proof factors through
the region-to-edge identity `regionInsertedCoeff_eq_smul_edgeInsertedCoeff`: the region/complement
contraction is the single-bond cut at `f` (up to the non-boundary multiplicity, which is
gauge-invariant), so the edge-granularity cancellation applies and is transported back.  The
`regionEdgeOrient` records the boundary-edge orientation: the conjugation is by `(Z_f)ᵀ`
exactly as at the edge level when `f`'s left endpoint lies in `R`, and by the transpose-orientation
of that conjugation otherwise. -/
theorem regionInsertedCoeff_applyGauge (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) (applyGauge B Z) R f M σ τ =
      regionInsertedCoeff (G := G) B R f
        (regionEdgeOrient (G := G) B R f
          ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ *
            regionEdgeOrient (G := G) B R f M *
            ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)⁻¹)ᵀ)) σ τ := by
  classical
  -- Apply the region-to-edge identity on the gauged tensor.
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff (applyGauge B Z) R f M σ τ]
  rw [regionEdgeOrient_applyGauge B R Z f M]
  -- Cancel the gauge at the edge granularity.
  rw [edgeInsertedCoeff_applyGauge B Z f.1 (assembleRegionσ (V := V) (d := d) R σ τ)
    (regionEdgeOrient (G := G) B R f M)]
  -- Transport back through the region-to-edge identity on `B`.
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff B R f
    (regionEdgeOrient (G := G) B R f
      ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ *
        regionEdgeOrient (G := G) B R f M *
        ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)⁻¹)ᵀ)) σ τ]
  -- The bond-dimension multiplicities agree; the oriented matrix is an involution.
  rw [regionEdgeOrient_regionEdgeOrient B R f]
  -- `regionInteriorBondProd (applyGauge B Z) R = regionInteriorBondProd B R` definitionally.
  rfl

end PEPS
end TNLean
