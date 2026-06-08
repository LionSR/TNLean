import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.NormalFundamentalTheorem

/-!
# Region realization toward the region insertion transfer

This file develops the region/complement decomposition of the closed state
coefficient, the foundation for the region analogue of the physical-to-virtual
recovery `physical_to_virtual_insertion` that supplies the data of a
`RegionInsertionTransfer` on a boundary edge of an arbitrary finite region `R`.

The closed state coefficient of an assembled physical configuration splits at the
region `R` into the region vertex product against the complement vertex product
(`prod_assembleRegionσ_split`). Inserting the identity on a boundary edge of `R`
contracts the blocked-region weight of `R` against that of its set complement; in
its double-global-configuration form (`regionInsertedCoeff_identity_eq_doubleSum`)
this is a sum over pairs of global virtual configurations agreeing on the boundary
of `R`. Merging such a pair into a single global configuration that reads the
region side from the first and the complement side from the second
(`regionMerge`, `regionProd_eq_merge`, `complementProd_eq_merge`) exhibits the
double sum as overcounting the closed state coefficient by the bond-dimension
product over the non-boundary edges (`regionInteriorBondProd`).

The identity insertion is now reduced to the equation
\[
  C_A(R,f,1;\sigma,\tau)
    = \Bigl(\prod_{e\notin\partial R}D_A(e)\Bigr)\,
      \langle \sigma,\tau \mid \Psi_A\rangle .
\]
Here \(D_A(e)\) is the bond dimension of the edge \(e\), and the product is over
the edges not crossing the boundary of `R`.
The remaining step toward the region insertion transfer is the corresponding
physical-to-virtual recovery for an arbitrary boundary-edge matrix insertion at
the in-region endpoint vertex, with this normalization kept visible; it is
recorded as remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Region/complement decomposition of the closed state coefficient

The closed state coefficient splits at an arbitrary region `R`, as a contraction
of the blocked-region weight on `R` against the blocked-region weight on the set
complement `univ \ R`, summed over the boundary configuration. Because the
blocked-region weight of `R` is a sum over *all* global virtual configurations
restricting to a given boundary configuration -- including free values on the
edges internal to the complement, which the region vertex product ignores -- the
contraction overcounts the closed state coefficient by the product of the bond
dimensions over the edges *not* crossing the boundary of `R`. This is the
region analogue of `stateCoeff_eq_vertexComplement`, where the single-vertex
star contraction has no such overcounting because its complement product reads
every edge. -/

/-- The global vertex product of the assembled physical configuration splits as
the region vertex product (reading `σ`) times the complement vertex product
(reading `τ`), at any fixed global virtual configuration. -/
theorem prod_assembleRegionσ_split (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (ζ : VirtualConfig A) :
    (∏ v : V, A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v)) =
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => ζ ie.1) (τ w) := by
  classical
  -- Read both region/complement subtype products through the assembled configuration.
  rw [show (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w.1) from
      Finset.prod_congr rfl (fun w _ => by rw [assembleRegionσ_mem]),
    show (∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => ζ ie.1) (τ w)) =
        ∏ w : {w : V // w ∈ Finset.univ \ R}, A.component w.1 (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w.1) from
      Finset.prod_congr rfl (fun w _ => by rw [assembleRegionσ_notMem])]
  -- Convert the two subtype products into the corresponding Finset products.
  rw [← Finset.prod_subtype R (fun x => Iff.rfl)
      (fun v => A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v)),
    ← Finset.prod_subtype (Finset.univ \ R) (fun x => Iff.rfl)
      (fun v => A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v))]
  -- Split the global product into `R` and its complement.
  rw [← Finset.compl_eq_univ_sdiff, Finset.prod_mul_prod_compl R
    (fun v => A.component v (fun ie => ζ ie.1)
      (assembleRegionσ (V := V) (d := d) R σ τ v))]

/-- The complement boundary label of a global virtual configuration equals
`regionComplementBoundaryConfig μ` exactly when its region boundary label equals
`μ`. Both record that the configuration agrees with `μ` on every boundary edge of
`R`, read through the boundary-edge identification of `R` with its complement. -/
theorem regionBoundaryLabel_compl_eq_iff (A : Tensor G d) (R : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R) (ξ : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
        regionComplementBoundaryConfig (G := G) A R μ ↔
      regionBoundaryLabel (G := G) A R ξ = μ := by
  constructor
  · intro h
    funext f
    have hh := congrFun h (regionBoundaryEdgeToCompl (G := G) R f)
    simpa [regionBoundaryLabel, regionComplementBoundaryConfig, regionBoundaryEdgeToCompl,
      regionBoundaryEdgeComplEquiv, Equiv.subtypeEquivRight] using hh
  · intro h
    funext f
    simp only [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
    have hh := congrFun h ((regionBoundaryEdgeComplEquiv (G := G) R).symm f)
    rw [regionBoundaryLabel_apply] at hh
    exact hh

/-! ### The boundary-agreement form of the identity region insertion

Summing the product of the blocked-region weight on `R` against the blocked-region
weight on `univ \ R` over the boundary configuration collapses the two boundary
filters into a single constraint: the two global virtual configurations agree on
every edge crossing the boundary of `R`. This is the double-global-sum form of
`regionInsertedCoeff_identity`, the starting point for the multiplicity collapse
to the closed state coefficient. -/

open scoped Classical in
/-- The identity-inserted region coefficient, in its double-global-configuration
form: a sum over pairs of global virtual configurations agreeing on the boundary
of `R`, of the region vertex product against the complement vertex product. -/
theorem regionInsertedCoeff_identity_eq_doubleSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
        (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
          ∏ w : {w : V // w ∈ Finset.univ \ R},
            A.component w.1 (fun ie => p.2 ie.1) (τ w) := by
  classical
  rw [regionInsertedCoeff_identity]
  -- Expand each blocked-region weight as a filtered sum over global configurations.
  simp only [regionBlockedWeight]
  -- Distribute the products of filtered sums and identify the combined filter.
  rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
        (∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
                regionComplementBoundaryConfig (G := G) A R μ),
            ∏ w : {w : V // w ∈ Finset.univ \ R},
              A.component w.1 (fun ie => ξ ie.1) (τ w)) =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = μ),
            (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w) from ?_]
  · -- Reindex the triple sum (μ, ζ, ξ) onto the boundary-agreement pair sum.
    simp only [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A R ζ)]
    · rw [if_pos rfl]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases heq : regionBoundaryLabel (G := G) A R ζ = regionBoundaryLabel (G := G) A R ξ
      · rw [if_pos heq.symm, if_pos heq]
      · rw [if_neg (fun h => heq h.symm), if_neg heq]
    · intro μ _ hμ
      rw [if_neg (fun h => hμ h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- The complement filter matches the region filter after the boundary-edge bridge,
    -- and the product of sums is the doubled sum.
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    refine Finset.sum_nbij' id id ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun ξ hξ => rfl)
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ).mp hξ
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ).mpr hξ

/-! ### Multiplicity collapse to the closed state coefficient

The boundary-agreement double sum overcounts the closed state coefficient by the
bond-dimension product over the edges not crossing the boundary of `R`. To see
this, merge the two configurations of an agreeing pair into one global
configuration that reads the region side from the first and the complement side
from the second: the region vertex product depends only on the merged
configuration through the region-incident edges, the complement vertex product
only through the complement-incident edges, and over each merged configuration
the agreeing pairs form a product of the free interior bonds. -/

/-- The bond-dimension product over the edges not crossing the boundary of `R`:
the overcounting multiplicity of the boundary-agreement double sum relative to the
closed state coefficient. -/
noncomputable def regionInteriorBondProd (A : Tensor G d) (R : Finset V) : ℕ :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e),
    A.bondDim e

open scoped Classical in
/-- Merge an agreeing pair of global virtual configurations into one global
configuration: the region-incident edges read the first configuration, the
remaining edges read the second. -/
noncomputable def regionMerge (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) : VirtualConfig A :=
  fun e => if IsRegionIncidentEdge (G := G) R e then p.1 e else p.2 e

omit [Fintype V] in
/-- The region vertex product reads the first configuration only through the
region-incident edges, so it agrees with the merged configuration. -/
theorem regionProd_eq_merge (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (p : VirtualConfig A × VirtualConfig A) :
    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ R},
        A.component w.1 (fun ie => regionMerge (G := G) A R p ie.1) (σ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  -- An edge incident to `w ∈ R` is region-incident, where merge reads `p.1`.
  have hinc : IsRegionIncidentEdge (G := G) R ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  rw [regionMerge, if_pos hinc]

/-- The complement vertex product reads the second configuration only through the
complement-incident edges, so it agrees with the merged configuration: on the
edges internal to the complement `merge` reads `p.2` by definition, and on the
boundary edges `p.1` and `p.2` agree. -/
theorem complementProd_eq_merge (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2) :
    (∏ w : {w : V // w ∈ Finset.univ \ R}, A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      ∏ w : {w : V // w ∈ Finset.univ \ R},
        A.component w.1 (fun ie => regionMerge (G := G) A R p ie.1) (τ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  have hw : w.1 ∉ R := by have := w.2; rw [Finset.mem_sdiff] at this; exact this.2
  by_cases hinc : IsRegionIncidentEdge (G := G) R ie.1
  · -- `ie` is region-incident but also complement-incident: it is a boundary edge,
    -- where `p.1` and `p.2` agree.
    have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
    have hbdry : IsRegionBoundaryEdge (G := G) R ie.1 := by
      rcases hinc with h1 | h2
      · -- `ie.1.1.1 ∈ R`; since one endpoint is `w ∉ R`, the edge crosses the boundary.
        rcases hwinc with hw1 | hw2
        · exact absurd (by rw [← hw1]; exact h1) hw
        · refine Or.inl ⟨h1, ?_⟩; rw [hw2]; exact hw
      · rcases hwinc with hw1 | hw2
        · refine Or.inr ⟨?_, h2⟩; rw [hw1]; exact hw
        · exact absurd (by rw [← hw2]; exact h2) hw
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨ie.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]

/-! ### The cardinality collapse to the closed state coefficient

Over each merged configuration `η` the agreeing pairs of an `η`-fiber are
parameterized by the free virtual indices on the edges not crossing the boundary
of `R`: an agreeing pair is determined on the boundary-crossing edges and on the
region-incident edges by `η`, leaving free the complement values on the
region-interior edges and the region values on the edges away from `R`. The
common count of these free indices is the bond-dimension product
`regionInteriorBondProd`, so the boundary-agreement double sum is that product
times the closed state coefficient. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge not incident to `R` does not cross the boundary of `R`: a
boundary-crossing edge touches `R`. -/
theorem not_boundary_of_not_incident (R : Finset V) {e : Edge G}
    (h : ¬ IsRegionIncidentEdge (G := G) R e) : ¬ IsRegionBoundaryEdge (G := G) R e :=
  fun hb => h (isRegionBoundaryEdge_touches (G := G) R hb)

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge crossing the boundary of `R` is incident to `R`. -/
theorem incident_of_boundary (R : Finset V) {e : Edge G}
    (h : IsRegionBoundaryEdge (G := G) R e) : IsRegionIncidentEdge (G := G) R e :=
  isRegionBoundaryEdge_touches (G := G) R h

/-- The free virtual indices of an agreeing pair: on a region-incident interior
edge the complement value, on an edge away from `R` the region value. These are
the indices left free once the merged configuration and the boundary agreement
are fixed. -/
def regionFiberLegs (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) :
    (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (A.bondDim e.1) :=
  fun e => if IsRegionIncidentEdge (G := G) R e.1 then p.2 e.1 else p.1 e.1

/-- Reconstruct an agreeing pair in the `η`-fiber from its free virtual indices:
the region-incident edges read `η`, the edges away from `R` read the free indices
in the first configuration, and the region-interior edges read them in the
second. -/
noncomputable def regionFiberPair (A : Tensor G d) (R : Finset V) (η : VirtualConfig A)
    (h : (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (A.bondDim e.1)) :
    VirtualConfig A × VirtualConfig A :=
  (fun e => if hinc : IsRegionIncidentEdge (G := G) R e then η e
              else h ⟨e, not_boundary_of_not_incident (G := G) R hinc⟩,
   fun e => if hb : IsRegionBoundaryEdge (G := G) R e then η e
              else if _hinc : IsRegionIncidentEdge (G := G) R e then h ⟨e, hb⟩
              else η e)

open scoped Classical in
/-- The `η`-fiber of the boundary-agreeing pairs under `regionMerge` has
cardinality `regionInteriorBondProd A R`: the free virtual indices on the
non-boundary edges biject with the fiber. -/
theorem regionFiber_card (A : Tensor G d) (R : Finset V) (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2)
          ∧ regionMerge (G := G) A R p = η)).card =
      regionInteriorBondProd (G := G) A R := by
  classical
  rw [show regionInteriorBondProd (G := G) A R =
      (Finset.univ : Finset ((e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e})
        → Fin (A.bondDim e.1))).card from ?_]
  · refine Finset.card_nbij'
      (regionFiberLegs (G := G) A R) (regionFiberPair (G := G) A R η) ?_ ?_ ?_ ?_
    · -- The free indices land in the full configuration set.
      intro p _; exact Finset.mem_univ _
    · -- The reconstruction lands in the `η`-fiber of agreeing pairs.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · -- The reconstructed pair agrees on every boundary edge.
        funext f
        simp only [regionBoundaryLabel_apply, regionFiberPair]
        rw [dif_pos (incident_of_boundary (G := G) R f.2), dif_pos f.2]
      · -- The reconstructed pair merges back to `η`.
        funext e
        simp only [regionMerge, regionFiberPair]
        by_cases hinc : IsRegionIncidentEdge (G := G) R e
        · rw [if_pos hinc, dif_pos hinc]
        · rw [if_neg hinc, dif_neg (not_boundary_of_not_incident (G := G) R hinc),
            dif_neg hinc]
    · -- Reconstructing from the free indices of a fiber pair recovers the pair.
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hagree, hmerge⟩ := hp
      have hagree' : ∀ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          p.1 f.1 = p.2 f.1 := fun f => congrFun hagree f
      have hmerge' : ∀ e : Edge G,
          (if IsRegionIncidentEdge (G := G) R e then p.1 e else p.2 e) = η e :=
        fun e => congrFun hmerge e
      refine Prod.ext ?_ ?_
      · -- First configuration.
        funext e
        simp only [regionFiberPair, regionFiberLegs]
        by_cases hinc : IsRegionIncidentEdge (G := G) R e
        · rw [dif_pos hinc]
          have := hmerge' e; rw [if_pos hinc] at this; exact this.symm
        · rw [dif_neg hinc, if_neg hinc]
      · -- Second configuration.
        funext e
        simp only [regionFiberPair, regionFiberLegs]
        by_cases hb : IsRegionBoundaryEdge (G := G) R e
        · rw [dif_pos hb]
          -- On a boundary edge the agreement and the merge identity force `p.2 e = η e`.
          have hinc := incident_of_boundary (G := G) R hb
          have h1 := hmerge' e; rw [if_pos hinc] at h1
          have h2 := hagree' ⟨e, hb⟩
          rw [← h1, h2]
        · rw [dif_neg hb]
          by_cases hinc : IsRegionIncidentEdge (G := G) R e
          · rw [dif_pos hinc, if_pos hinc]
          · rw [dif_neg hinc]
            have := hmerge' e; rw [if_neg hinc] at this; exact this.symm
    · -- Reading the free indices of a reconstruction recovers them.
      intro h _
      funext e
      simp only [regionFiberLegs, regionFiberPair]
      by_cases hinc : IsRegionIncidentEdge (G := G) R e.1
      · rw [if_pos hinc, dif_neg e.2, dif_pos hinc]
      · rw [if_neg hinc, dif_neg hinc]
  · -- The free-index configuration set has the bond-dimension product as its size.
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [regionInteriorBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e))
        (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e)]

open scoped Classical in
/-- The merged summand at a global virtual configuration `η`: the region vertex
product against the complement vertex product, both read from `η`. -/
noncomputable def regionMergedSummand (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (η : VirtualConfig A) : ℂ :=
  (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => η ie.1) (σ w)) *
    ∏ w : {w : V // w ∈ Finset.univ \ R}, A.component w.1 (fun ie => η ie.1) (τ w)

open scoped Classical in
/-- The sum of the merged summands over all global virtual configurations is the
closed state coefficient of the assembled physical configuration, by the
region/complement split of the global vertex product. -/
theorem sum_regionMergedSummand (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ η : VirtualConfig A, regionMergedSummand (G := G) A R σ τ η) =
      stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  unfold stateCoeff regionMergedSummand
  refine Finset.sum_congr rfl (fun η _ => ?_)
  exact (prod_assembleRegionσ_split (G := G) A R σ τ η).symm

open scoped Classical in
/-- **Cardinality collapse of the boundary-agreement double sum.** The
boundary-agreement double sum of the region vertex product against the complement
vertex product collapses to the bond-dimension product over the edges not
crossing the boundary of `R`, times the closed state coefficient of the assembled
physical configuration. This is the multiplicity collapse promised by the
double-global-sum form `regionInsertedCoeff_identity_eq_doubleSum`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem stateCoeff_eq_regionComplement (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  -- Read each agreeing summand through the merged configuration.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
        regionMergedSummand (G := G) A R σ τ (regionMerge (G := G) A R p) from ?_]
  · -- Group the agreeing pairs by their merged configuration.
    rw [← Finset.sum_fiberwise (Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2))
      (fun p => regionMerge (G := G) A R p)
      (fun p => regionMergedSummand (G := G) A R σ τ (regionMerge (G := G) A R p))]
    -- On each fiber the merged summand is constant, with the bond product as count.
    rw [← sum_regionMergedSummand (G := G) A R σ τ, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    rw [Finset.filter_filter,
      Finset.sum_congr rfl (g := fun _ => regionMergedSummand (G := G) A R σ τ η)
        (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
      Finset.sum_const, regionFiber_card (G := G) A R η]
  · -- Each agreeing summand is the merged summand at the merged configuration.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [regionMergedSummand, regionProd_eq_merge (G := G) A R σ p,
      complementProd_eq_merge (G := G) A R τ p hp.2]

open scoped Classical in
/-- **Identity insertion reads the closed state coefficient.** Inserting the
identity matrix on a boundary edge `f` of `R` equals the bond-dimension product
over the edges not crossing the boundary of `R`, times the closed state
coefficient of the assembled physical configuration. This combines the
double-global-sum form of the identity insertion with the cardinality collapse.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_one_eq_stateCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  rw [regionInsertedCoeff_identity_eq_doubleSum (G := G) A R f σ τ,
    stateCoeff_eq_regionComplement (G := G) A R σ τ]

end PEPS
end TNLean
