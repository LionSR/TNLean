import TNLean.PEPS.TorusWindowChain3

/-!
# Transitivity of the corner extension across nested regions

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318) chains
consecutive-window comparisons across the staircase patch.  The open-boundary
chaining needs the transitivity of corner extension: for nested regions
`R ⊆ S ⊆ P`,

```
Ext_{S⊆P}(Ext_{R⊆S}(C)) = Ext_{R⊆P}(C).
```

Here `Ext` denotes the normalized corner extension of a region insert.  The
unnormalized extension `Extbar` satisfies the stronger bookkeeping identity

```
Extbar_{S⊆P}(Extbar_{R⊆S}(C))
  = IB(V \ S) • Extbar_{R⊆P}(C),
```

where `IB(T)` is the product of the interior bond dimensions over the region
`T`.  The normalized identity follows by cancelling this common multiplicity.

## Blue-coupling composition

Let `Φ_{R,S}` denote the blue coefficient for the nested three-block geometry
`R ⊆ S`, with blue block `S \ R` and exterior `V \ S`.  The bare composition is
equivalent to

```
Σ ν, Φ_{R,S}(β_R, σ_{S\R}, ν) Φ_{S,P}(ν, σ_{P\S}, β_P)
  = IB(V \ S) • Φ_{R,P}(β_R, σ_{P\R}, β_P).
```

This is the coefficient identity used when two consecutive corner extensions
are replaced by the direct extension over `R ⊆ P`.

## Merge collapse

The preceding blue-coupling law is proved by a two-sub-block merge collapse.
Pairs of virtual configurations that agree on the boundary of `V \ S` are
merged over `V \ S`.  Each merged configuration has exactly `IB(V \ S)`
preimages, and the products over the two blue blocks recombine because

```
P \ R = (S \ R) ⊔ (P \ S).
```

Thus the boundary-agreeing double sum collapses to `IB(V \ S)` times the
single sum over the merged configuration, which is the blue coefficient for
`R ⊆ P`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Host-label and product transfers through a region merge

The merge `regionMerge A T p` reads the `T`-incident edges from `p.1` and the rest from `p.2`.
A host label or a vertex product over a sub-block transfers to the merge when the sub-block's
boundary edges sit on the correct side of `T`. -/

omit [Fintype V] in
/-- A boundary edge of a region `H` with `H ⊆ T`, read off the merge `regionMerge A T p`, equals
the value of `p.1`: such an edge touches `H ⊆ T`, hence is `T`-incident, where the merge reads
`p.1`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the host-side boundary-edge reading);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionBoundaryLabel_regionMerge_of_subset_left {T H : Finset V} (hHT : H ⊆ T)
    (p : VirtualConfig A × VirtualConfig A) :
    regionBoundaryLabel (G := G) A H (regionMerge (G := G) A T p) =
      regionBoundaryLabel (G := G) A H p.1 := by
  funext f
  simp only [regionBoundaryLabel_apply]
  have hinc : IsRegionIncidentEdge (G := G) T f.1 := by
    rcases isRegionBoundaryEdge_touches (G := G) H f.2 with h1 | h2
    · exact Or.inl (hHT h1)
    · exact Or.inr (hHT h2)
  rw [regionMerge, if_pos hinc]

/-- A boundary edge of the host `univ \ K` with `K ⊆ univ \ T`, read off the merge
`regionMerge A T p`, equals the value of `p.2`, provided the pair agrees on the `T`-boundary.
Such an edge has its `K`-endpoint in `univ \ T` (so not in `T`); if `T`-incident, its other
endpoint is in `T`, making it a `T`-boundary edge where the agreement pins the value, and
otherwise the merge reads `p.2` directly.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the complement-side boundary-edge reading);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionBoundaryLabel_regionMerge_compl_of_subset {T K : Finset V}
    (hKT : K ⊆ Finset.univ \ T) (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ K) (regionMerge (G := G) A T p) =
      regionBoundaryLabel (G := G) A (Finset.univ \ K) p.2 := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : IsRegionIncidentEdge (G := G) T f.1
  · -- `f` is a boundary edge of `univ \ K` and `T`-incident: it is a `T`-boundary edge.
    have hbdry : IsRegionBoundaryEdge (G := G) T f.1 := by
      -- The endpoint of `f` lying in `K` is in `univ \ T`, so the `T`-incidence is via the
      -- other endpoint, giving a `T`-boundary edge.
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · -- `f.1.1 ∈ univ \ K`, `f.1.2 ∉ univ \ K`, i.e. `f.1.2 ∈ K`.
        have h2K : f.1.1.2 ∈ K := by
          by_contra hk; exact h2nothost (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)
        have h2notT : f.1.1.2 ∉ T := by
          have := hKT h2K; rw [Finset.mem_sdiff] at this; exact this.2
        rcases hinc with hc1 | hc2
        · exact Or.inl ⟨hc1, h2notT⟩
        · exact absurd hc2 h2notT
      · have h1K : f.1.1.1 ∈ K := by
          by_contra hk; exact h1nothost (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)
        have h1notT : f.1.1.1 ∉ T := by
          have := hKT h1K; rw [Finset.mem_sdiff] at this; exact this.2
        rcases hinc with hc1 | hc2
        · exact absurd hc1 h1notT
        · exact Or.inr ⟨h1notT, hc2⟩
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨f.1, hbdry⟩
    simpa [regionBoundaryLabel] using this
  · rw [regionMerge, if_neg hinc]

omit [Fintype V] in
/-- A vertex product over `B ⊆ T` reads `p.1` through the merge `regionMerge A T p`: edges
incident to `B ⊆ T` are `T`-incident, where the merge reads `p.1`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionProd_p1_eq_merge_of_subset {T B : Finset V} (hBT : B ⊆ T)
    (σ : RegionPhysicalConfig (V := V) (d := d) B) (p : VirtualConfig A × VirtualConfig A) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  have hinc : IsRegionIncidentEdge (G := G) T ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (hBT (by rw [hie]; exact w.2))
    · exact Or.inr (hBT (by rw [hie]; exact w.2))
  rw [regionMerge, if_pos hinc]

/-- A vertex product over `B ⊆ univ \ T` reads `p.2` through the merge `regionMerge A T p`, given
the pair agrees on the `T`-boundary: an edge incident to `B` either misses `T` (where the merge
reads `p.2`) or, being `T`-incident with an endpoint in `B ⊆ univ \ T`, is a `T`-boundary edge
where the agreement pins it.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionProd_p2_eq_merge_of_compl {T B : Finset V} (hBT : B ⊆ Finset.univ \ T)
    (σ : RegionPhysicalConfig (V := V) (d := d) B) (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.2 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  have hwnotT : w.1 ∉ T := by have := hBT w.2; rw [Finset.mem_sdiff] at this; exact this.2
  by_cases hinc : IsRegionIncidentEdge (G := G) T ie.1
  · -- `ie` is `T`-incident and touches `w ∉ T`: a boundary edge of `T`.
    have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
    have hbdry : IsRegionBoundaryEdge (G := G) T ie.1 := by
      rcases hinc with h1 | h2
      · rcases hwinc with hw1 | hw2
        · exact absurd (by rw [← hw1]; exact h1) hwnotT
        · refine Or.inl ⟨h1, ?_⟩; rw [hw2]; exact hwnotT
      · rcases hwinc with hw1 | hw2
        · refine Or.inr ⟨?_, h2⟩; rw [hw1]; exact hwnotT
        · exact absurd (by rw [← hw2]; exact h2) hwnotT
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨ie.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]

/-! ### The two-sub-block merge collapse -/

open scoped Classical in
/-- **The two-sub-block merge collapse.**  Over a region `T`, the boundary-agreeing double sum
of a product over `B₁ ⊆ univ \ T` (read from `p.2`) against a product over `B₂ ⊆ T` (read from
`p.1`), with the `p.2` side constrained on the host `univ \ K₁` (`K₁ ⊆ univ \ T`) and the `p.1`
side on a host `H₂ ⊆ T`, collapses to the `T`-interior bond multiple of the single sum over a
global configuration `η` constrained by both hosts, both products read from `η`.  Over each merge
fiber the agreeing pairs number the `T`-interior bond product (`regionFiber_card`); the host
constraints transfer to the merge through the boundary-edge embeddings.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the multiplicity collapse of the host-relative double
sum); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem mergeCollapse2 {T B₁ B₂ K₁ H₂ : Finset V}
    (hB₁ : B₁ ⊆ Finset.univ \ T) (hB₂ : B₂ ⊆ T)
    (hK₁ : K₁ ⊆ Finset.univ \ T) (hH₂ : H₂ ⊆ T)
    (c₁ : RegionBoundaryConfig (G := G) A (Finset.univ \ K₁))
    (c₂ : RegionBoundaryConfig (G := G) A H₂)
    (σ₁ : RegionPhysicalConfig (V := V) (d := d) B₁)
    (σ₂ : RegionPhysicalConfig (V := V) (d := d) B₂) :
    (∑ p ∈ Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A (Finset.univ \ K₁) p.2 = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ p.1 = c₂) ∧
          regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2),
      (∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => p.2 ie.1) (σ₁ w)) *
        ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => p.1 ie.1) (σ₂ w)) =
      regionInteriorBondProd (G := G) A T •
        ∑ η ∈ Finset.univ.filter (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
              regionBoundaryLabel (G := G) A H₂ η = c₂),
          (∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => η ie.1) (σ₁ w)) *
            ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => η ie.1) (σ₂ w) := by
  classical
  -- The merged summand at a global configuration `η`.
  set f : VirtualConfig A → ℂ := fun η =>
    (∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => η ie.1) (σ₁ w)) *
      ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => η ie.1) (σ₂ w) with hf
  -- Read each agreeing summand through the merged configuration.
  rw [show (∑ p ∈ Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A (Finset.univ \ K₁) p.2 = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ p.1 = c₂) ∧
          regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2),
      (∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => p.2 ie.1) (σ₁ w)) *
        ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => p.1 ie.1) (σ₂ w)) =
      ∑ p ∈ Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A (Finset.univ \ K₁) p.2 = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ p.1 = c₂) ∧
          regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2),
        f (regionMerge (G := G) A T p) from ?_]
  · -- Group the agreeing pairs by their merged configuration over all `η`.
    rw [← Finset.sum_fiberwise (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A (Finset.univ \ K₁) p.2 = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ p.1 = c₂) ∧
          regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2))
      (fun p => regionMerge (G := G) A T p)
      (fun p => f (regionMerge (G := G) A T p))]
    -- Compare the η-indexed sums on both sides.
    rw [show (regionInteriorBondProd (G := G) A T •
          ∑ η ∈ Finset.univ.filter (fun η : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
                regionBoundaryLabel (G := G) A H₂ η = c₂),
            f η) =
        ∑ η : VirtualConfig A,
          regionInteriorBondProd (G := G) A T •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
                regionBoundaryLabel (G := G) A H₂ η = c₂ then f η else 0) from ?_]
    · refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [Finset.filter_filter,
        Finset.sum_congr rfl (g := fun _ => f η)
          (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
        Finset.sum_const]
      -- The fiber count is the conditional `T`-interior bond product.
      rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            ((regionBoundaryLabel (G := G) A (Finset.univ \ K₁) p.2 = c₁ ∧
                  regionBoundaryLabel (G := G) A H₂ p.1 = c₂) ∧
                regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2) ∧
              regionMerge (G := G) A T p = η)) =
          (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2 ∧
              regionMerge (G := G) A T p = η)) ∩
            if regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
                regionBoundaryLabel (G := G) A H₂ η = c₂ then Finset.univ else ∅) from ?_]
      · by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ η = c₂
        · rw [if_pos hcompat, if_pos hcompat, Finset.inter_univ,
            regionFiber_card (G := G) A T η]
        · rw [if_neg hcompat, if_neg hcompat, Finset.inter_empty, Finset.card_empty,
            zero_smul, smul_zero]
      · by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
            regionBoundaryLabel (G := G) A H₂ η = c₂
        · rw [if_pos hcompat, Finset.inter_univ]
          refine Finset.filter_congr (fun p _ => ?_)
          constructor
          · rintro ⟨⟨_, hagree⟩, hmerge⟩; exact ⟨hagree, hmerge⟩
          · rintro ⟨hagree, hmerge⟩
            refine ⟨⟨⟨?_, ?_⟩, hagree⟩, hmerge⟩
            · rw [← regionBoundaryLabel_regionMerge_compl_of_subset hK₁ p hagree, hmerge]
              exact hcompat.1
            · rw [← regionBoundaryLabel_regionMerge_of_subset_left hH₂ p, hmerge]
              exact hcompat.2
        · rw [if_neg hcompat, Finset.inter_empty, Finset.filter_eq_empty_iff]
          rintro p _ ⟨⟨⟨hc₁, hc₂⟩, hagree⟩, hmerge⟩
          apply hcompat
          refine ⟨?_, ?_⟩
          · rw [← hmerge, regionBoundaryLabel_regionMerge_compl_of_subset hK₁ p hagree]; exact hc₁
          · rw [← hmerge, regionBoundaryLabel_regionMerge_of_subset_left hH₂ p]; exact hc₂
    · -- Distribute the multiplicity into the η-sum, discarding the unconstrained η.
      rw [Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
              regionBoundaryLabel (G := G) A H₂ η = c₂)]
      rw [show (∑ η ∈ Finset.univ.filter (fun η : VirtualConfig A =>
            ¬ (regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
              regionBoundaryLabel (G := G) A H₂ η = c₂)),
          regionInteriorBondProd (G := G) A T •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ K₁) η = c₁ ∧
                regionBoundaryLabel (G := G) A H₂ η = c₂ then f η else 0)) = 0 from ?_,
        add_zero]
      · refine Finset.sum_congr rfl (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_pos hη.2]
      · refine Finset.sum_eq_zero (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_neg hη.2, smul_zero]
  · -- Each agreeing summand is the merged summand at the merged configuration.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [hf, regionProd_p2_eq_merge_of_compl hB₁ σ₁ p hp.2.2,
      regionProd_p1_eq_merge_of_subset hB₂ σ₂ p]

/-! ### The product split over `P \ R = (S \ R) ⊔ (P \ S)` -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- For `R ⊆ S ⊆ P`, the vertex set `P \ R` is the disjoint union of `S \ R` and `P \ S`. -/
theorem sdiff_union_sdiff_of_subset {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P) :
    (S \ R) ∪ (P \ S) = P \ R := by
  ext w
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hwS, hwR⟩ | ⟨hwP, hwS⟩)
    · exact ⟨hSP hwS, hwR⟩
    · exact ⟨hwP, fun hwR => hwS (hRS hwR)⟩
  · rintro ⟨hwP, hwR⟩
    by_cases hwS : w ∈ S
    · exact Or.inl ⟨hwS, hwR⟩
    · exact Or.inr ⟨hwP, hwS⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- `S \ R` and `P \ S` are disjoint. -/
theorem sdiff_disjoint_sdiff {R S P : Finset V} : Disjoint (S \ R) (P \ S) := by
  rw [Finset.disjoint_left]
  rintro w hwSR hwPS
  exact (Finset.mem_sdiff.mp hwPS).2 (Finset.mem_sdiff.mp hwSR).1

omit [Fintype V] [DecidableRel G.Adj] in
/-- For `R ⊆ S ⊆ P`, `S \ R ⊆ P \ R`. -/
theorem sdiff_subset_sdiff_left {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P) :
    S \ R ⊆ P \ R := by
  rw [← sdiff_union_sdiff_of_subset hRS hSP]; exact Finset.subset_union_left

omit [Fintype V] [DecidableRel G.Adj] in
/-- For `R ⊆ S ⊆ P`, `P \ S ⊆ P \ R`. -/
theorem sdiff_subset_sdiff_right {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P) :
    P \ S ⊆ P \ R := by
  rw [← sdiff_union_sdiff_of_subset hRS hSP]; exact Finset.subset_union_right

omit [Fintype V] in
/-- A vertex product over a region `B` that is the disjoint union `B₁ ∪ B₂` splits as the product
over `B₁` against the product over `B₂`, each sub-block reading the physical leg `σ` restricted to
it.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex` (the vertex product over a region splits along a partition);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionProd_split {B B₁ B₂ : Finset V} (hdisj : Disjoint B₁ B₂)
    (hunion : B₁ ∪ B₂ = B) (ζ : VirtualConfig A)
    (σ : RegionPhysicalConfig (V := V) (d := d) B)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
      (∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => ζ ie.1) (σ ⟨w.1, h₁ w.2⟩)) *
        ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => ζ ie.1) (σ ⟨w.1, h₂ w.2⟩) := by
  classical
  -- Read every product through a single global physical function extending `σ`.
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hB : IsEmpty {w : V // w ∈ B} := ⟨fun w => hd.elim (σ w)⟩
    have hB₁ : IsEmpty {w : V // w ∈ B₁} := ⟨fun w => hd.elim (σ ⟨w.1, h₁ w.2⟩)⟩
    have hB₂ : IsEmpty {w : V // w ∈ B₂} := ⟨fun w => hd.elim (σ ⟨w.1, h₂ w.2⟩)⟩
    rw [Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, one_mul]
  · set gf : V → Fin d := fun w => if h : w ∈ B then σ ⟨w, h⟩ else Classical.arbitrary (Fin d)
      with hgf
    have hBval : (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
        ∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_); congr 1; rw [hgf]; simp only [dif_pos w.2]
    have hB₁val : (∏ w : {w : V // w ∈ B₁},
          A.component w.1 (fun ie => ζ ie.1) (σ ⟨w.1, h₁ w.2⟩)) =
        ∏ w : {w : V // w ∈ B₁}, A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_); congr 1; rw [hgf]; simp only [dif_pos (h₁ w.2)]
    have hB₂val : (∏ w : {w : V // w ∈ B₂},
          A.component w.1 (fun ie => ζ ie.1) (σ ⟨w.1, h₂ w.2⟩)) =
        ∏ w : {w : V // w ∈ B₂}, A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_); congr 1; rw [hgf]; simp only [dif_pos (h₂ w.2)]
    rw [hBval, hB₁val, hB₂val,
      ← Finset.prod_subtype B (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      ← Finset.prod_subtype B₁ (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      ← Finset.prod_subtype B₂ (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      ← hunion, Finset.prod_union hdisj]

/-! ### The blue-coupling composition law -/

open scoped Classical in
/-- **The blue-coupling composition law.**  For nested regions `R ⊆ S ⊆ P`, the composition over
the shared `univ \ S` rows of the blue couplings of `nested(R⊆S)` and `nested(S⊆P)` is the
`univ \ S` interior bond multiple of the single blue coupling of `nested(R⊆P)`.  The two host
labels and the two blue products pair across the shared `univ \ S` boundary as a two-sub-block
merge collapse over `univ \ S`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem threeBlockBlueCoeff_comp {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P)
    (bdryR : RegionBoundaryConfig (G := G) A (Finset.univ \ R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (P \ R))
    (bcP : RegionBoundaryConfig (G := G) A (Finset.univ \ P)) :
    (∑ ν' : RegionBoundaryConfig (G := G) A S,
      (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff bdryR
          (fun w => σ ⟨w.1, sdiff_subset_sdiff_left hRS hSP w.2⟩)
          (regionComplementBoundaryConfig (G := G) A S ν') *
        (nestedThreeBlockGeometry (V := V) hSP).threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := G) A S ν')
          (fun w => σ ⟨w.1, sdiff_subset_sdiff_right hRS hSP w.2⟩)
          bcP) =
      regionInteriorBondProd (G := G) A (Finset.univ \ S) •
        (nestedThreeBlockGeometry (V := V) (hRS.trans hSP)).threeBlockBlueCoeff bdryR σ bcP := by
  classical
  -- Abbreviations for the two blue physical legs, restrictions of `σ` to `S \ R` and `P \ S`.
  let σ₁ : RegionPhysicalConfig (V := V) (d := d) (S \ R) :=
    fun w => σ ⟨w.1, sdiff_subset_sdiff_left hRS hSP w.2⟩
  let σ₂ : RegionPhysicalConfig (V := V) (d := d) (P \ S) :=
    fun w => σ ⟨w.1, sdiff_subset_sdiff_right hRS hSP w.2⟩
  change (∑ ν' : RegionBoundaryConfig (G := G) A S,
      (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff bdryR σ₁
          (regionComplementBoundaryConfig (G := G) A S ν') *
        (nestedThreeBlockGeometry (V := V) hSP).threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := G) A S ν') σ₂ bcP) =
    regionInteriorBondProd (G := G) A (Finset.univ \ S) •
      (nestedThreeBlockGeometry (V := V) (hRS.trans hSP)).threeBlockBlueCoeff bdryR σ bcP
  -- Transform the RHS blue coupling into the split-product `mergeCollapse2` form.
  rw [show (nestedThreeBlockGeometry (V := V) (hRS.trans hSP)).threeBlockBlueCoeff bdryR σ bcP =
      ∑ η ∈ Finset.univ.filter (fun η : VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ R) η = bdryR ∧
            regionBoundaryLabel (G := G) A (Finset.univ \ P) η = bcP),
        (∏ w : {w : V // w ∈ S \ R}, A.component w.1 (fun ie => η ie.1) (σ₁ w)) *
          ∏ w : {w : V // w ∈ P \ S}, A.component w.1 (fun ie => η ie.1) (σ₂ w) from by
      rw [ThreeBlockGeometry.threeBlockBlueCoeff]
      refine Finset.sum_congr rfl (fun η _ => ?_)
      exact regionProd_split (A := A) sdiff_disjoint_sdiff
        (sdiff_union_sdiff_of_subset hRS hSP) η σ
        (sdiff_subset_sdiff_left hRS hSP) (sdiff_subset_sdiff_right hRS hSP)]
  -- Transform the LHS: unfold the two blue couplings and reindex the `ν'` sum.
  rw [show (∑ ν' : RegionBoundaryConfig (G := G) A S,
        (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff bdryR σ₁
            (regionComplementBoundaryConfig (G := G) A S ν') *
          (nestedThreeBlockGeometry (V := V) hSP).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A S ν') σ₂ bcP) =
      ∑ bc'' : RegionBoundaryConfig (G := G) A (Finset.univ \ S),
        (∑ q₁ ∈ Finset.univ.filter (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ R) q = bdryR ∧
              regionBoundaryLabel (G := G) A (Finset.univ \ S) q = bc''),
          ∏ w : {w : V // w ∈ S \ R}, A.component w.1 (fun ie => q₁ ie.1) (σ₁ w)) *
          ∑ q₂ ∈ Finset.univ.filter (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ S) q = bc'' ∧
              regionBoundaryLabel (G := G) A (Finset.univ \ P) q = bcP),
            ∏ w : {w : V // w ∈ P \ S}, A.component w.1 (fun ie => q₂ ie.1) (σ₂ w) from ?_]
  · -- Regroup the `bc''` double sum into the agreeing-pair sum, then merge-collapse.
    rw [← mergeCollapse2 (A := A) (T := Finset.univ \ S) (B₁ := S \ R) (B₂ := P \ S)
      (K₁ := R) (H₂ := Finset.univ \ P)
      (by intro w hw; rw [Finset.mem_sdiff] at hw; rw [Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨Finset.mem_univ _, fun h => h.2 hw.1⟩)
      (by intro w hw; rw [Finset.mem_sdiff] at hw; rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_univ _, hw.2⟩)
      (by intro w hw; rw [Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨Finset.mem_univ _, fun h => h.2 (hRS hw)⟩)
      (by intro w hw; rw [Finset.mem_sdiff] at hw; rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_univ _, fun h => hw.2 (hSP h)⟩)
      bdryR bcP σ₁ σ₂]
    · -- Match the `bc''` double sum to the agreeing-pair sum by fiberwise grouping.
      rw [← Finset.sum_fiberwise (Finset.univ.filter
          (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A (Finset.univ \ R) p.2 = bdryR ∧
                regionBoundaryLabel (G := G) A (Finset.univ \ P) p.1 = bcP) ∧
              regionBoundaryLabel (G := G) A (Finset.univ \ S) p.1 =
                regionBoundaryLabel (G := G) A (Finset.univ \ S) p.2))
        (fun p => regionBoundaryLabel (G := G) A (Finset.univ \ S) p.2)
        (fun p => (∏ w : {w : V // w ∈ S \ R},
            A.component w.1 (fun ie => p.2 ie.1) (σ₁ w)) *
          ∏ w : {w : V // w ∈ P \ S}, A.component w.1 (fun ie => p.1 ie.1) (σ₂ w))]
      refine Finset.sum_congr rfl (fun bc'' _ => ?_)
      rw [Finset.sum_mul_sum, Finset.filter_filter, ← Finset.sum_product']
      refine Finset.sum_equiv (Equiv.prodComm _ _) ?_ (fun _ _ => rfl)
      rintro ⟨q₁, q₂⟩
      constructor
      · -- A `(q₁, q₂)` index of the separated sum maps to an agreeing-pair fiber element.
        intro hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hq ⊢
        obtain ⟨⟨hR, hS₁⟩, hS₂, hP⟩ := hq
        exact ⟨⟨⟨hR, hP⟩, hS₂.trans hS₁.symm⟩, hS₁⟩
      · -- An agreeing-pair fiber element maps back to a `(q₁, q₂)` separated index.
        intro hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hq ⊢
        obtain ⟨⟨⟨hR, hP⟩, hagree⟩, hfib⟩ := hq
        exact ⟨⟨hR, hfib⟩, hagree.trans hfib, hP⟩
  · -- Reindex `ν'` by the complement boundary equivalence and unfold the couplings.
    rw [← Equiv.sum_comp (regionComplementBoundaryConfigEquiv (G := G) A S)
      (fun bc'' : RegionBoundaryConfig (G := G) A (Finset.univ \ S) =>
        (∑ q₁ ∈ Finset.univ.filter (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ R) q = bdryR ∧
              regionBoundaryLabel (G := G) A (Finset.univ \ S) q = bc''),
          ∏ w : {w : V // w ∈ S \ R}, A.component w.1 (fun ie => q₁ ie.1) (σ₁ w)) *
          ∑ q₂ ∈ Finset.univ.filter (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ S) q = bc'' ∧
              regionBoundaryLabel (G := G) A (Finset.univ \ P) q = bcP),
            ∏ w : {w : V // w ∈ P \ S}, A.component w.1 (fun ie => q₂ ie.1) (σ₂ w))]
    refine Finset.sum_congr rfl (fun ν' _ => ?_)
    rw [regionComplementBoundaryConfigEquiv_apply,
      ThreeBlockGeometry.threeBlockBlueCoeff, ThreeBlockGeometry.threeBlockBlueCoeff]
    rfl

/-! ### The bare and clean composition laws -/

open scoped Classical in
/-- **The bare composition law.**  For nested regions `R ⊆ S ⊆ P`, composing the bare corner
extensions over `R ⊆ S` and `S ⊆ P` equals the `univ \ S` interior bond multiple of the bare
corner extension over `R ⊆ P`.  The bare extension contracts the insert against the blue
coupling, so the law is the blue-coupling composition `threeBlockBlueCoeff_comp` carried through
the insert sum, with the `R`-physical leg aligned through the two restrictions.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem bareExtendInsert_trans {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P)
    (C : RegionInsert (G := G) (d := d) A R) :
    bareExtendInsert (G := G) hSP (bareExtendInsert (G := G) hRS C) =
      fun ν σ => regionInteriorBondProd (G := G) A (Finset.univ \ S) •
        bareExtendInsert (G := G) (hRS.trans hSP) C ν σ := by
  classical
  funext ν σ
  -- Expand both bare extensions; swap the `ν'`- and `μ`-sums and align the `R`-physical leg.
  simp only [bareExtendInsert, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [restrictSubRegionσ_restrictSubRegionσ hRS hSP]
  -- Pull the `C μ` factor through the `ν'`-sum.
  rw [show (∑ ν' : RegionBoundaryConfig (G := G) A S,
        C μ (restrictSubRegionσ (V := V) (d := d) (hRS.trans hSP) σ) *
          (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A R μ)
            (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset
              (restrictSubRegionσ (V := V) (d := d) hSP σ))
            (regionComplementBoundaryConfig (G := G) A S ν') *
          (nestedThreeBlockGeometry (V := V) hSP).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A S ν')
            (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset σ)
            (regionComplementBoundaryConfig (G := G) A P ν)) =
      C μ (restrictSubRegionσ (V := V) (d := d) (hRS.trans hSP) σ) *
        ∑ ν' : RegionBoundaryConfig (G := G) A S,
          (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A R μ)
            (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset
              (restrictSubRegionσ (V := V) (d := d) hSP σ))
            (regionComplementBoundaryConfig (G := G) A S ν') *
          (nestedThreeBlockGeometry (V := V) hSP).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A S ν')
            (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset σ)
            (regionComplementBoundaryConfig (G := G) A P ν) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun ν' _ => ?_); ring]
  rw [← mul_smul_comm]
  congr 1
  exact threeBlockBlueCoeff_comp (A := A) hRS hSP
    (regionComplementBoundaryConfig (G := G) A R μ)
    (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset σ)
    (regionComplementBoundaryConfig (G := G) A P ν)

/-- **The corner-extension transitivity.**  For nested regions `R ⊆ S ⊆ P` and positive bond
dimensions, extending an insert `C` over `R ⊆ S` and then over `S ⊆ P` agrees with extending it
directly over `R ⊆ P`.  The interior-bond multiplicity divisors of the clean corner extensions
cancel the `univ \ S` factor the bare composition law produces.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the chained extensions across the staircase patch);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem extendInsert_trans {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) (C : RegionInsert (G := G) (d := d) A R) :
    extendInsert (G := G) hSP (extendInsert (G := G) hRS C) =
      extendInsert (G := G) (hRS.trans hSP) C := by
  have hneS : (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) A (Finset.univ \ S) hpos).ne'
  -- Strip the outer and inner extensions to bare ones, pull the inner multiplicity through the
  -- outer bare extension, then apply the bare composition law and cancel the `univ \ S` factor.
  rw [extendInsert_eq_smul_bare hSP,
    show extendInsert (G := G) hRS C =
        fun ν σ => (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ)⁻¹ *
          bareExtendInsert (G := G) hRS C ν σ from extendInsert_eq_smul_bare hRS C,
    bareExtendInsert_const_smul hSP (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ)⁻¹
      (bareExtendInsert (G := G) hRS C),
    bareExtendInsert_trans hRS hSP, extendInsert_eq_smul_bare (hRS.trans hSP) C]
  funext ν σ
  simp only [nsmul_eq_mul]
  field_simp

end PEPS
end TNLean
