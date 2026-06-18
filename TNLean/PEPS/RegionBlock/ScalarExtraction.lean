import TNLean.PEPS.RegionBlock.InsertResidual

/-!
# The inserted-site scalar extraction for the normal PEPS Fundamental Theorem

This file performs the scalar-extraction step of the normal PEPS Fundamental
Theorem's final comparison (arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1544--1571 of `Papers/1804.04964/paper_normal.tex`).

Throughout, `B'` abbreviates the gauged tensor, which the source writes with a
tilde over `B`.

The region comparison `regionComplement_comparison` delivers, at a region `R` and
at the one-site-larger region `insert v R`, the two scalar proportionalities
`A_R = c_R · B'_R` and `A_S = c_S · B'_S` of the blocked weights.  Feeding both
through the landed inserted-site factorization
`insertOuterBondProd_smul_regionBlockedWeight_insert` cancels the bond-only
inserted-site multiplicity and leaves, at every inserted-site local configuration
`η`, the inserted-site tensor of `A` against the bridge-label blocked weight of `R`
matched with `c_S` against the inserted-site tensor of `B'` against the same
bridge-label weight, scaled by `c_R` after substituting the `R`-proportionality.

The bridge labels of the *consistent* local configurations `η` at `v` are in
bijection with `η` itself: a consistent `η` is determined by the bridge label on
the `v`-incident edges that bound `R` and by `μ` on the `v`-incident edges that do
not.  Linear independence of `B'`'s `R`-blocked family therefore separates the
`η`-coefficients to a single term each, yielding the per-vertex relation
`A.component v η = (c_S / c_R) · B'.component v η` at every local configuration `η`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1544--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Consistent local configurations are determined by their bridge label

A local configuration `η` at the inserted site `v` is read by the bridge label
`boundaryLabelOfInsert μ η` on exactly the `v`-incident edges that bound `R`; the
remaining `v`-incident edges run from `v` to a vertex outside `insert v R`, where
inserted-site consistency pins `η` to `μ`.  Hence a consistent `η` is determined by
`μ` together with its bridge label, and two consistent local configurations with
the same bridge label coincide. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `v`-incident edge bounds `R` exactly when it is incident to `R`: its `R`-side
endpoint lies in `R` and its `v` endpoint does not. -/
theorem isRegionBoundaryEdge_of_vIncident_regionIncident (R : Finset V) {v : V}
    (hv : v ∉ R) {e : Edge G} (hev : e.1.1 = v ∨ e.1.2 = v)
    (hinc : IsRegionIncidentEdge (G := G) R e) :
    IsRegionBoundaryEdge (G := G) R e := by
  rcases hev with he | he
  · -- `e.1.1 = v ∉ R`; incidence forces the other endpoint into `R`.
    have h1 : e.1.1 ∉ R := by rw [he]; exact hv
    rcases hinc with h | h
    · exact absurd h h1
    · exact Or.inr ⟨h1, h⟩
  · have h2 : e.1.2 ∉ R := by rw [he]; exact hv
    rcases hinc with h | h
    · exact Or.inl ⟨h, h2⟩
    · exact absurd h h2

omit [Fintype V] in
/-- **Inserted-site consistency pins a local configuration to its bridge label.**

Under inserted-site consistency, the local configuration `η` at `v` is determined
by `μ` and the bridge label `boundaryLabelOfInsert μ η`: on a `v`-incident edge that
bounds `R` it is read from the bridge label, and on a `v`-incident edge that does not
bound `R` (so runs to a vertex outside `insert v R`) consistency reads it from `μ`. -/
theorem localConfig_eq_of_insertConsistent (A : Tensor G d) (R : Finset V) {v : V}
    (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R)) (η η' : LocalVirtualConfig A v)
    (hcons : InsertConsistent (G := G) A R μ η)
    (hcons' : InsertConsistent (G := G) A R μ η')
    (hbridge : boundaryLabelOfInsert (G := G) A R hv μ η =
      boundaryLabelOfInsert (G := G) A R hv μ η') :
    η = η' := by
  classical
  funext ie
  by_cases hinc : IsRegionIncidentEdge (G := G) R ie.1
  · -- `v`-incident and `R`-incident: an `R`-boundary edge; the bridge label reads `η`.
    have hb : IsRegionBoundaryEdge (G := G) R ie.1 :=
      isRegionBoundaryEdge_of_vIncident_regionIncident (G := G) R hv ie.2 hinc
    have h1 : boundaryLabelOfInsert (G := G) A R hv μ η ⟨ie.1, hb⟩ = η ie := by
      rw [boundaryLabelOfInsert, dif_pos ie.2]
    have h2 : boundaryLabelOfInsert (G := G) A R hv μ η' ⟨ie.1, hb⟩ = η' ie := by
      rw [boundaryLabelOfInsert, dif_pos ie.2]
    rw [← h1, ← h2, congrFun hbridge ⟨ie.1, hb⟩]
  · -- `v`-incident, non-`R`-incident: a `v`-incident `insert v R`-boundary edge.
    have hb : IsRegionBoundaryEdge (G := G) (insert v R) ie.1 :=
      isRegionBoundaryEdge_insert_of_vIncident_not_regionIncident (G := G) R ie.2 hinc
    have h1 : η ie = μ ⟨ie.1, hb⟩ := (hcons ⟨ie.1, hb⟩ ie.2).symm
    have h2 : η' ie = μ ⟨ie.1, hb⟩ := (hcons' ⟨ie.1, hb⟩ ie.2).symm
    rw [h1, h2]

/-! ### The inserted-site factorization in bridge-weight form

Assembling the inserted-site factorization
`insertOuterBondProd_smul_regionBlockedWeight_insert` with the residual collapse
`insertOuterBondProd_smul_insertResidual_eq` reads the inserted-site multiplicity
times the blocked weight of `insert v R` as the sum, over local configurations `η`
at `v`, of the inserted-site tensor against the bridge-label blocked weight of `R`
on the configurations consistent with `μ`, and zero otherwise. -/

open scoped Classical in
/-- **The inserted-site factorization through the bridge-label blocked weight.**

The inserted-site multiplicity times the blocked weight of `insert v R` at `μ`, `σ`
is the sum over local configurations `η` of the inserted site `v` of the
inserted-site tensor `A.component v η (σ_v)` against the blocked weight of `R` at the
bridge label `boundaryLabelOfInsert μ η` when `μ` and `η` are consistent, and zero
otherwise.

This combines `insertOuterBondProd_smul_regionBlockedWeight_insert` (which isolates
the inserted-site tensor against the multiplicity-scaled residual) with
`insertOuterBondProd_smul_insertResidual_eq` (which collapses that scaled residual to
the bridge-label blocked weight on consistent configurations).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem insertOuterBondProd_smul_regionBlockedWeight_insert_eq_bridge (A : Tensor G d)
    (R : Finset V) {v : V} (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    insertOuterBondProd (G := G) A R (v := v) •
        regionBlockedWeight (G := G) A (insert v R) μ σ =
      ∑ η : LocalVirtualConfig A v,
        A.component v η (σ ⟨v, Finset.mem_insert_self v R⟩) *
          (if InsertConsistent (G := G) A R μ η then
            regionBlockedWeight (G := G) A R (boundaryLabelOfInsert (G := G) A R hv μ η)
              (restrictInsertPhysical (V := V) (d := d) R σ)
          else 0) := by
  rw [insertOuterBondProd_smul_regionBlockedWeight_insert (G := G) A R hv μ σ]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [insertOuterBondProd_smul_insertResidual_eq (G := G) A R hv μ σ η]

/-! ### A boundary label making a chosen local configuration consistent

Every local configuration `η` at `v` is consistent with the boundary label that
reads `η` on the `v`-incident edges and is arbitrary elsewhere; this realizes `η`
as a consistent configuration of some `μ`, so the per-vertex relation extracted
below holds at every `η`. -/

open scoped Classical in
/-- A boundary label of `insert v R` reading the chosen local configuration `η` on
the `v`-incident edges and a supplied base label `μ₀` elsewhere. -/
noncomputable def insertConsistentExtend (A : Tensor G d) (R : Finset V) {v : V}
    (μ₀ : RegionBoundaryConfig (G := G) A (insert v R))
    (η : LocalVirtualConfig A v) : RegionBoundaryConfig (G := G) A (insert v R) :=
  fun g =>
    if hgv : g.1.1.1 = v ∨ g.1.1.2 = v then η ⟨g.1, hgv⟩ else μ₀ g

omit [Fintype V] in
/-- The chosen local configuration is consistent with its boundary-label extension. -/
theorem insertConsistent_insertConsistentExtend (A : Tensor G d) (R : Finset V) {v : V}
    (μ₀ : RegionBoundaryConfig (G := G) A (insert v R))
    (η : LocalVirtualConfig A v) :
    InsertConsistent (G := G) A R (insertConsistentExtend (G := G) A R μ₀ η) η := by
  classical
  intro g hgv
  rw [insertConsistentExtend, dif_pos hgv]

/-- The inserted-site overcounting multiplicity is positive when every bond
dimension is positive. -/
theorem insertOuterBondProd_pos (A : Tensor G d) (R : Finset V) {v : V}
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    0 < insertOuterBondProd (G := G) A R (v := v) := by
  rw [insertOuterBondProd]
  exact Finset.prod_pos (fun e _ => hpos e)

/-! ### The scalar extraction

From the two region proportionalities `A_R = c_R · C_R` and `A_S = c_S · C_S` (with
`C` the reindexed comparison tensor) and the inserted-site factorization, the
inserted-site tensor of `A` and of `C` are scalar proportional with ratio
`c_S / c_R`, separated by linear independence of `C`'s `R`-blocked family. -/

open scoped Classical in
/-- **The inserted-site scalar extraction.**

Let `C := reindexTensor Btilde hbd` be the comparison tensor transported to `A`'s
bonds.  If the blocked weights of `A` and `C` are scalar proportional with nonzero
ratio `c_R` over the region `R` and with ratio `c_S` over the one-site-larger region
`insert v R`, the multiplicity over `R` is nonzero, and `C`'s `R`-blocked family is
linearly independent, then the inserted-site tensors of `A` and `C` are scalar
proportional with ratio `c_S / c_R` at every local configuration `η` at `v`:
`A.component v η σ = (c_S / c_R) · C.component v η σ`.

The inserted-site factorization
`insertOuterBondProd_smul_regionBlockedWeight_insert_eq_bridge` reads each blocked
weight of `insert v R` as the inserted-site tensor against the bridge-label blocked
weight of `R` on the consistent local configurations.  Substituting the
`R`-proportionality and cancelling the (nonzero, bond-only) inserted-site
multiplicity gives, for every choice of base boundary label `μ`, a vanishing
combination of `C`'s `R`-blocked family weighted by `c_R · A_v(η) - c_S · C_v(η)` over
the consistent `η`.  The consistent local configurations inject into their bridge
labels (`localConfig_eq_of_insertConsistent`), so linear independence separates the
combination to a single term, forcing `c_R · A_v(η) = c_S · C_v(η)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem component_eq_of_regionProportional (A Btilde : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R) (hbd : A.bondDim = Btilde.bondDim)
    (c_R c_S : ℂ) (hcR : c_R ≠ 0)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hCinj : RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) R)
    (hR : ∀ (b : RegionBoundaryConfig (G := G) A R)
        (ρ : RegionPhysicalConfig (V := V) (d := d) R),
        regionBlockedWeight (G := G) A R b ρ =
          c_R * regionBlockedWeight (G := G) (reindexTensor (G := G) Btilde hbd) R b ρ)
    (hS : ∀ (μ : RegionBoundaryConfig (G := G) A (insert v R))
        (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)),
        regionBlockedWeight (G := G) A (insert v R) μ σ =
          c_S * regionBlockedWeight (G := G) (reindexTensor (G := G) Btilde hbd)
            (insert v R) μ σ)
    (η : LocalVirtualConfig A v) (σv : Fin d) :
    A.component v η σv =
      (c_S / c_R) *
        (reindexTensor (G := G) Btilde hbd).component v η σv := by
  classical
  set C := reindexTensor (G := G) Btilde hbd with hCdef
  set m := insertOuterBondProd (G := G) A R (v := v) with hmdef
  have hm : m ≠ 0 := (insertOuterBondProd_pos (G := G) A R hpos).ne'
  -- A base boundary label making `η` consistent (only the `v`-incident values matter).
  let μ : RegionBoundaryConfig (G := G) A (insert v R) :=
    insertConsistentExtend (G := G) A R (fun g => ⟨0, hpos g.1⟩) η
  have hcons : InsertConsistent (G := G) A R μ η :=
    insertConsistent_insertConsistentExtend (G := G) A R _ η
  -- The vanishing combination of `C`'s `R`-blocked family, for each region physical config `ρ`.
  -- Coefficient at bridge label `b`: the consistent `η'` in the bridge-fiber of `b`, weighted by
  -- `c_R · A_v(η') - c_S · C_v(η')`.
  set g : RegionBoundaryConfig (G := G) A R → ℂ :=
    (fun b => ∑ η' ∈ Finset.univ.filter
        (fun η' : LocalVirtualConfig A v =>
          InsertConsistent (G := G) A R μ η' ∧
            boundaryLabelOfInsert (G := G) A R hv μ η' = b),
      (c_R * A.component v η' σv - c_S * C.component v η' σv)) with hgdef
  -- The combination vanishes as a function of the region physical configuration.
  -- The inserted-site weight factor at a local config, common to both sides.
  set gC : LocalVirtualConfig A v → RegionPhysicalConfig (V := V) (d := d) R → ℂ :=
    (fun η' ρ => if InsertConsistent (G := G) A R μ η' then
      regionBlockedWeight (G := G) C R (boundaryLabelOfInsert (G := G) A R hv μ η') ρ else 0)
    with hgCdef
  have hcomb : ∀ ρ : RegionPhysicalConfig (V := V) (d := d) R,
      ∑ b : RegionBoundaryConfig (G := G) A R, g b * regionBlockedTensorFamily (G := G) C R b ρ
        = 0 := by
    intro ρ
    -- Extend `ρ` and `σv` to a physical configuration on `insert v R`.
    let σ : RegionPhysicalConfig (V := V) (d := d) (insert v R) :=
      fun w => if hw : w.1 ∈ R then ρ ⟨w.1, hw⟩ else σv
    have hσR : restrictInsertPhysical (V := V) (d := d) R σ = ρ := by
      funext w
      rw [restrictInsertPhysical]
      simp only [σ, dif_pos w.2]
    have hσv : σ ⟨v, Finset.mem_insert_self v R⟩ = σv := by
      simp only [σ, dif_neg hv]
    -- Regroup the bridge-label sum over the consistent local configurations.
    have hregroup :
        ∑ b : RegionBoundaryConfig (G := G) A R, g b * regionBlockedTensorFamily (G := G) C R b ρ
          = ∑ η' : LocalVirtualConfig A v,
              (c_R * A.component v η' σv - c_S * C.component v η' σv) * gC η' ρ := by
      -- Step 1: expand `g b`, distribute the weight, and rewrite the weight at each fiber's label.
      have step1 :
          ∑ b : RegionBoundaryConfig (G := G) A R, g b * regionBlockedTensorFamily (G := G) C R b ρ
            = ∑ b : RegionBoundaryConfig (G := G) A R,
                ∑ η' ∈ Finset.univ.filter
                    (fun η' : LocalVirtualConfig A v =>
                      InsertConsistent (G := G) A R μ η' ∧
                        boundaryLabelOfInsert (G := G) A R hv μ η' = b),
                  (c_R * A.component v η' σv - c_S * C.component v η' σv) *
                    regionBlockedWeight (G := G) C R
                      (boundaryLabelOfInsert (G := G) A R hv μ η') ρ := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [hgdef]
        simp only
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun η' hη' => ?_)
        rw [Finset.mem_filter] at hη'
        rw [regionBlockedTensorFamily, hη'.2.2]
      -- Step 2: match the fiber filters and collapse them to the filtered sum over consistent
      -- configurations.
      rw [step1]
      have hfiber : ∀ b : RegionBoundaryConfig (G := G) A R,
          (Finset.univ.filter
              (fun η' : LocalVirtualConfig A v =>
                InsertConsistent (G := G) A R μ η' ∧
                  boundaryLabelOfInsert (G := G) A R hv μ η' = b))
            = (Finset.univ.filter
                (fun η' : LocalVirtualConfig A v => InsertConsistent (G := G) A R μ η')).filter
                (fun η' => boundaryLabelOfInsert (G := G) A R hv μ η' = b) := by
        intro b; rw [Finset.filter_filter]
      simp_rw [hfiber]
      rw [Finset.sum_fiberwise (Finset.univ.filter
            (fun η' : LocalVirtualConfig A v => InsertConsistent (G := G) A R μ η'))
          (fun η' => boundaryLabelOfInsert (G := G) A R hv μ η')
          (fun η' => (c_R * A.component v η' σv - c_S * C.component v η' σv) *
            regionBlockedWeight (G := G) C R (boundaryLabelOfInsert (G := G) A R hv μ η') ρ)]
      -- Step 3: convert the filtered sum to a full sum using `gC`'s consistency `if`/`else`.
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun η' _ => ?_)
      simp only [hgCdef]
      by_cases hc : InsertConsistent (G := G) A R μ η'
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hregroup]
    -- The vanishing combination from the two factorizations.
    -- The C-side inserted-site factorization at the base label `μ`.
    have hCfact : m • regionBlockedWeight (G := G) C (insert v R) μ σ
        = ∑ η' : LocalVirtualConfig A v, C.component v η' σv * gC η' ρ := by
      rw [hmdef, show (insertOuterBondProd (G := G) A R (v := v) : ℕ)
          = insertOuterBondProd (G := G) C R (v := v) from rfl,
        insertOuterBondProd_smul_regionBlockedWeight_insert_eq_bridge (G := G) C R hv μ σ]
      refine Finset.sum_congr rfl (fun η' _ => ?_)
      rw [hσv]
      simp only [hgCdef, hσR]
      rfl
    -- The A-side inserted-site factorization at the base label `μ`, substituting `hR`.
    have hAfact : m • regionBlockedWeight (G := G) A (insert v R) μ σ
        = c_R * ∑ η' : LocalVirtualConfig A v, A.component v η' σv * gC η' ρ := by
      rw [hmdef,
        insertOuterBondProd_smul_regionBlockedWeight_insert_eq_bridge (G := G) A R hv μ σ,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun η' _ => ?_)
      rw [hσv]
      simp only [hgCdef, hσR]
      rw [mul_left_comm]
      congr 1
      by_cases hc : InsertConsistent (G := G) A R μ η'
      · rw [if_pos hc, if_pos hc, hR (boundaryLabelOfInsert (G := G) A R hv μ η') ρ]
      · rw [if_neg hc, if_neg hc, mul_zero]
    -- Equate the two factorizations through `hS`.
    have hAS : m • regionBlockedWeight (G := G) A (insert v R) μ σ
        = c_S * (m • regionBlockedWeight (G := G) C (insert v R) μ σ) := by
      rw [hS μ σ, mul_smul_comm]
    rw [hAfact, hCfact] at hAS
    -- `c_R · ∑ A_v·gC = c_S · ∑ C_v·gC`, hence the difference sum vanishes.
    -- Rewrite the combination as the difference of the two scaled sums.
    rw [show (∑ η' : LocalVirtualConfig A v,
          (c_R * A.component v η' σv - c_S * C.component v η' σv) * gC η' ρ)
        = (c_R * ∑ η' : LocalVirtualConfig A v, A.component v η' σv * gC η' ρ)
          - c_S * ∑ η' : LocalVirtualConfig A v, C.component v η' σv * gC η' ρ from ?_]
    · rw [hAS, sub_self]
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun η' _ => ?_)
      ring
  -- Linear independence separates the combination to each coefficient.
  have hgzero : ∀ b, g b = 0 := by
    have hli := hCinj
    rw [RegionBlockedTensorInjective, Fintype.linearIndependent_iff] at hli
    refine hli g ?_
    funext ρ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    trans ∑ b : RegionBoundaryConfig (G := G) A R,
        g b * regionBlockedTensorFamily (G := G) C R b ρ
    · exact Finset.sum_congr rfl (fun _ _ => rfl)
    · exact hcomb ρ
  -- The bridge fiber of `boundaryLabelOfInsert μ η` over the consistent configs is `{η}`.
  have hgη : g (boundaryLabelOfInsert (G := G) A R hv μ η)
      = c_R * A.component v η σv - c_S * C.component v η σv := by
    rw [hgdef]
    beta_reduce
    rw [Finset.filter_congr (q := fun η' => η' = η) ?_]
    · rw [Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]
    · intro η' _
      constructor
      · rintro ⟨hcons', hbr⟩
        exact localConfig_eq_of_insertConsistent (G := G) A R hv μ η' η hcons' hcons hbr
      · rintro rfl
        exact ⟨hcons, rfl⟩
  -- Read off the per-vertex relation.
  have hsub : c_R * A.component v η σv - c_S * C.component v η σv = 0 :=
    hgη ▸ hgzero (boundaryLabelOfInsert (G := G) A R hv μ η)
  have heq : c_R * A.component v η σv = c_S * C.component v η σv := sub_eq_zero.mp hsub
  change A.component v η σv = (c_S / c_R) * C.component v η σv
  rw [div_mul_eq_mul_div, eq_div_iff hcR]
  simpa [mul_comm] using heq

/-! ### The per-vertex gauge relation from two two-block proportionalities

Packaging the scalar extraction with the comparison output: when the comparison
tensor is the gauge-absorbed second tensor `applyGauge B X`, the reindexed
inserted-site tensor is the gauge action `gaugeVertex B X` at `v`, so the scalar
extraction reads as the per-vertex gauge relation
`A.component v η = (c_S / c_R) · gaugeVertex B X v (η)` the torus theorem consumes. -/

open scoped Classical in
/-- **The per-vertex gauge relation from the two region proportionalities.**

When the comparison tensor is the gauge-absorbed second tensor `applyGauge B X`, the
two-block scalar proportionalities of the blocked weights of `A` and `applyGauge B X`
over `R` and over `insert v R` (the outputs of `regionComplement_comparison` at the
two comparison regions) yield the per-vertex gauge relation
`A.component v η σ = (c_S / c_R) · gaugeVertex B X v (Fin.cast … η) σ` at every local
configuration `η` of the inserted site `v`.

The proportionalities are fed to `component_eq_of_regionProportional`; the reindexed
inserted-site tensor of `applyGauge B X` is the gauge action `gaugeVertex B X v` at
`v` by `reindexTensor_component` and `applyGauge`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem component_eq_gaugeVertex_of_twoBlockProportional (A B : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R) (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (c_R c_S : ℂ) (hcR : c_R ≠ 0)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hCinj : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) R)
    (hRprop : TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
      (regionTwoBlock (G := G) (reindexTensor (G := G) (applyGauge B X) hbd) R) c_R)
    (hSprop : TwoBlockScalarProportional (regionTwoBlock (G := G) A (insert v R))
      (regionTwoBlock (G := G) (reindexTensor (G := G) (applyGauge B X) hbd) (insert v R)) c_S)
    (η : LocalVirtualConfig A v) (σ : Fin d) :
    A.component v η σ =
      (c_S / c_R) *
        gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ := by
  have hext := component_eq_of_regionProportional A (applyGauge B X) R hv hbd c_R c_S hcR hpos
    hCinj
    (fun b ρ => hRprop PUnit.unit b ρ)
    (fun μ σ' => hSprop PUnit.unit μ σ')
    η σ
  rw [hext, reindexTensor_component]
  rfl

end PEPS
end TNLean
