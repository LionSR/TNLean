import TNLean.PEPS.RegionBlock.Recovery6

/-!
# Block-level image coincidence for the normal PEPS Fundamental Theorem

This file proves the **block-level image coincidence** lemma: under `SameState`,
the range of the blocked-region tensor map of a region `R` is the same for two
tensors `A` and `B`, provided the *complement* block `univ \ R` of each tensor is
blocked-tensor injective and the bond dimensions are positive and equal.

This is the block-granularity analogue of the vertex-level image coincidence
`range_localTensorMap_eq_of_sameState` of `TNLean.PEPS.RegionBlock.Recovery3`. The
vertex frame is too weak for the general normal theorem because a single vertex
need not be injective; the *block* `R` is the object that is injective in the
normal setting, so the image coincidence must hold at block granularity.

## The Schmidt-span argument

Both ranges equal the column space of the global state across the `R` / complement
cut, which is `SameState`-invariant. Concretely, both ranges equal the span of the
**partial states**

> `regionPartialState A R τ := fun σ => stateCoeff A (assembleRegionσ R σ τ)`

as the complement physical configuration `τ` ranges. The proof mirrors the
vertex-level proof of `TNLean.PEPS.RegionBlock.Recovery3` at block granularity:

* The range of the blocked-region tensor map is the span of the blocked-region
  weights (`Fintype.range_linearCombination`).
* Each partial state is, up to the nonzero interior bond multiplicity, a
  blocked-region-weight combination of `A` over `R` (the identity-insertion
  reading of the closed state coefficient), so the partial states lie in the span
  of the blocked-region weights.
* Conversely, blocked-tensor injectivity of the complement
  (`RegionBlockedTensorInjective A (univ \ R)`) makes the complement weight family
  linearly independent, so by `span_cols_eq_top_of_linearIndependent` its columns
  span; this realizes every blocked-region weight as a partial-state combination.
* The partial states depend only on `stateCoeff`, so they are `SameState`-invariant.

Combining these gives
`range (regionBlockedTensorMap A R) = span τ {regionPartialState A R τ}
  = span τ {regionPartialState B R τ} = range (regionBlockedTensorMap B R)`,
the block analogue of `range_localTensorMap_eq_of_sameState`.

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

/-! ### The partial states across the region cut

The partial state at a complement physical configuration `τ` is the closed state
coefficient of the assembled global configuration, read as a function of the
region physical configuration `σ`. It is the column of the global state vector
across the `R` / complement cut at the fixed complement configuration `τ`. -/

/-- The partial state across the region cut at a complement physical
configuration `τ`: the closed state coefficient of `assembleRegionσ R σ τ`, viewed
as a function of the region physical configuration `σ`. This is a column of the
global state vector across the `R` / complement cut. -/
noncomputable def regionPartialState (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionPhysicalConfig (V := V) (d := d) R → ℂ :=
  fun σ => stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ)

/-- The partial state depends on the tensor only through its closed state
coefficient, so it is invariant under `SameState`. -/
theorem regionPartialState_sameState {A B : Tensor G d} (hAB : SameState A B)
    (R : Finset V) (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionPartialState (G := G) A R τ = regionPartialState (G := G) B R τ := by
  funext σ
  rw [regionPartialState, regionPartialState, hAB]

/-! ### The range of the blocked-region tensor map is the span of its weights

The blocked-region tensor map is the linear combination of the blocked-region
weight family, so its range is the span of those weights. -/

/-- The range of the blocked-region tensor map is the span of the blocked-region
weights, since the map is `Fintype.linearCombination` of the weight family. -/
theorem range_regionBlockedTensorMap_eq_span (A : Tensor G d) (R : Finset V) :
    LinearMap.range (regionBlockedTensorMap (G := G) A R) =
      Submodule.span ℂ
        (Set.range (fun μ : RegionBoundaryConfig (G := G) A R =>
          regionBlockedWeight (G := G) A R μ)) := by
  rw [regionBlockedTensorMap, Fintype.range_linearCombination]
  rfl

/-! ### The blocked-region-weight contraction of the closed state coefficient

Contracting the blocked-region weight on `R` against the blocked-region weight on
`univ \ R`, summed over the boundary configuration, reads the interior bond
multiple of the closed state coefficient. This is the edge-free form of the
identity-insertion reading `regionInsertedCoeff_one_eq_stateCoeff`: it does not
single out a boundary edge, so it applies to a region with no boundary edge as
well. -/

open scoped Classical in
/-- The boundary-configuration contraction of the region weight against the
complement weight reads the interior bond multiple of the closed state
coefficient. This is the edge-free identity-insertion reading: it follows from the
double-global-configuration form of the closed-state split
(`stateCoeff_eq_regionComplement`) after expanding both weights. -/
theorem sum_regionBlockedWeight_mul_complement (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A R μ σ *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ) =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  rw [← stateCoeff_eq_regionComplement (G := G) A R σ τ]
  -- Expand both blocked-region weights as filtered sums over global configurations.
  simp only [regionBlockedWeight]
  -- Distribute the products of filtered sums and reorganize into the
  -- boundary-agreement pair sum, mirroring `regionInsertedCoeff_identity_eq_doubleSum`.
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
  · -- The complement filter matches the region filter after the boundary-edge
    -- identification, and the product of sums is the doubled sum.
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

/-! ### The partial state lies in the span of the blocked-region weights

The interior bond multiple of a partial state is the blocked-region-weight
combination whose coefficients are the complement weights at the fixed complement
configuration. Since the interior bond multiplicity is a nonzero scalar, the
partial state itself lies in the span of the blocked-region weights. -/

/-- The interior bond multiple of a partial state is the blocked-region-weight
combination of `A` over `R` with the complement weights as coefficients. This is
`sum_regionBlockedWeight_mul_complement` read as an equality of functions of the
region physical configuration. -/
theorem regionInteriorBondProd_smul_regionPartialState (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ •
          regionBlockedWeight (G := G) A R μ := by
  funext σ
  -- The right side, evaluated at `σ`, is the doubled-sum identity reading.
  have hsum := sum_regionBlockedWeight_mul_complement (G := G) A R σ τ
  simp only [nsmul_eq_mul] at hsum
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  -- Both sides are now the interior bond multiple of the closed state coefficient.
  rw [show regionPartialState (G := G) A R τ σ =
      stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) from rfl, ← hsum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [mul_comm]

/-- **The partial state lies in the span of the blocked-region weights.** Its
interior bond multiple is a blocked-region-weight combination
(`regionInteriorBondProd_smul_regionPartialState`), and the interior bond
multiplicity is a nonzero scalar (positive bond dimensions), so dividing it out
keeps the partial state in the span. -/
theorem regionPartialState_mem_span_regionBlockedWeight (A : Tensor G d) (R : Finset V)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionPartialState (G := G) A R τ ∈
      Submodule.span ℂ (Set.range (fun μ : RegionBoundaryConfig (G := G) A R =>
        regionBlockedWeight (G := G) A R μ)) := by
  have hne : (regionInteriorBondProd (G := G) A R : ℂ) ≠ 0 := by
    have hpos : 0 < regionInteriorBondProd (G := G) A R :=
      Finset.prod_pos (fun e _ => hposA e)
    exact_mod_cast hpos.ne'
  rw [← Submodule.smul_mem_iff _ hne,
    regionInteriorBondProd_smul_regionPartialState (G := G) A R τ]
  refine Submodule.sum_mem _ (fun μ _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)

/-! ### The blocked-region weights lie in the span of the partial states

Blocked-tensor injectivity of the complement makes the complement weight family
linearly independent, so by `span_cols_eq_top_of_linearIndependent` its columns
span the full complement boundary-configuration space. Choosing the column
combination realizing the standard basis vector at a boundary configuration `μ`
extracts the single blocked-region weight of `μ` from the partial-state
combination. -/

/-- **The blocked-region weights lie in the span of the partial states.** Under
blocked-tensor injectivity of the complement, the complement weight columns span
the complement boundary-configuration space, so for each boundary configuration
`μ` there is a complement-physical combination whose complement weights pick out
the Kronecker delta at `μ`. Applying that combination to the partial-state reading
of the interior bond multiple isolates the blocked-region weight of `μ`. -/
theorem regionBlockedWeight_mem_span_regionPartialState (A : Tensor G d) (R : Finset V)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (μ : RegionBoundaryConfig (G := G) A R) :
    regionBlockedWeight (G := G) A R μ ∈
      Submodule.span ℂ
        (Set.range (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          regionPartialState (G := G) A R τ)) := by
  classical
  -- The complement weight family is linearly independent (blocked injectivity).
  have hli : LinearIndependent ℂ (regionBlockedTensorFamily (G := G) A (Finset.univ \ R)) := hCA
  -- Its columns span the complement boundary-configuration space.
  have hcols := span_cols_eq_top_of_linearIndependent
    (regionBlockedTensorFamily (G := G) A (Finset.univ \ R)) hli
  -- The standard basis vector at `regionComplementBoundaryConfig μ` lies in the
  -- column span, so it is a finite combination of the columns indexed by `τ`.
  set ν₀ : RegionBoundaryConfig (G := G) A (Finset.univ \ R) :=
    regionComplementBoundaryConfig (G := G) A R μ with hν₀
  have hmem : Pi.single ν₀ (1 : ℂ) ∈
      Submodule.span ℂ (Set.range
        (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          fun ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
            regionBlockedTensorFamily (G := G) A (Finset.univ \ R) ν τ)) := by
    rw [hcols]; trivial
  -- Read off the column combination as a finitely-supported coefficient family `a`.
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨a, ha⟩ := hmem
  -- `ha` evaluated at a complement boundary configuration `ν` reads the chosen
  -- column combination off the Kronecker delta `Pi.single ν₀ 1 ν`.
  have hcombo : ∀ ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R),
      (∑ τ ∈ a.support, a τ * regionBlockedWeight (G := G) A (Finset.univ \ R) ν τ) =
        (Pi.single ν₀ (1 : ℂ) :
          RegionBoundaryConfig (G := G) A (Finset.univ \ R) → ℂ) ν := by
    intro ν
    have := congrFun ha ν
    rw [Finsupp.sum] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      regionBlockedTensorFamily] at this
    exact this
  -- `regionComplementBoundaryConfig` is injective, so the Kronecker delta at `ν₀`
  -- read on `complBdry μ'` is the Kronecker delta at `μ` read on `μ'`.
  have hδ : ∀ μ' : RegionBoundaryConfig (G := G) A R,
      (Pi.single ν₀ (1 : ℂ) :
          RegionBoundaryConfig (G := G) A (Finset.univ \ R) → ℂ)
          (regionComplementBoundaryConfig (G := G) A R μ') =
        (Pi.single μ (1 : ℂ) : RegionBoundaryConfig (G := G) A R → ℂ) μ' := by
    intro μ'
    by_cases hμ' : μ' = μ
    · subst hμ'; rw [hν₀, Pi.single_eq_same, Pi.single_eq_same]
    · have hne : regionComplementBoundaryConfig (G := G) A R μ' ≠ ν₀ := by
        rw [hν₀]
        exact fun hc => hμ' ((regionComplementBoundaryConfigEquiv (G := G) A R).injective hc)
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hμ']
  -- The blocked-region weight of `μ` is the same combination of the partial
  -- states, scaled by the interior bond multiplicity.
  have hweight : regionBlockedWeight (G := G) A R μ =
      ∑ τ ∈ a.support,
        ((regionInteriorBondProd (G := G) A R : ℂ) * a τ) •
          regionPartialState (G := G) A R τ := by
    funext σ
    rw [Finset.sum_apply]
    -- Pull the interior bond factor through each partial state and expand the
    -- scaled partial state as the complement-weight combination.
    have hstep : ∀ τ ∈ a.support,
        (((regionInteriorBondProd (G := G) A R : ℂ) * a τ) •
            regionPartialState (G := G) A R τ) σ =
          ∑ μ' : RegionBoundaryConfig (G := G) A R,
            a τ * (regionBlockedWeight (G := G) A (Finset.univ \ R)
                (regionComplementBoundaryConfig (G := G) A R μ') τ *
              regionBlockedWeight (G := G) A R μ' σ) := by
      intro τ _
      -- The interior bond multiple of the partial state is the complement-weight
      -- combination, evaluated at `σ`.
      have hkey := congrFun (regionInteriorBondProd_smul_regionPartialState (G := G) A R τ) σ
      rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hkey
      simp only [Pi.smul_apply, smul_eq_mul] at hkey
      -- Reassociate the left side, pull the bond factor onto the partial state,
      -- and substitute the combination; then redistribute `a τ` over the sum.
      rw [Pi.smul_apply, smul_eq_mul, mul_comm (regionInteriorBondProd (G := G) A R : ℂ) (a τ),
        mul_assoc, hkey, Finset.mul_sum]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    -- On each `μ'` the τ-sum collapses to the Kronecker delta via `hcombo`, `hδ`.
    have hinner : ∀ μ' : RegionBoundaryConfig (G := G) A R,
        (∑ τ ∈ a.support,
            a τ * (regionBlockedWeight (G := G) A (Finset.univ \ R)
                (regionComplementBoundaryConfig (G := G) A R μ') τ *
              regionBlockedWeight (G := G) A R μ' σ)) =
          (Pi.single μ (1 : ℂ) : RegionBoundaryConfig (G := G) A R → ℂ) μ' *
            regionBlockedWeight (G := G) A R μ' σ := by
      intro μ'
      rw [Finset.sum_congr rfl (fun τ _ => (mul_assoc (a τ) _ _).symm), ← Finset.sum_mul,
        hcombo (regionComplementBoundaryConfig (G := G) A R μ'), hδ μ']
    rw [Finset.sum_congr rfl (fun μ' _ => hinner μ')]
    -- The μ'-sum of `Pi.single μ 1 μ' * weight_R μ' σ` is `weight_R μ σ`.
    rw [Finset.sum_eq_single μ]
    · rw [Pi.single_eq_same, one_mul]
    · intro μ' _ hμ'; rw [Pi.single_eq_of_ne hμ', zero_mul]
    · intro h; exact absurd (Finset.mem_univ μ) h
  rw [hweight]
  refine Submodule.sum_mem _ (fun τ _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ, rfl⟩)

/-! ### The range of the blocked-region tensor map is the span of the partial states

The two span-membership directions show that the span of the blocked-region
weights and the span of the partial states coincide. With the range read as the
span of the weights, the range of the blocked-region tensor map is the span of the
partial states. -/

/-- **The range of the blocked-region tensor map is the span of the partial
states.** Combining the range-as-weight-span reading
(`range_regionBlockedTensorMap_eq_span`) with the two span-membership directions
(`regionPartialState_mem_span_regionBlockedWeight`,
`regionBlockedWeight_mem_span_regionPartialState`) identifies the range with the
span of the partial states across the region cut. -/
theorem range_regionBlockedTensorMap_eq_span_regionPartialState (A : Tensor G d)
    (R : Finset V)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) :
    LinearMap.range (regionBlockedTensorMap (G := G) A R) =
      Submodule.span ℂ
        (Set.range (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          regionPartialState (G := G) A R τ)) := by
  rw [range_regionBlockedTensorMap_eq_span]
  refine le_antisymm ?_ ?_
  · -- Span of weights ⊆ span of partial states: each weight is a partial-state combo.
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact regionBlockedWeight_mem_span_regionPartialState (G := G) A R hCA μ
  · -- Span of partial states ⊆ span of weights: each partial state is a weight combo.
    rw [Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    exact regionPartialState_mem_span_regionBlockedWeight (G := G) A R hposA τ

/-! ### Block-level image coincidence

Under `SameState`, the partial states of the two tensors coincide
(`regionPartialState_sameState`), so the spans of the partial states coincide.
With each range identified as the span of the partial states, the two ranges of
the blocked-region tensor maps coincide. This is the block-granularity analogue of
`range_localTensorMap_eq_of_sameState`. -/

/-- **Block-level image coincidence.** Under `SameState`, with both complement
blocks blocked-tensor injective and positive bond dimensions, the ranges of the
blocked-region tensor maps of the two tensors coincide. Both ranges equal the span
of the partial states across the region cut
(`range_regionBlockedTensorMap_eq_span_regionPartialState`), and the partial
states are `SameState`-invariant (`regionPartialState_sameState`).

This is the block analogue of `range_localTensorMap_eq_of_sameState`: the single
vertex of the vertex frame need not be injective, but the block is, so the image
coincidence holds at block granularity. It is the block-level image preservation
the general region-injective normal PEPS Fundamental Theorem needs.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem range_regionBlockedTensorMap_eq_of_sameState (A B : Tensor G d) (R : Finset V)
    (hAB : SameState A B)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    LinearMap.range (regionBlockedTensorMap (G := G) A R) =
      LinearMap.range (regionBlockedTensorMap (G := G) B R) := by
  rw [range_regionBlockedTensorMap_eq_span_regionPartialState A R hCA hposA,
    range_regionBlockedTensorMap_eq_span_regionPartialState B R hCB hposB]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩; exact ⟨τ, (regionPartialState_sameState hAB R τ).symm⟩
  · rintro ⟨τ, rfl⟩; exact ⟨τ, regionPartialState_sameState hAB R τ⟩

/-! ### Nonvanishing of the closed state coefficient under region injectivity

The region-injective analogue of `exists_stateCoeff_ne_zero`. The vertex-injective
proof splits the closed network at a single vertex; here the split is at an
arbitrary blocked region `R` whose complement is also injective. Both the region
weight family and the complement weight family are linearly independent, so the
bilinear pairing that builds the closed state coefficient cannot vanish
identically. -/

open scoped Classical in
/-- A region-injective PEPS with positive bond dimensions has a nonzero closed
state coefficient.

This is the region-injective analogue of `exists_stateCoeff_ne_zero`. The
vertex-injective version splits the closed network at a single vertex and uses
single-vertex injectivity (`localCoeff_eq_zero_of_contract_zero`); the normal
route replaces the single vertex by an arbitrary blocked region `R` whose
complement is also injective.

Splitting at `R` (`regionInteriorBondProd_smul_regionPartialState`) writes the
interior-bond multiple of every partial state across the region cut as the
blocked-region tensor map of `R` applied to the complement weights at the fixed
complement physical configuration. If every closed state coefficient vanished,
the partial states would vanish, so for each complement configuration `τ` the
complement weight family `μ ↦ regionBlockedWeight A (univ \ R) (compl μ) τ` would
lie in the kernel of the blocked-region tensor map of `R`; region injectivity of
`R` (the left inverse `regionBlockedLeftInverse`) forces it to vanish, so the
whole complement weight family would be identically zero, contradicting linear
independence of that family (region injectivity of the complement). The boundary
configuration on the complement is nonempty because positive bond dimensions make
every crossing-edge fibre nonempty. No physical-dimension hypothesis `0 < d` is
needed: region injectivity of the complement already forces a physical
configuration carrying nonzero weight.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`, read at the level of the closed state
coefficient rather than the bond-inserted coefficient. -/
theorem exists_stateCoeff_ne_zero_of_regionInjective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ σ : V → Fin d, stateCoeff A σ ≠ 0 := by
  classical
  -- Positive bond dimensions make every crossing-edge fibre nonempty, so the
  -- complement boundary-configuration type has a member `ν₀`.
  have hNeBdry : Nonempty (RegionBoundaryConfig (G := G) A (Finset.univ \ R)) :=
    ⟨fun f => ⟨0, hpos f.1⟩⟩
  obtain ⟨ν₀⟩ := hNeBdry
  -- The complement weight family is linearly independent, hence nonzero at `ν₀`.
  have hne : regionBlockedTensorFamily (G := G) A (Finset.univ \ R) ν₀ ≠ 0 := hC.ne_zero ν₀
  -- Some complement physical configuration gives a nonzero complement weight at `ν₀`.
  obtain ⟨τ₀, hτ₀⟩ :
      ∃ τ, regionBlockedWeight (G := G) A (Finset.univ \ R) ν₀ τ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (by funext τ; simpa [regionBlockedTensorFamily] using hall τ)
  -- Suppose, for contradiction, every closed state coefficient vanishes.
  by_contra hzero
  push Not at hzero
  -- Then every partial state across the region cut vanishes.
  have hpartial : ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
      regionPartialState (G := G) A R τ = 0 := by
    intro τ
    funext σ
    rw [regionPartialState, hzero, Pi.zero_apply]
  -- For each `τ`, the complement weights at `τ`, read through the boundary
  -- identification, form a kernel vector of the blocked-region tensor map of `R`.
  have hker : ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
      regionBlockedTensorMap (G := G) A R
          (fun μ : RegionBoundaryConfig (G := G) A R =>
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R μ) τ) = 0 := by
    intro τ
    -- The map applied to those coefficients is the interior-bond multiple of the
    -- partial state, which vanishes.
    funext σ
    rw [regionBlockedTensorMap_apply]
    have hsplit := congrFun
      (regionInteriorBondProd_smul_regionPartialState (G := G) A R τ) σ
    rw [Pi.smul_apply, hpartial τ, Pi.zero_apply, smul_zero, Finset.sum_apply] at hsplit
    simp only [Pi.smul_apply, smul_eq_mul] at hsplit
    rw [Pi.zero_apply]
    -- Match the map expansion to the split sum (both `c μ • weight μ σ`).
    simp only [smul_eq_mul]
    rw [← hsplit]
  -- Region injectivity of `R` forces every such complement-weight coefficient family
  -- to vanish (the chosen left inverse reads `0` off the kernel image).
  have hcompZero : ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
      (fun μ : RegionBoundaryConfig (G := G) A R =>
        regionBlockedWeight (G := G) A (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R μ) τ) = 0 := by
    intro τ
    have := regionBlockedTensorMap_injective_of_injective (G := G) A R hR
    have hzeroμ := this (a₁ := fun μ : RegionBoundaryConfig (G := G) A R =>
        regionBlockedWeight (G := G) A (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R μ) τ)
      (a₂ := 0) (by rw [hker τ, map_zero])
    exact hzeroμ
  -- The complement boundary identification is a bijection onto every complement
  -- configuration, so the whole complement weight family is identically zero.
  obtain ⟨μ₀, hμ₀⟩ :
      ∃ μ₀ : RegionBoundaryConfig (G := G) A R,
        regionComplementBoundaryConfig (G := G) A R μ₀ = ν₀ :=
    ⟨(regionComplementBoundaryConfigEquiv (G := G) A R).symm ν₀, by
      rw [← regionComplementBoundaryConfigEquiv_apply (G := G) A R]
      exact (regionComplementBoundaryConfigEquiv (G := G) A R).apply_symm_apply ν₀⟩
  have := congrFun (hcompZero τ₀) μ₀
  rw [hμ₀, Pi.zero_apply] at this
  exact hτ₀ this

end PEPS
end TNLean
