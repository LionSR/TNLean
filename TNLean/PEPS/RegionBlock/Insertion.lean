import TNLean.PEPS.NormalEdgeGauge
import TNLean.PEPS.FundamentalTheorem.OneVertexComparison

/-!
# Region-level matrix insertion for the normal PEPS Fundamental Theorem

For an arbitrary finite region `R`, this file inserts a matrix `M` on one of the
edges crossing the boundary of `R` and contracts the lattice as the two blocks
`R` and its complement `Vᶜ = univ \ R`. This is the region analogue of the
edge-centred insertion chain of `TNLean.PEPS.Blocking` and
`TNLean.PEPS.FundamentalTheorem.OneVertexComparison`.

There the two blocks are a single vertex `v` and its complement `V\{v}`, the
shared bonds are the edges incident to `v`, and `edgeInsertedCoeff` inserts a
matrix on one such edge. Here the two blocks are an arbitrary region `R` and its
complement, the shared bonds are the edges crossing the boundary of `R`, and
`regionInsertedCoeff` inserts a matrix on one such crossing edge.

The development mirrors the edge-level chain piece by piece:

* `regionInsertedCoeff` is the region analogue of `edgeInsertedCoeff`: insert `M`
  on a boundary edge `f`, contract the region `R` on one side and its complement
  on the other.
* `twoBlockInsertedCoeff_eq_regionInsertedCoeff` is the region analogue of
  `twoBlockInsertedCoeff_eq_edgeInsertedCoeff`: the abstract two-block inserted
  coefficient of the `R`/complement two-block pair equals `regionInsertedCoeff`.
* `sameTwoBlockInsertions_of_regionInsertedCoeff_eq` is the region analogue of
  `sameTwoBlockInsertions_of_edgeInsertedCoeff_eq`: equal region-inserted
  coefficients of two tensors give `SameTwoBlockInsertions` of the two
  `R`/complement two-block pairs, which is the input the abstract two-injective
  comparison (`one_vertex_complement_comparison`,
  `two_injective_tensor_insertion_comparison`) consumes.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Theorem 3
  and the theorem labelled `normal`, lines 1407--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 1205--1210 (one block against its
  complement) and lines 1475--1500 (each blocked region compared as an injective
  block).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Boundary edges of a region and its complement

An edge crosses the boundary of `R` precisely when it crosses the boundary of the
set complement `univ \ R`: in both cases exactly one endpoint lies in `R`. This
symmetry lets the complement block reuse the boundary bonds of `R`. -/

omit [DecidableRel G.Adj] in
/-- An edge crosses the boundary of `R` exactly when it crosses the boundary of
the set complement `univ \ R`. -/
theorem isRegionBoundaryEdge_compl_iff (R : Finset V) (f : Edge G) :
    IsRegionBoundaryEdge (G := G) (Finset.univ \ R) f ↔
      IsRegionBoundaryEdge (G := G) R f := by
  simp only [IsRegionBoundaryEdge, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- A boundary edge of `R`, reread as a boundary edge of the complement
`univ \ R`. -/
def regionBoundaryEdgeToCompl (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    {f : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ \ R) f} :=
  ⟨f.1, (isRegionBoundaryEdge_compl_iff (G := G) R f.1).mpr f.2⟩

/-- The boundary edges of `R` and of its complement `univ \ R` are the same
edges. -/
def regionBoundaryEdgeComplEquiv (R : Finset V) :
    {f : Edge G // IsRegionBoundaryEdge (G := G) R f} ≃
      {f : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ \ R) f} :=
  Equiv.subtypeEquivRight (fun f => (isRegionBoundaryEdge_compl_iff (G := G) R f).symm)

omit [DecidableRel G.Adj] in
@[simp] theorem regionBoundaryEdgeComplEquiv_apply_coe (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    ((regionBoundaryEdgeComplEquiv (G := G) R f) : Edge G) = f.1 := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem regionBoundaryEdgeComplEquiv_symm_apply_coe (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ \ R) f}) :
    (((regionBoundaryEdgeComplEquiv (G := G) R).symm f) : Edge G) = f.1 := rfl

/-! ### The complement region as a two-block tensor over the boundary of `R`

The complement block of `R` is the blocked tensor of the set complement
`univ \ R`, reindexed so that its open boundary legs are indexed by the boundary
edges of `R`. This is the second block in the region analogue of the
one-vertex-versus-complement comparison. -/

/-- The boundary configuration on the complement `univ \ R`, obtained from a
boundary configuration on `R` by reading each crossing edge under the
boundary-edge identification. -/
def regionComplementBoundaryConfig (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ R) :=
  fun f => bdry ((regionBoundaryEdgeComplEquiv (G := G) R).symm f)

/-- The complement boundary configuration reads the boundary edge `f` of `R`,
viewed on the complement as `regionBoundaryEdgeToCompl R f`, off the original
boundary value at `f`. -/
theorem regionComplementBoundaryConfig_apply_toCompl (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G) A R bdry (regionBoundaryEdgeToCompl (G := G) R f) =
      bdry f := by
  rw [regionComplementBoundaryConfig]
  congr 1

/-- The complement region `univ \ R`, viewed as an abstract two-block tensor over
the edges crossing the boundary of `R`.

This is the region analogue of `complementTwoBlock` from
`TNLean.PEPS.FundamentalTheorem.OneVertexComparison`: the role played there by the
single vertex `v` and its complement `V\{v}` is played here by the region `R` and
its set complement `univ \ R`, with the open boundary legs reindexed to the
boundary edges of `R`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`, where one block is compared against its
complement. -/
noncomputable def regionComplementTwoBlock (A : Tensor G d) (R : Finset V) :
    TwoBlockTensor (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (fun f => Fin (A.bondDim f.1)) PUnit
      (RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :=
  fun _ bdry τ =>
    regionBlockedWeight (G := G) A (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) A R bdry) τ

@[simp] theorem regionComplementTwoBlock_apply (A : Tensor G d) (R : Finset V)
    (u : PUnit) (bdry : RegionBoundaryConfig (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionComplementTwoBlock (G := G) A R u bdry τ =
      regionBlockedWeight (G := G) A (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R bdry) τ := rfl

/-- The complement region two-block tensor is two-block injective whenever the
blocked tensor family of the set complement `univ \ R` is linearly independent.

The boundary-configuration reindexing is a permutation of the open legs and so
preserves linear independence; the auxiliary one-point external boundary is
absorbed by `Equiv.punitProd`.

Source: arXiv:1804.04964, Section 3, lines 205--250 of
`Papers/1804.04964/paper_normal.tex`, where a contraction of injective tensors
over a region is injective. -/
theorem isTwoBlockInjective_regionComplementTwoBlock (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R)) :
    IsTwoBlockInjective (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (regionComplementTwoBlock (G := G) A R) := by
  classical
  -- Reindex the family through the punit and boundary-edge equivalences.
  have hfam : (fun η : PUnit × RegionBoundaryConfig (G := G) A R =>
        fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          regionComplementTwoBlock (G := G) A R η.1 η.2 τ) =
      (regionBlockedTensorFamily (G := G) A (Finset.univ \ R)) ∘
        (fun η : PUnit × RegionBoundaryConfig (G := G) A R =>
          regionComplementBoundaryConfig (G := G) A R η.2) := by
    funext η; rfl
  rw [IsTwoBlockInjective, hfam]
  refine hR.comp _ ?_
  -- The composite map `(unit, bdry) ↦ complement reindex of bdry` is injective.
  intro x y hxy
  obtain ⟨⟨⟩, bx⟩ := x
  obtain ⟨⟨⟩, by'⟩ := y
  simp only [Prod.mk.injEq, true_and]
  funext f
  have := congrFun hxy (regionBoundaryEdgeToCompl (G := G) R f)
  change regionComplementBoundaryConfig (G := G) A R bx
      (regionBoundaryEdgeToCompl (G := G) R f) =
    regionComplementBoundaryConfig (G := G) A R by'
      (regionBoundaryEdgeToCompl (G := G) R f) at this
  rwa [regionComplementBoundaryConfig_apply_toCompl,
    regionComplementBoundaryConfig_apply_toCompl] at this

/-! ### The region-inserted coefficient

Insert a matrix `M` on one edge `f` crossing the boundary of `R`, contract the
region `R` against its complement, and read off the resulting scalar. This is the
explicit doubled-sum form of the abstract two-block inserted coefficient of the
`R`/complement two-block pair. -/

open scoped Classical in
/-- The region-inserted coefficient: insert `M` on the boundary edge `f` of `R`,
contract `R` on one side and the complement `univ \ R` on the other, with all the
other boundary bonds contracted by the identity.

The sum has two boundary configurations `μ` (read by `R`) and `ν` (read by the
complement), constrained to agree away from `f`; `M` couples their values on `f`.
This is the region analogue of `edgeInsertedCoeff`, where the two endpoints of an
edge are replaced by the whole region and its complement, and the residual
endpoint stars are replaced by the region boundary configurations.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionInsertedCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : ℂ := by
  classical
  exact
    ∑ μ : RegionBoundaryConfig (G := G) A R,
      ∑ ν : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionBlockedWeight (G := G) A R μ σ *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R ν) τ

open scoped Classical in
/-- Unfolding lemma for `regionInsertedCoeff` (the explicit double-sum form). -/
theorem regionInsertedCoeff_eq (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ν : RegionBoundaryConfig (G := G) A R,
          (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
            regionBlockedWeight (G := G) A R μ σ *
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R ν) τ := by
  rw [regionInsertedCoeff]

/-! ### The region coefficient identity

The abstract two-block inserted coefficient of the `R`/complement two-block pair
equals `regionInsertedCoeff`. This is the region analogue of
`twoBlockInsertedCoeff_eq_edgeInsertedCoeff`. -/

open scoped Classical in
/-- **Region coefficient identity.** The abstract two-block inserted coefficient
of the region/complement two-block pair, with `M` inserted on a boundary edge `f`
of `R`, equals the region-inserted coefficient `regionInsertedCoeff`.

The external boundary spaces are one-point, so the external arguments are
`PUnit.unit`; the abstract shared-bond sums of `twoBlockInsertedCoeff` are exactly
the two boundary-configuration sums of `regionInsertedCoeff`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem twoBlockInsertedCoeff_eq_regionInsertedCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    twoBlockInsertedCoeff (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
        (bondDim := fun f => Fin (A.bondDim f.1))
        (regionTwoBlock (G := G) A R) (regionComplementTwoBlock (G := G) A R)
        f M PUnit.unit PUnit.unit σ τ =
      regionInsertedCoeff (G := G) A R f M σ τ := by
  classical
  rw [regionInsertedCoeff_eq, twoBlockInsertedCoeff]
  simp only [regionTwoBlock_apply, regionComplementTwoBlock_apply]
  -- The two doubled sums differ only by the index `Fintype` instance carried by the
  -- abstract `SharedBondConfig` (`Pi.instFintype`) versus the concrete
  -- `RegionBoundaryConfig` (`instFintypeRegionBoundaryConfig`); `Finset.ext` bridges the
  -- two `Finset.univ`s without forcing a costly definitional unfolding.
  refine Finset.sum_congr (by ext x; simp) (fun μ _ => ?_)
  refine Finset.sum_congr (by ext x; simp) (fun ν _ => rfl)

/-! ### Bond-dimension reindex of the region-inserted coefficient

To compare two tensors with the same bond dimensions, the second tensor is
transported to the first tensor's bond family. The region-inserted coefficient
transports by conjugating the inserted matrix with the reindexing equivalence,
matching `edgeInsertedCoeff_reindexTensor`. -/

/-- The blocked-region weight transports along a bond-dimension reindex: the
weight of the reindexed tensor at a boundary configuration is the weight of the
original tensor at the cast boundary configuration. -/
theorem regionBlockedWeight_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) (reindexTensor (G := G) B h) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) (reindexTensor (G := G) B h) R bdry τ =
      regionBlockedWeight (G := G) B R
        (fun f => Fin.cast (congr_fun h f.1) (bdry f)) τ := by
  classical
  rw [regionBlockedWeight, regionBlockedWeight]
  -- Reindex the constrained virtual-configuration sum by casting every bond.
  let φ : VirtualConfig (reindexTensor (G := G) B h) ≃ VirtualConfig B :=
    Equiv.piCongrRight fun e =>
      finCongr (by simpa [reindexTensor_bondDim] using congr_fun h e)
  refine Finset.sum_nbij' φ φ.symm ?_ ?_ ?_ ?_ ?_
  · -- Forward map lands in the complement filter.
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    funext f
    have hf : regionBoundaryLabel (G := G) (reindexTensor (G := G) B h) R ζ f = bdry f :=
      congrFun hζ f
    rw [regionBoundaryLabel_apply] at hf ⊢
    change Fin.cast (by simpa [reindexTensor_bondDim] using congr_fun h f.1) (ζ f.1) =
      Fin.cast (by simpa [reindexTensor_bondDim] using congr_fun h f.1) (bdry f)
    rw [hf]
  · -- Backward map lands in the original filter.
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    funext f
    have hf : regionBoundaryLabel (G := G) B R ζ f = Fin.cast (congr_fun h f.1) (bdry f) :=
      congrFun hζ f
    rw [regionBoundaryLabel_apply] at hf ⊢
    apply Fin.eq_of_val_eq
    change (((finCongr (by simpa [reindexTensor_bondDim] using congr_fun h f.1)).symm
      (ζ f.1) : Fin ((reindexTensor (G := G) B h).bondDim f.1)) : ℕ) = (bdry f : ℕ)
    rw [finCongr_symm_apply_coe]
    simpa using congrArg Fin.val hf
  · -- Left inverse.
    intro ζ _
    exact φ.left_inv ζ
  · -- Right inverse.
    intro ζ _
    exact φ.right_inv ζ
  · -- Matching summand: products of casts agree.
    intro ζ _
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [reindexTensor_component]
    congr 1

open scoped Classical in
/-- `regionInsertedCoeff` transports along a bond-dimension reindex by conjugating
the inserted matrix with the corresponding reindexing algebra equivalence.

This is the region analogue of `edgeInsertedCoeff_reindexTensor`. -/
theorem regionInsertedCoeff_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (bd f.1)) (Fin (bd f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) (reindexTensor (G := G) B h) R f N σ τ =
      regionInsertedCoeff (G := G) B R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun h f.1)) N) σ τ := by
  classical
  rw [regionInsertedCoeff_eq, regionInsertedCoeff_eq]
  -- Reindex both boundary-configuration sums by casting every bond.
  refine Fintype.sum_equiv
    (Equiv.piCongrRight
      (fun e : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
        finCongr (congr_fun h e.1))) _ _ (fun μ => ?_)
  refine Fintype.sum_equiv
    (Equiv.piCongrRight
      (fun e : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
        finCongr (congr_fun h e.1))) _ _ (fun ν => ?_)
  -- Rewrite the bare equiv-applications `(piCongrRight …) μ`, `(piCongrRight …) ν`
  -- (passed as whole functions) to their pointwise-cast forms; the pointwise simp
  -- lemmas below then clear the residual `μ f`/`ν f` applications.
  have hμeq : (Equiv.piCongrRight
        (fun e : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
          finCongr (congr_fun h e.1))) μ =
      (fun e => Fin.cast (congr_fun h e.1) (μ e)) := by
    funext e; simp only [Equiv.piCongrRight_apply, Pi.map_apply, finCongr_apply]
  have hνeq : (Equiv.piCongrRight
        (fun e : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
          finCongr (congr_fun h e.1))) ν =
      (fun e => Fin.cast (congr_fun h e.1) (ν e)) := by
    funext e; simp only [Equiv.piCongrRight_apply, Pi.map_apply, finCongr_apply]
  rw [hμeq, hνeq]
  -- The `SameAwayFromBond` predicate is preserved by the pointwise reindex.
  have hsame : SameAwayFromBond f
        (fun e => Fin.cast (congr_fun h e.1) (μ e))
        (fun e => Fin.cast (congr_fun h e.1) (ν e)) ↔ SameAwayFromBond f μ ν := by
    constructor
    · intro hμν c hc
      exact Fin.cast_injective _ (hμν c hc)
    · intro hμν c hc
      change Fin.cast (congr_fun h c.1) (μ c) = Fin.cast (congr_fun h c.1) (ν c)
      rw [hμν c hc]
  -- The first region weight reindexes to `B`'s weight at the cast of `μ`.
  rw [regionBlockedWeight_reindexTensor B h R μ σ]
  -- The complement region weight reindexes to `B`'s weight at the cast of `ν`.
  rw [show regionBlockedWeight (G := G) (reindexTensor (G := G) B h) (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) (reindexTensor (G := G) B h) R ν) τ =
      regionBlockedWeight (G := G) B (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) B R
          (fun e => Fin.cast (congr_fun h e.1) (ν e))) τ from ?_]
  · -- The two region weights are now syntactically identical, so it remains to match the
    -- scalar prefactors: the inserted matrix factor reindexes to the conjugated entry of `N`.
    refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) ?_ rfl) rfl
    split_ifs with h₁ h₂ h₂
    · -- Both predicates hold: the conjugated matrix entry equals the original entry.
      rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
      simp
    · exact absurd (hsame.mpr h₁) h₂
    · exact absurd (hsame.mp h₂) h₁
    · rfl
  · rw [regionBlockedWeight_reindexTensor B h (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) (reindexTensor (G := G) B h) R ν) τ]
    congr 1

/-! ### Same region two-block insertions from a coefficient equality

If two tensors share their bond dimensions and have equal region-inserted
coefficients on every boundary edge, then the region/complement two-block
insertions of the two tensors coincide. This is the load-bearing output: it lets
the abstract two-injective comparison consume the region blocks.

This is the region analogue of `sameTwoBlockInsertions_of_edgeInsertedCoeff_eq`. -/

open scoped Classical in
/-- **Same region two-block insertions from a region-insertion equality.** If two
PEPS tensors share their bond dimensions and have equal region-inserted
coefficients on every boundary edge of `R` (after the appropriate reindexed
matrix), then the region/complement two-block insertions of the two tensors
coincide.

This is the abstract reduction from equality of all region-inserted coefficients
to equality of all one-bond insertions for the two-block decomposition of the
region `R` against its complement, after transporting the second tensor to the
first tensor's bond family.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 and 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sameTwoBlockInsertions_of_regionInsertedCoeff_eq (A B : Tensor G d)
    (R : Finset V) (hbd : A.bondDim = B.bondDim)
    (hregion : ∀ (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f N σ τ =
        regionInsertedCoeff (G := G) B R f
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N) σ τ) :
    SameTwoBlockInsertions (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (bondDim := fun f => Fin (A.bondDim f.1))
      (regionTwoBlock (G := G) A R)
      (regionTwoBlock (G := G) (reindexTensor (G := G) B hbd) R)
      (regionComplementTwoBlock (G := G) A R)
      (regionComplementTwoBlock (G := G) (reindexTensor (G := G) B hbd) R) := by
  rintro f M ⟨⟩ ⟨⟩ σ τ
  -- LHS as a region-inserted coefficient of `A`.
  rw [twoBlockInsertedCoeff_eq_regionInsertedCoeff A R f M σ τ]
  -- RHS chain: two-block of the reindexed tensor → its region-inserted coefficient →
  -- the region-inserted coefficient of `B` after reindexing.
  refine Eq.trans (hregion f M σ τ) ?_
  refine Eq.trans
    (regionInsertedCoeff_reindexTensor B hbd R f M σ τ).symm ?_
  exact (twoBlockInsertedCoeff_eq_regionInsertedCoeff (reindexTensor (G := G) B hbd) R f M σ τ).symm

end PEPS
end TNLean
