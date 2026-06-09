import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
import TNLean.PEPS.RegionBlock.RegionReconcile

/-!
# Block-frame coefficient transfer for the normal PEPS Fundamental Theorem

This file builds the **block-frame coefficient transfer** for region-injective
tensors: from two tensors `A`, `B` generating the same state, with both the
region block `R` and its complement `univ \ R` blocked-tensor injective and
positive bond dimensions, the region-inserted coefficient of any matrix `M` on a
boundary edge `f` of `R` in the first tensor is realized by a matrix `N` on the
second tensor:

> `∀ M, ∃ N, ∀ σ τ, regionInsertedCoeff A R f M σ τ = regionInsertedCoeff B R f N σ τ`.

The construction uses only the **block-level image coincidence**
`range_regionBlockedTensorMap_eq_of_sameState`
(`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`), never single-vertex
injectivity. The single-vertex frame (which pins the recovered matrix off the
in-region endpoint's virtual pullback) needs the vertex component to be linearly
independent, which a single vertex of a normal tensor need not satisfy. The block
frame inverts the whole region block and its complement instead, which are
injective by hypothesis.

## The route

For a fixed inserted matrix `M`, the region-inserted coefficient as a function of
the region physical configuration `σ` factors through the region blocked tensor
map (`regionInsertedCoeff_eq_region_blockedMap`). The block-level image
coincidence puts it in the range of the second tensor's region blocked tensor
map, so the chosen region left inverse of the second tensor reads off a
boundary-configuration coefficient row, `rowB`, with

> `regionInsertedCoeff A R f M σ τ = regionBlockedTensorMap B R (rowB τ) σ`.

Symmetrically in `τ`: each coefficient `rowB τ μ`, as a function of the complement
physical configuration `τ`, factors through the second tensor's *complement*
blocked tensor map (block-level image coincidence with the roles of `R` and
`univ \ R` exchanged, using `univ \ (univ \ R) = R`), so the chosen complement
left inverse reads off a complement-boundary-configuration coefficient kernel
`K`, with

> `rowB τ μ = regionBlockedTensorMap B (univ \ R) (fun ν => K μ ν) τ`.

Combining the two readings expresses the coefficient as a double sum over the
second tensor's region and complement weights with the **single kernel** `K`,
which by the second tensor's double blocked injectivity is unique. Matching `K`
against the explicit incident-matrix form of `regionInsertedCoeff B R f N`
produces the transferred matrix `N`.

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

/-! ### The region-side blocked reading of the inserted coefficient

For a fixed inserted matrix `M`, the region-inserted coefficient of the first
tensor, as a function of the region physical configuration `σ`, lies in the range
of the *second* tensor's region blocked tensor map. The block-level image
coincidence `range_regionBlockedTensorMap_eq_of_sameState` transports the
first-tensor factoring `regionInsertedCoeff_eq_region_blockedMap` into the second
tensor's range, so the second tensor's region left inverse reads off a
boundary-configuration row. -/

/-- The region-side transferred row: the second tensor's region left inverse
applied to the first tensor's region-inserted coefficient viewed as a function of
the region physical configuration `σ`, at a fixed complement physical
configuration `τ`. By the block-level image coincidence this row reproduces the
coefficient through the second tensor's region blocked tensor map. -/
noncomputable def blockTransferRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) B R → ℂ :=
  regionBlockedLeftInverse (G := G) B R hRB
    (fun σ => regionInsertedCoeff (G := G) A R f M σ τ)

/-- **The region-side blocked reading.** Under `SameState`, with both complement
blocks blocked-tensor injective and positive bond dimensions, the first tensor's
region-inserted coefficient is the second tensor's region blocked tensor map of
the transferred row `blockTransferRow`. The block-level image coincidence
`range_regionBlockedTensorMap_eq_of_sameState` puts the coefficient (a function of
`σ`) in the range of the second tensor's region blocked tensor map, and the chosen
left inverse `regionBlockedLeftInverse B R hRB` realizes it as that map's image.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_blockTransferRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionBlockedTensorMap (G := G) B R (blockTransferRow A B R hRB f M τ) σ := by
  -- The coefficient as a function of `σ` factors through the first tensor's
  -- region blocked tensor map, hence lies in its range.
  have hmemA : (fun σ' => regionInsertedCoeff (G := G) A R f M σ' τ) ∈
      LinearMap.range (regionBlockedTensorMap (G := G) A R) := by
    rw [LinearMap.mem_range]
    exact ⟨regionRegionRow (G := G) A R f M τ,
      (funext (fun σ' =>
        (regionInsertedCoeff_eq_region_blockedMap A R f M σ' τ).symm))⟩
  -- The block-level image coincidence transports it into the second tensor's range.
  rw [range_regionBlockedTensorMap_eq_of_sameState A B R hAB hCA hCB hposA hposB hDim]
    at hmemA
  rw [LinearMap.mem_range] at hmemA
  obtain ⟨c, hc⟩ := hmemA
  -- The chosen region left inverse of the second tensor reads off `c`, which is the
  -- transferred row, and applying the second tensor's map back reproduces the
  -- coefficient.
  have hrow : blockTransferRow A B R hRB f M τ = c := by
    rw [blockTransferRow, ← hc, regionBlockedLeftInverse_apply_regionBlockedTensorMap]
  rw [hrow, hc]

/-! ### The double-complement transport of blocked-tensor injectivity

The blocked-region weight is double-complement invariant
(`regionBlockedWeight_doubleCompl`), so the blocked tensor family of
`univ \ (univ \ R)` is, up to the double-complement boundary-configuration
reindexing and the double-complement physical-configuration reindexing, the
blocked tensor family of `R`. Reindexing by an equivalence and precomposing with a
bijective change of the physical-configuration index both preserve linear
independence, so blocked-tensor injectivity transports from `R` to
`univ \ (univ \ R)`. This supplies the complement-block injectivity hypothesis the
block-level image coincidence needs when applied to the region `univ \ R`. -/

/-- The double-complement physical-configuration transport as an equivalence: a
region physical configuration on `R` corresponds to one on `univ \ (univ \ R)` by
reading each vertex under the double-complement vertex equivalence. -/
def regionDoubleComplPhysicalConfigEquiv (R : Finset V) :
    RegionPhysicalConfig (V := V) (d := d) R ≃
      RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ (Finset.univ \ R)) where
  toFun := regionDoubleComplPhysicalConfig (V := V) (d := d) R
  invFun σ := fun w => σ ((regionDoubleComplVertexEquiv (V := V) R).symm w)
  left_inv σ := by
    funext w
    simp only [regionDoubleComplPhysicalConfig, Equiv.apply_symm_apply]
  right_inv σ := by
    funext w
    simp only [regionDoubleComplPhysicalConfig, Equiv.symm_apply_apply]

/-- **Double-complement transport of blocked-tensor injectivity.** If the region
`R` is blocked-tensor injective, then so is `univ \ (univ \ R)`. The blocked tensor
family of `univ \ (univ \ R)`, reindexed by the double-complement
boundary-configuration equivalence and precomposed with the double-complement
physical-configuration equivalence, is the blocked tensor family of `R`
(`regionBlockedWeight_doubleCompl`); both reindexings preserve linear independence. -/
theorem regionBlockedTensorInjective_doubleCompl (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ (Finset.univ \ R)) := by
  -- The blocked family of `R` is the double-complement family reindexed by `Ψ` and
  -- precomposed with the physical-config equivalence `Φ`.
  set Ψ := regionDoubleComplBoundaryConfigEquiv (G := G) A R with hΨ
  set Φ := regionDoubleComplPhysicalConfigEquiv (V := V) (d := d) R with hΦ
  have hfam : (LinearEquiv.funCongrLeft ℂ ℂ Φ) ∘
        (regionBlockedTensorFamily (G := G) A (Finset.univ \ (Finset.univ \ R)) ∘ Ψ) =
      regionBlockedTensorFamily (G := G) A R := by
    funext bdry
    funext σ
    rw [Function.comp_apply, Function.comp_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply]
    -- `Ψ bdry = regionDoubleComplBoundaryConfig bdry`, `Φ σ = regionDoubleComplPhysicalConfig σ`.
    show regionBlockedTensorFamily (G := G) A (Finset.univ \ (Finset.univ \ R))
        (regionDoubleComplBoundaryConfig (G := G) A R bdry)
        (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ) =
      regionBlockedTensorFamily (G := G) A R bdry σ
    rw [regionBlockedTensorFamily, regionBlockedTensorFamily,
      regionBlockedWeight_doubleCompl A R bdry σ]
  -- `hR` gives linear independence of `regionBlockedTensorFamily A R`; transport back.
  have hRfam : LinearIndependent ℂ
      ((LinearEquiv.funCongrLeft ℂ ℂ Φ) ∘
        (regionBlockedTensorFamily (G := G) A (Finset.univ \ (Finset.univ \ R)) ∘ Ψ)) := by
    rw [hfam]; exact hR
  -- Strip the linear iso, then the index equivalence.
  have hΨfam : LinearIndependent ℂ
      (regionBlockedTensorFamily (G := G) A (Finset.univ \ (Finset.univ \ R)) ∘ Ψ) :=
    LinearIndependent.of_comp _ hRfam
  exact (linearIndependent_equiv Ψ).mp hΨfam

/-! ### Complement-block image coincidence

The block-level image coincidence applied to the region `univ \ R`: its complement
is `univ \ (univ \ R)`, which is blocked-tensor injective by the double-complement
transport above. So the ranges of the two complement blocked tensor maps coincide
under `SameState`. This is the complement-side companion of
`range_regionBlockedTensorMap_eq_of_sameState`, used to read off the transfer
kernel through the second tensor's complement block. -/

/-- **Complement-block image coincidence.** Under `SameState`, with both region
blocks `R` blocked-tensor injective and positive bond dimensions, the ranges of the
complement blocked tensor maps of `univ \ R` coincide. This is
`range_regionBlockedTensorMap_eq_of_sameState` applied to the region `univ \ R`,
whose complement-block injectivity is supplied by
`regionBlockedTensorInjective_doubleCompl`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem range_regionBlockedTensorMap_compl_eq_of_sameState (A B : Tensor G d) (R : Finset V)
    (hAB : SameState A B)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim) :
    LinearMap.range (regionBlockedTensorMap (G := G) A (Finset.univ \ R)) =
      LinearMap.range (regionBlockedTensorMap (G := G) B (Finset.univ \ R)) :=
  range_regionBlockedTensorMap_eq_of_sameState A B (Finset.univ \ R) hAB
    (regionBlockedTensorInjective_doubleCompl A R hRA)
    (regionBlockedTensorInjective_doubleCompl B R hRB) hposA hposB hDim

end PEPS
end TNLean
