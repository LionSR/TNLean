import TNLean.PEPS.RegionBlock.Recovery11

/-!
# Region physical-to-virtual recovery: the block-endpoint inversion (region-injective)

This file ports the block-endpoint inversion of the region resonate step to the
**region-injective** regime, with the blocked-region left inverses of `R` and of
its set complement `univ \ R` as the two inversion tools, and *without* assuming
single-vertex injectivity `IsVertexInjective`. It is the region-granularity port
of `resonate_invert_right_endpoint` (`TNLean.PEPS.InsertionRealization`) and the
first half of the open obligation of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

The contributions here are non-circular and use only blocked-region injectivity:

* `regionComplementRow_eq_regionInsertionOp` reads the explicit complement row of a
  second-tensor matrix `N` as the second tensor's own in-region endpoint operator of
  `N.transpose` against the second tensor's region weight vectors at the endpoint
  leg. This is `region_innerSum_eq_realized` (`TNLean.PEPS.RegionBlock.Recovery2`)
  packaged for the complement row of `TNLean.PEPS.RegionBlock.Recovery7`.

* `coeffTransfer_of_endpointOp_eq` reduces the **coefficient transfer** (matching the
  region-inserted coefficients of `A` and `B`) to the agreement of the two in-region
  endpoint operators on the second tensor's region weight vectors at the endpoint
  leg. The reduction inverts the complement block through the blocked-region left
  inverse `regionBlockedLeftInverse B (univ \ R) hCB` and is exactly the
  block-granularity form of inverting the second tensor's complement away from the
  in-region endpoint. It uses no single-vertex spanning.

These are the region-injective replacements for the steps that
`TNLean.PEPS.RegionBlock.Recovery9`/`Recovery10`/`Recovery11` performed with the
single-vertex realization (which needs `IsVertexInjective` through the spanning
`span_stateOpenCoeff_eq_top`).

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

/-! ### The complement row as an in-region endpoint operator

The explicit complement row `regionComplementRow B R f N σ` of the second tensor
(`TNLean.PEPS.RegionBlock.Recovery7`) is, at the complement boundary configuration
`w`, the incident-matrix sum of `N` against the second tensor's region blocked
weights. The inner-sum realization `region_innerSum_eq_realized`
(`TNLean.PEPS.RegionBlock.Recovery2`) reads that sum as the second tensor's *own*
in-region endpoint operator of `N.transpose`, applied to the second tensor's region
weight vector at the reindexed boundary configuration, evaluated at the endpoint
leg. This is the second-tensor counterpart of the v-side row `vSideRow`
(`TNLean.PEPS.RegionBlock.Recovery10`), which reads the *first* tensor's operator on
the same weight vectors; matching the two rows is the coefficient transfer. -/

/-- **The complement row as the second tensor's in-region endpoint operator.** At a
complement boundary configuration `w` of `univ \ R`, the explicit complement row of
the matrix `N` on the second tensor equals the second tensor's in-region endpoint
operator from `N.transpose`, applied to the second tensor's region weight vector at
the reindexed boundary configuration, evaluated at the endpoint physical leg `σ v`.

This is `region_innerSum_eq_realized` (`TNLean.PEPS.RegionBlock.Recovery2`)
specialized to the second tensor with the boundary configuration
`(regionComplementBoundaryConfigEquiv B R).symm w`. It exposes the complement row of
`regionComplementRow` (`TNLean.PEPS.RegionBlock.Recovery7`) in the same form as the
v-side row `vSideRow` (`TNLean.PEPS.RegionBlock.Recovery10`), so the coefficient
transfer becomes the agreement of the two operators on the same weight vectors.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionComplementRow_eq_regionInsertionOp (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (w : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    regionComplementRow (G := G) B R f N σ w =
      regionInsertionOp (G := G) B R f hvB N.transpose
          (regionWeightVec (G := G) B R f
            ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w) σ)
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  classical
  rw [regionComplementRow]
  exact region_innerSum_eq_realized B R f hvB N
    ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w) σ

/-! ### The coefficient transfer from agreement of the two endpoint operators

The v-side factorization `regionInsertedCoeff_eq_complement_blockedMap_vSideRow`
(`TNLean.PEPS.RegionBlock.Recovery10`) writes the first tensor's region-inserted
coefficient of `M`, as a function of the complement physical configuration, as the
second tensor's complement blocked tensor map of the v-side row `vSideRow`. The
B-side factorization `regionInsertedCoeff_eq_complement_blockedMap`
(`TNLean.PEPS.RegionBlock.Recovery7`) does the same for the second tensor's
region-inserted coefficient of `N`, with row the explicit complement row
`regionComplementRow B R f N σ`. Both factor through the *same* injective complement
blocked tensor map (`hCB`), so the coefficient transfer is equivalent to matching
the two rows at every region physical configuration. By
`regionComplementRow_eq_regionInsertionOp` and the definition of `vSideRow`, the two
rows agree exactly when the first tensor's in-region endpoint operator (from
`M.transpose`) and the second tensor's (from `N.transpose`) agree on the second
tensor's region weight vectors at the endpoint leg. This is the block-granularity
inversion of the complement away from the in-region endpoint, the region port of
`resonate_invert_right_endpoint`; it uses no single-vertex spanning. -/

/-- **The coefficient transfer from endpoint-operator agreement.** If the first
tensor's in-region endpoint operator from `M.transpose` and the second tensor's from
`N.transpose` agree, at the endpoint physical leg, on the second tensor's region
weight vectors at every reindexed complement boundary configuration and region
physical configuration, then the region-inserted coefficient of `M` in the first
tensor equals that of `N` in the second at every physical configuration.

The two rows of the (shared) injective complement blocked tensor map are the v-side
row `vSideRow A B R f hvA M σ` (the first tensor's operator on the weight vectors)
and the explicit complement row `regionComplementRow B R f N σ` (read by
`regionComplementRow_eq_regionInsertionOp` as the second tensor's operator on the
same weight vectors). The hypothesis matches them, so `hCB` injectivity forces the
coefficients equal through `regionInsertedCoeff_eq_of_complementRow_eq`
(`TNLean.PEPS.RegionBlock.Recovery10`). The argument is region-injective: it inverts
only the second tensor's complement block, never the single vertex `v`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_endpointOp_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hop : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (ν : RegionBoundaryConfig (G := G) B R),
      regionInsertionOp (G := G) A R f hvA M.transpose
          (regionWeightVec (G := G) B R f ν σ)
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) =
        regionInsertionOp (G := G) B R f hvB N.transpose
          (regionWeightVec (G := G) B R f ν σ)
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  refine regionInsertedCoeff_eq_of_complementRow_eq A B R f hvA hAB hDim M N (fun σ' => ?_) σ τ
  funext w
  rw [vSideRow, regionComplementRow_eq_regionInsertionOp B R f hvB N σ' w]
  exact hop σ' ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w)

/-! ### The symmetric reduction: coefficient transfer through the region block

The σ-side mirror of `regionInsertedCoeff_eq_of_complementRow_eq`
(`TNLean.PEPS.RegionBlock.Recovery10`). Fixing the complement physical
configuration `τ`, the first tensor's region-inserted coefficient of `M` factors, as
a function of the region physical configuration `σ`, through the second tensor's
region blocked tensor map with row `complSideRow A B R f hvAout M τ`
(`regionInsertedCoeff_eq_region_blockedMap_B`, `Recovery10`); the second tensor's
region-inserted coefficient of `N` factors through the *same* map with the explicit
region row `regionRegionRow B R f N τ` (`regionInsertedCoeff_eq_region_blockedMap`,
`Recovery7`). Region-block injectivity (`hRB`) forces the coefficients equal when the
two rows agree. This is the σ-side inversion, the region port of
`resonate_invert_left_endpoint`. -/

/-- **Coefficient transfer through the region block.** If the σ-side row
`complSideRow A B R f hvAout M τ` of the first tensor agrees with the explicit region
row `regionRegionRow B R f N τ` of the second tensor at every complement physical
configuration `τ`, then the region-inserted coefficient of `M` in the first tensor
equals that of `N` in the second at every physical configuration.

Both rows are rows of the same injective region blocked tensor map of `B` (`hRB`):
the first tensor's coefficient is its map of `complSideRow` by
`regionInsertedCoeff_eq_region_blockedMap_B` (`Recovery10`), the second tensor's of
`regionRegionRow` by `regionInsertedCoeff_eq_region_blockedMap` (`Recovery7`). This
is the σ-side mirror of `regionInsertedCoeff_eq_of_complementRow_eq`; it inverts only
the second tensor's region block.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_regionRow_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hrow : ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
      complSideRow (G := G) A B R f hvAout M τ = regionRegionRow (G := G) B R f N τ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  have hA := congrFun
    (regionInsertedCoeff_eq_region_blockedMap_B A B R f hvAout hAB hDim M τ) σ
  rw [hA, hrow τ, ← regionInsertedCoeff_eq_region_blockedMap B R f N σ τ]

/-! ### The region insertion transfer datum from a region-injective coefficient transfer

The block-level injectivity `regionInsertedCoeff_injective`
(`TNLean.PEPS.RegionBlock.Algebra`) is unconditional on blocked-region injectivity.
It lets the per-edge matrix transfer maps be chosen directly from a coefficient
transfer — for each inserted matrix a matching matrix on the other tensor — with the
coefficient-matching fields holding by the choice and the unital field by the
`SameState` identity insertion `regionInsertedCoeff_one_eq_stateCoeff`
(`TNLean.PEPS.RegionBlock.Recovery`). The only remaining input is multiplicativity of
the chosen forward transfer, which the source supplies by the homomorphism property
of the physical realization. Isolating it as a hypothesis assembles the
`RegionInsertionTransfer` datum region-injectively: feeding it to
`exists_regionEdgeGauge_of_transfer` (`TNLean.PEPS.RegionBlock.Algebra`) reads off the
per-edge gauge with no single-vertex injectivity. -/

/-- A chosen forward per-edge matrix transfer from a coefficient transfer: for each
inserted matrix `M` on the first tensor, a matrix on the second tensor whose
region-inserted coefficient matches. The matching is the defining property
`coeffTransferMap_coeff`. -/
noncomputable def coeffTransferMap (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (htransfer : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  (htransfer M).choose

/-- The chosen forward transfer matches the region-inserted coefficients. -/
theorem coeffTransferMap_coeff (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (htransfer : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f (coeffTransferMap (G := G) A B R f htransfer M) σ τ :=
  (htransfer M).choose_spec σ τ

/-- The chosen forward transfer is unital, by the `SameState` identity insertion. The
region-inserted coefficient of the identity is the interior bond product times the
closed-state coefficient (`regionInsertedCoeff_one_eq_stateCoeff`), matched across the
two tensors by `SameState` and equal bond dimensions. Block injectivity of the second
tensor then forces the chosen transfer of `1` to be `1`. -/
theorem coeffTransferMap_one (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (htransfer : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ) :
    coeffTransferMap (G := G) A B R f htransfer 1 = 1 := by
  refine regionInsertedCoeff_injective (G := G) B R hRB hCB hposB f _ 1 (fun σ τ => ?_)
  rw [← coeffTransferMap_coeff A B R f htransfer 1 σ τ,
    regionInsertedCoeff_one_eq_stateCoeff (G := G) A R f σ τ,
    regionInsertedCoeff_one_eq_stateCoeff (G := G) B R f σ τ,
    regionInteriorBondProd_congr A B R hDim, hAB _]

/-- **Region insertion transfer datum from a region-injective coefficient transfer.**
Given coefficient transfers in both directions (for each inserted matrix on one
tensor a matching matrix on the other), matched bond dimensions, `SameState`,
positive bond dimensions, region/complement blocked injectivity of both tensors, and
multiplicativity of the chosen forward transfer, the per-edge matrix transfer maps
assemble into a `RegionInsertionTransfer` datum.

The forward and backward maps are chosen by `coeffTransferMap`; their
coefficient-matching fields are `coeffTransferMap_coeff`; the unital field is
`coeffTransferMap_one`; the multiplicative field is the hypothesis `hmul`. All other
content is `regionInsertedCoeff_injective`, which is unconditional on blocked-region
injectivity. The datum feeds `exists_regionEdgeGauge_of_transfer`
(`TNLean.PEPS.RegionBlock.Algebra`) to read off the per-edge gauge with no
single-vertex injectivity.

**Scope (multiplicativity hypothesis):** the forward-transfer multiplicativity `hmul`
is the only field not yet derived region-injectively. The source derives it from the
homomorphism property of the physical realization
(`Papers/1804.04964/paper_normal.tex`, eq. `X->O`), whose region port reads the
recovered matrix off the single-vertex virtual pullback and so currently needs the
in-region endpoint spanning. The block-endpoint inversions above
(`coeffTransfer_of_endpointOp_eq`, `regionInsertedCoeff_eq_of_regionRow_eq`) supply
the coefficient transfers `htransferAB`/`htransferBA`; the residual single-vertex
read-off is documented in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionInsertionTransfer_of_coeffTransfer (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ)
    (htransferBA : ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      ∃ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) B R f N σ τ =
            regionInsertedCoeff (G := G) A R f M σ τ)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      coeffTransferMap (G := G) A B R f htransferAB (M * M') =
        coeffTransferMap (G := G) A B R f htransferAB M *
          coeffTransferMap (G := G) A B R f htransferAB M') :
    RegionInsertionTransfer (G := G) A B R f where
  fwd M := coeffTransferMap (G := G) A B R f htransferAB M
  bwd N := coeffTransferMap (G := G) B A R f htransferBA N
  fwd_coeff M σ τ := coeffTransferMap_coeff A B R f htransferAB M σ τ
  bwd_coeff N σ τ := coeffTransferMap_coeff B A R f htransferBA N σ τ
  fwd_mul M M' := hmul M M'
  fwd_one := coeffTransferMap_one A B R f hRB hCB hAB hposB hDim htransferAB

/-- **Per-edge gauge from a region-injective coefficient transfer.** Given coefficient
transfers in both directions with a multiplicative forward choice, region/complement
blocked injectivity of both tensors, positive bond dimensions, `SameState`, and
matched bond dimensions, the chosen forward per-edge matrix transfer on the boundary
edge `f` is conjugation by an invertible gauge matrix `Z`, and the two bond
dimensions on `f` coincide. No single-vertex injectivity is used: the datum is
`regionInsertionTransfer_of_coeffTransfer` and the read-off is
`exists_regionEdgeGauge_of_transfer` (`TNLean.PEPS.RegionBlock.Algebra`).

**Scope (multiplicativity hypothesis):** see
`regionInsertionTransfer_of_coeffTransfer`.

Source: arXiv:1804.04964, Section 3, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_coeffTransfer (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ)
    (htransferBA : ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      ∃ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) B R f N σ τ =
            regionInsertedCoeff (G := G) A R f M σ τ)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      coeffTransferMap (G := G) A B R f htransferAB (M * M') =
        coeffTransferMap (G := G) A B R f htransferAB M *
          coeffTransferMap (G := G) A B R f htransferAB M') :
    ∃ hEdge : A.bondDim f.1 = B.bondDim f.1,
      ∃ Z : GL (Fin (B.bondDim f.1)) ℂ,
        ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          (regionInsertionTransfer_of_coeffTransfer A B R f hRB hCB hAB hposB hDim
              htransferAB htransferBA hmul).fwd M =
            (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
                Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  exists_regionEdgeGauge_of_transfer A B R f
    (regionInsertionTransfer_of_coeffTransfer A B R f hRB hCB hAB hposB hDim
      htransferAB htransferBA hmul)
    hRA hCA hposA hRB hCB hposB

end PEPS
end TNLean
