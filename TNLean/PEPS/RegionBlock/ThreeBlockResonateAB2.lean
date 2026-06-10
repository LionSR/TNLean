import TNLean.PEPS.RegionBlock.ThreeBlockResonateAB

/-!
# The host↔blue collapse of the cross-tensor three-block resonate identity

This file continues `TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`, building the
**host↔blue collapse** of the cross-tensor resonate identity for the general normal
PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3, Lemma
`inj_isomorph`, the step `V=W`).

The landed cross-tensor resonate identity `threeBlockOpCoeff_resonate_AB`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) reads the first tensor's
region-inserted coefficient of `M` through the **second** tensor's `SameState`-invariant
partial states two ways:

* the **red-side** realization, the first tensor's red-block realization operator
  `blockRealizeOp A red hRA f M` on the second tensor's red partial state;
* the **host-side** realization, the first tensor's host-block realization operator
  `blockRealizeOp A (univ \ red) hCA (toCompl f) Mᵀ` on the second tensor's host partial
  state.

The decisive geometric fact is that the host block `univ \ red` is the disjoint union of
the blue and complement blocks (`sdiff_red_eq_blue_union_complement`), and the red and
blue blocks cross at exactly the distinguished edge `e`. So the host-side reading,
written through the blue/complement split, carries the bond-paired structure on `e`
inside the blue block. The complement block is the separately invertible middle; the
landed single-tensor engine (`threeBlock_invert_blue`, `threeBlock_middle_strip`) strips
it, leaving a **blue-block reading**.

This file works entirely in **physical-configuration space** — the host complement leg
`τ` of `univ \ red` is read as the fused blue/complement leg
`threeBlockComplPhysical DB σblue σcompl` — to avoid the dependent-type casts of the
boundary-configuration spaces of the two tensors.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, the step `V=W`, lines 355--486 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The cross-tensor resonate identity in the three-block frame

Reading the host complement leg `τ` of `univ \ red` through the blue/complement split
`threeBlockComplPhysical DB σblue σcompl` puts the cross-tensor resonate identity
`threeBlockOpCoeff_resonate_AB` (`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) into the
frame the single-tensor three-block engine on the second tensor consumes: the host leg is
quantified as the two separate legs `σblue`, `σcompl`. This is the substitution
`τ := threeBlockComplPhysical DB σblue σcompl`, with the second tensor's one-edge
blocking datum `DB` supplying the blue/complement fusing. -/

/-- **The cross-tensor resonate identity in the three-block frame.** Substituting the
fused blue/complement leg of the second tensor's one-edge blocking datum `DB` for the host
complement leg, the cross-tensor resonate identity reads the first tensor's
region-inserted coefficient of `M` two ways at a fixed red physical leg `σ` and split
blue/complement legs `σblue`, `σcompl`: the first tensor's red-block realization operator
on the second tensor's red partial state, and the first tensor's host-block realization
operator of `Mᵀ` on the second tensor's host partial state at the fused leg.

This is `threeBlockOpCoeff_resonate_AB`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) evaluated at
`τ := threeBlockComplPhysical DB σblue σcompl`, with `R := DB.red` the second tensor's red
region. It puts the cross-tensor identity into the three-block frame, with the host leg
read as the two separate legs the single-tensor engine on the second tensor inverts.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_resonate_AB_split (A B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hRA : RegionBlockedTensorInjective (G := G) A DB.red)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ DB.red))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    blockRealizeOp (G := G) A DB.red hRA f M
        ((regionInteriorBondProd (G := G) B DB.red : ℂ) •
          regionPartialState (G := G) B DB.red
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)) σ =
      blockRealizeOp (G := G) A (Finset.univ \ DB.red) hCA
        (regionBoundaryEdgeToCompl (G := G) DB.red f) M.transpose
        ((regionInteriorBondProd (G := G) B (Finset.univ \ DB.red) : ℂ) •
          regionPartialState (G := G) B (Finset.univ \ DB.red)
            (regionDoubleComplPhysicalConfig (V := V) (d := d) DB.red σ))
        (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) := by
  have h := threeBlockOpCoeff_resonate_AB A B DB.red hRA hCA hAB hDim f M σ
  exact congrFun h (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)

/-! ### The double factorization of the first tensor's coefficient with the host weight
split along blue and complement

The block-frame double factorization
`regionInsertedCoeff_eq_doubleSum_transferCoeff_block`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) writes the first tensor's region-inserted
coefficient of `M` as a boundary-configuration double sum of the transfer kernel
`transferCoeff A B red f M` against the second tensor's host and red blocked weights.
Reading the host complement leg through the blue/complement split
`threeBlockComplPhysical DB σblue σcompl` and unfolding each host blocked weight along
`univ \ red = blue ⊔ complement` (`regionBlockedWeight_threeBlockComplPhysical_eq`,
`TNLean.PEPS.RegionBlock.ThreeBlockResonate`) exposes the second tensor's blue/complement
structure inside the first tensor's coefficient. This is the host-side expansion the blue
read-off `threeBlock_invert_blue` (`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`) acts on,
in physical-configuration space. -/

open scoped Classical in
/-- **The first tensor's coefficient with the host weight split along blue and
complement.** Reading the host complement leg of the second tensor's red region through
the blue/complement split, the first tensor's region-inserted coefficient of `M` is the
host-residual double sum of the transfer kernel `transferCoeff A B red f M` against the
second tensor's red blocked weight and the second tensor's host blocked weight, the latter
expanded as the constrained global-configuration sum of the blue vertex product (read with
`σblue`) times the complement vertex product (read with `σcompl`).

This is the block-frame double factorization
`regionInsertedCoeff_eq_doubleSum_transferCoeff_block`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) at the fused leg, with each host blocked
weight unfolded along `univ \ red = blue ⊔ complement`
(`regionBlockedWeight_threeBlockComplPhysical_eq`,
`TNLean.PEPS.RegionBlock.ThreeBlockResonate`). It exposes the second tensor's
blue/complement structure inside the first tensor's coefficient.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_doubleSum_transferCoeff_blue_complement_split
    (A B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hRA : RegionBlockedTensorInjective (G := G) A DB.red)
    (hRB : RegionBlockedTensorInjective (G := G) B DB.red)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ DB.red))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ DB.red))
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    regionInsertedCoeff (G := G) A DB.red f M σ
        (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) =
      ∑ μ : RegionBoundaryConfig (G := G) B DB.red,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ DB.red),
          transferCoeff (G := G) A B DB.red hRB hCB f M μ ν' *
            (∑ ζ ∈ Finset.univ.filter
                (fun ζ : VirtualConfig B =>
                  regionBoundaryLabel (G := G) B (Finset.univ \ DB.red) ζ = ν'),
              (∏ w : {w : V // w ∈ DB.blue},
                  B.component w.1 (fun ie => ζ ie.1) (σblue w)) *
                ∏ w : {w : V // w ∈ DB.complement},
                  B.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
            regionBlockedWeight (G := G) B DB.red μ σ := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum_transferCoeff_block A B DB.red hRA hRB hCA hCB hAB
    hposA hposB hDim f M σ (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  refine Finset.sum_congr rfl (fun ν' _ => ?_)
  rw [regionBlockedWeight_threeBlockComplPhysical_eq (A := B) (e := e) DB ν' σblue σcompl]

/-! ### The host↔blue collapse of the first tensor's coefficient

Scaling the first tensor's coefficient by the second tensor's blue interior bond product
and applying the blue-block decoupling
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`) to each host blocked weight at the fused
leg replaces the host weight by the second tensor's blue blocked weight coupled through the
**M-free** complement coupling row `threeBlockComplCoeff B`. This is the host↔blue collapse
in physical-configuration space: the host reading of the first tensor's coefficient becomes
a blue reading, with the residual complement structure carried by the M-free coupling row
the blue read-off `threeBlock_invert_blue` (`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`)
inverts. The red↔blue crossing at the distinguished edge `e` survives because the blue
blocked weight `regionBlockedWeight B blue bβ σblue` is bond-paired on the blue boundary,
of which `e` is the distinguished crossing. -/

open scoped Classical in
/-- **The host↔blue collapse of the first tensor's coefficient.** The second tensor's blue
interior bond multiple of the first tensor's region-inserted coefficient of `M`, read at
the fused blue/complement leg of the second tensor's red region, is the host-residual
double sum of the transfer kernel `transferCoeff A B red f M` against the second tensor's
red blocked weight and the **blue**-coupled host structure: each host blocked weight is
replaced by the sum over blue boundary configurations `bβ` of the M-free complement
coupling row `threeBlockComplCoeff B ν' σcompl bβ` against the second tensor's blue blocked
weight `regionBlockedWeight B blue bβ σblue`.

This is `regionInsertedCoeff_eq_doubleSum_transferCoeff_blue_complement_split` after
multiplying by the second tensor's blue interior bond product and applying the blue-block
decoupling `regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`) to each host blocked weight. The host
reading of the first tensor's coefficient is collapsed to a blue reading; the residual
complement structure is the M-free coupling row the blue read-off
`threeBlock_invert_blue` inverts.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse
    (A B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hRA : RegionBlockedTensorInjective (G := G) A DB.red)
    (hRB : RegionBlockedTensorInjective (G := G) B DB.red)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ DB.red))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ DB.red))
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    (regionInteriorBondProd (G := G) B DB.blue : ℂ) •
        regionInsertedCoeff (G := G) A DB.red f M σ
          (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) =
      ∑ μ : RegionBoundaryConfig (G := G) B DB.red,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ DB.red),
          transferCoeff (G := G) A B DB.red hRB hCB f M μ ν' *
            (∑ bβ : RegionBoundaryConfig (G := G) B DB.blue,
              threeBlockComplCoeff (A := B) (e := e) DB ν' σcompl bβ *
                regionBlockedWeight (G := G) B DB.blue bβ σblue) *
            regionBlockedWeight (G := G) B DB.red μ σ := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum_transferCoeff_block A B DB.red hRA hRB hCA hCB hAB
    hposA hposB hDim f M σ (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun ν' _ => ?_)
  -- Scale the host blocked weight at the fused leg by the blue interior bond product and
  -- decouple it into the blue-coupled complement-coupling combination.
  have hblue := congrFun
    (regionInteriorBondProd_smul_threeBlockBlueWeight_eq (A := B) (e := e) DB ν' σcompl) σblue
  rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hblue
  simp only [Pi.smul_apply, smul_eq_mul] at hblue
  -- `hblue : interior_blue * host_weight ν' (fused) = ∑ bβ, threeBlockComplCoeff · blueWeight`.
  rw [smul_eq_mul, show (regionInteriorBondProd (G := G) B DB.blue : ℂ) *
        (transferCoeff (G := G) A B DB.red hRB hCB f M μ ν' *
          regionBlockedWeight (G := G) B (Finset.univ \ DB.red) ν'
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) *
          regionBlockedWeight (G := G) B DB.red μ σ) =
      transferCoeff (G := G) A B DB.red hRB hCB f M μ ν' *
        ((regionInteriorBondProd (G := G) B DB.blue : ℂ) *
          regionBlockedWeight (G := G) B (Finset.univ \ DB.red) ν'
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)) *
        regionBlockedWeight (G := G) B DB.red μ σ from by ring]
  rw [hblue]

/-! ### The host realization operator collapses to the blue-coupled structure

Combining the cross-tensor resonate identity in the three-block frame
`threeBlockOpCoeff_resonate_AB_split` with the host↔blue collapse
`regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse` reads the
**host-side** realization operator of `A1` — the first tensor's host-block realization
operator of `Mᵀ` on the second tensor's host partial state — directly as the blue-coupled
structure. This is the host↔blue collapse stated on the resonate identity itself: the host
reading of the first tensor's coefficient is the blue reading, with the residual complement
structure carried by the M-free coupling row. -/

open scoped Classical in
/-- **The host realization operator collapses to the blue-coupled structure.** The second
tensor's blue interior bond multiple of the host-side realization operator of the
cross-tensor resonate identity — the first tensor's host-block realization operator of
`Mᵀ` on the second tensor's host partial state, read at the fused blue/complement leg — is
the host-residual double sum of the transfer kernel `transferCoeff A B red f M` against the
second tensor's red blocked weight and the blue-coupled host structure (each host weight
replaced by the blue blocked weight coupled through the M-free complement coupling row
`threeBlockComplCoeff B`).

This composes `threeBlockOpCoeff_resonate_AB_split` (which equates the host-side
realization with the first tensor's coefficient at the fused leg) with the host↔blue
collapse `regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse`. It states
the collapse on the resonate identity's host side itself: what survives of the host reading
is a blue-block reading.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_blue_smul_hostRealizeOp_eq_blueCollapse
    (A B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hRA : RegionBlockedTensorInjective (G := G) A DB.red)
    (hRB : RegionBlockedTensorInjective (G := G) B DB.red)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ DB.red))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ DB.red))
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    (regionInteriorBondProd (G := G) B DB.blue : ℂ) •
        blockRealizeOp (G := G) A (Finset.univ \ DB.red) hCA
          (regionBoundaryEdgeToCompl (G := G) DB.red f) M.transpose
          ((regionInteriorBondProd (G := G) B (Finset.univ \ DB.red) : ℂ) •
            regionPartialState (G := G) B (Finset.univ \ DB.red)
              (regionDoubleComplPhysicalConfig (V := V) (d := d) DB.red σ))
          (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) =
      ∑ μ : RegionBoundaryConfig (G := G) B DB.red,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ DB.red),
          transferCoeff (G := G) A B DB.red hRB hCB f M μ ν' *
            (∑ bβ : RegionBoundaryConfig (G := G) B DB.blue,
              threeBlockComplCoeff (A := B) (e := e) DB ν' σcompl bβ *
                regionBlockedWeight (G := G) B DB.blue bβ σblue) *
            regionBlockedWeight (G := G) B DB.red μ σ := by
  classical
  -- The host-side realization equals the first tensor's coefficient at the fused leg.
  have hhost := (threeBlockOpCoeff_resonate_AB_split A B DB hRA hCA hAB hDim f M σ σblue
    σcompl).symm
  -- The red-side realization is the first tensor's coefficient.
  have hred : blockRealizeOp (G := G) A DB.red hRA f M
        ((regionInteriorBondProd (G := G) B DB.red : ℂ) •
          regionPartialState (G := G) B DB.red
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)) σ =
      regionInsertedCoeff (G := G) A DB.red f M σ
        (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) := by
    have h := regionInsertedCoeff_eq_blockRealizeOp_regionPartialState_B A B DB.red hRA hAB hDim
      f M (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)
    exact (congrFun h σ).symm
  rw [hhost, hred,
    regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse A B DB hRA hRB hCA hCB
      hAB hposA hposB hDim f M σ σblue σcompl]

end PEPS
end TNLean
