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

/-! ### The second tensor's coefficient of a witness through the blue collapse

The second tensor's own region-inserted coefficient of a witness matrix `N` collapses the
same way: its double-sum reading through the incident-matrix kernel
(`doubleSum_incidentKernel_eq_regionInsertedCoeff`,
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) has each host blocked weight at the fused leg
replaced by the same blue-coupled host structure. So the witness condition
`coeff_A M = coeff_B N` reads, after the blue collapse, as the two kernels —
`transferCoeff A B red f M` and `incidentKernel B red f N` — paired against the **same**
M-free blue/complement structure of the second tensor. This is the kernel-matching frame
the witness extraction lands in. -/

open scoped Classical in
/-- **The second tensor's coefficient of a witness through the blue collapse.** The second
tensor's blue interior bond multiple of its own region-inserted coefficient of `N`, read at
the fused blue/complement leg, is the host-residual double sum of the incident-matrix kernel
`incidentKernel B red f N` against the second tensor's red blocked weight and the
blue-coupled host structure (the same blue/complement structure that appears in the first
tensor's collapse `regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse`).

This is `doubleSum_incidentKernel_eq_regionInsertedCoeff`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) at the fused leg, scaled by the blue interior
bond product and with each host blocked weight decoupled along the blue/complement split.
Comparing it with the first tensor's collapse presents the witness condition
`coeff_A M = coeff_B N` as the kernel pairing `transferCoeff A B red f M` versus
`incidentKernel B red f N` against the same M-free structure.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_blue_smul_regionInsertedCoeff_B_eq_blueCollapse
    (B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    (regionInteriorBondProd (G := G) B DB.blue : ℂ) •
        regionInsertedCoeff (G := G) B DB.red f N σ
          (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) =
      ∑ μ : RegionBoundaryConfig (G := G) B DB.red,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ DB.red),
          incidentKernel (G := G) B DB.red f N μ ν' *
            (∑ bβ : RegionBoundaryConfig (G := G) B DB.blue,
              threeBlockComplCoeff (A := B) (e := e) DB ν' σcompl bβ *
                regionBlockedWeight (G := G) B DB.blue bβ σblue) *
            regionBlockedWeight (G := G) B DB.red μ σ := by
  classical
  rw [← doubleSum_incidentKernel_eq_regionInsertedCoeff B DB.red f N σ
    (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)]
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
  rw [smul_eq_mul, show (regionInteriorBondProd (G := G) B DB.blue : ℂ) *
        (incidentKernel (G := G) B DB.red f N μ ν' *
          regionBlockedWeight (G := G) B (Finset.univ \ DB.red) ν'
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) *
          regionBlockedWeight (G := G) B DB.red μ σ) =
      incidentKernel (G := G) B DB.red f N μ ν' *
        ((regionInteriorBondProd (G := G) B DB.blue : ℂ) *
          regionBlockedWeight (G := G) B (Finset.univ \ DB.red) ν'
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)) *
        regionBlockedWeight (G := G) B DB.red μ σ from by ring]
  rw [hblue]

/-! ### The witness condition through the blue collapse

Comparing the two blue collapses
(`regionInteriorBondProd_blue_smul_regionInsertedCoeff_eq_blueCollapse` and
`regionInteriorBondProd_blue_smul_regionInsertedCoeff_B_eq_blueCollapse`), the witness
condition `coeff_A M = coeff_B N` at the fused leg is the pairing of the two kernels —
`transferCoeff A B red f M` and `incidentKernel B red f N` — against the **same** M-free
blue/complement structure of the second tensor. Since the second tensor's blue interior
bond product is a nonzero scalar (positive bond dimensions), the witness condition at the
fused leg is exactly the equality of the two blue-collapsed double sums.

This pins the witness extraction to one statement: the transfer kernel of `M` has the
incident-matrix coupling form of a single bond matrix `N`. By kernel uniqueness through the
second tensor's double blocked injectivity
(`transferCoeff_eq_incidentKernel_iff_coeff_eq`,
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`), this is `IsBondLocalTransferKernel`. -/

open scoped Classical in
/-- **The witness condition through the blue collapse.** For a bond matrix `N` on the
boundary edge `f`, the transfer kernel `transferCoeff A B red f M` equals the incident-matrix
kernel `incidentKernel B red f N` if and only if the first tensor's blue-collapsed
coefficient of `M` equals the second tensor's blue-collapsed coefficient of `N` at every red
physical leg `σ` and split blue/complement legs `σblue`, `σcompl`.

The forward direction substitutes the kernel equality into either collapse; the backward
direction passes from the blue-collapse equality to the fused-leg coefficient equality
(dividing out the nonzero blue interior bond product) and reads off the kernel equation
through the fused-leg split bridge `regionInsertedCoeff_eq_threeBlockInsertedCoeff_split`
(`TNLean.PEPS.RegionBlock.ThreeBlockReconcile`) and kernel uniqueness
`transferCoeff_eq_incidentKernel_iff_coeff_eq`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`). This is the precise statement the witness
extraction must establish: the existence of a bond matrix `N` matching the blue-collapsed
coefficient.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_eq_incidentKernel_iff_blueCollapse_eq
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
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    transferCoeff (G := G) A B DB.red hRB hCB f M = incidentKernel (G := G) B DB.red f N ↔
      ∀ (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
        (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
        (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement),
        (regionInteriorBondProd (G := G) B DB.blue : ℂ) •
            regionInsertedCoeff (G := G) A DB.red f M σ
              (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) =
          (regionInteriorBondProd (G := G) B DB.blue : ℂ) •
            regionInsertedCoeff (G := G) B DB.red f N σ
              (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) := by
  classical
  -- The blue interior bond product of the second tensor is a nonzero scalar.
  have hne : (regionInteriorBondProd (G := G) B DB.blue : ℂ) ≠ 0 := by
    have : 0 < regionInteriorBondProd (G := G) B DB.blue :=
      regionInteriorBondProd_pos (G := G) B DB.blue hposB
    exact_mod_cast this.ne'
  constructor
  · -- The kernel equation gives the coefficient transfer, hence the blue-collapse equality.
    intro hker σ σblue σcompl
    have hcoeff := (transferCoeff_eq_incidentKernel_iff_coeff_eq A B DB.red hRA hRB hCA hCB hAB
      hposA hposB hDim f M N).mp hker σ
      (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)
    rw [hcoeff]
  · -- The blue-collapse equality gives the fused-leg coefficient transfer, hence the kernel
    -- equation.
    intro hblue
    rw [transferCoeff_eq_incidentKernel_iff_coeff_eq A B DB.red hRA hRB hCA hCB hAB
      hposA hposB hDim f M N]
    intro σ τ
    -- Recover the fused-leg coefficient equality from the blue-collapse equality by reading
    -- `τ` through the blue/complement split and dividing out the blue interior bond product.
    have hsplit := hblue σ (threeBlockBlueSplit (A := B) (e := e) DB τ)
      (threeBlockComplSplit (A := B) (e := e) DB τ)
    rw [threeBlockComplPhysical_split (A := B) (e := e) DB τ, smul_eq_mul, smul_eq_mul]
      at hsplit
    exact mul_left_cancel₀ hne hsplit

end PEPS
end TNLean
