import TNLean.PEPS.TorusWindowWitness
import TNLean.PEPS.RegionBlock.RegionReconcile

/-!
# The window-region conjugation coefficient identity from a coefficient transfer

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) feeds the window-region witness
`windowEdgeCoeffIdentityWitness` a single-bond *conjugation* coefficient identity on the reference
edge `e`: inserting `M` into `A` over the left end window matches inserting the conjugate into `B`,
for an invertible gauge `Z`.  This file produces that conjugation identity from the
*coefficient-transfer* data the staircase route supplies, reusing the unconditional region-level
algebra of `RegionInsertionTransfer`.

## The reduction

The per-edge gauge read-off `exists_regionEdgeGauge_of_coeffTransfer`
(`TNLean/PEPS/RegionBlock/RegionReconcile.lean`) turns three inputs on the left end window `W`,
taken at the reference edge `e`, into the gauge `Z` and the conjugation form of the forward
transfer:

* `htransferAB`: for each inserted matrix `M`, a matrix `N` on `B` with matching region-inserted
  coefficient on `W` (the cross-tensor coefficient transfer);
* `htransferBA`: the reverse transfer;
* `hmul`: multiplicativity of the chosen forward transfer `coeffTransferMap`.

Everything else --- region injectivity of `W`, host injectivity of `univ \ W`, additivity,
homogeneity, identity-preservation, and the two-sided inverse --- is the unconditional region-level
machinery of `RegionInsertionTransfer`, available at the corollary's minimal size because the host
of a *single window* is injective there (the landed `regionBlockedTensorInjective_windowComplement`,
in contrast to the host of the rectangle red block, which is not).  The forward transfer's
coefficient-matching field then is exactly the witness's conjugation identity once the gauge form of
`exists_regionEdgeGauge_of_coeffTransfer` is substituted.

The two genuine inputs `htransferAB`/`htransferBA` and `hmul` are the staircase residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1: the coefficient transfer is the single-bond
peeling of the end-pair equality coupled across `A` and `B`, and the multiplicativity is the
homomorphism the single-crossing geometry yields in place of the edge-middle injectivity the
rectangle route uses (which fails at the minimal size).  Given them, the window witness assembles
unconditionally, which is the §5.2 packaging.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1--5.2.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### The conjugation coefficient identity from a coefficient transfer

The per-edge gauge read-off `exists_regionEdgeGauge_of_coeffTransfer` of
`TNLean/PEPS/RegionBlock/RegionReconcile.lean` turns the coefficient-transfer data on any region `R`
at a boundary edge `f` --- the forward and backward transfers and the forward multiplicativity ---
into a gauge `Z` and the conjugation form of the forward transfer.  Substituting that gauge form
into the forward transfer's coefficient-matching field (`RegionInsertionTransfer.fwd_coeff`) gives
the witness's conjugation coefficient identity directly, with no region-specific input. -/

section Generic

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **The conjugation coefficient identity from a coefficient transfer.**

On any region `R` at a boundary edge `f`, with region and host injectivity of both tensors, positive
bonds, the same state, matched bond dimensions, the two cross-tensor coefficient transfers
`htransferAB`/`htransferBA`, and the forward-transfer multiplicativity `hmul`, there is a gauge `Z`
and an edge bond-dimension equality `hE` so that inserting `M` into `A` over `R` at `f` matches
inserting `Z · (reindex M) · Z⁻¹` into `B`.

The gauge and the conjugation form of the forward map come from
`exists_regionEdgeGauge_of_coeffTransfer`; the forward transfer's coefficient-matching field
(`RegionInsertionTransfer.fwd_coeff`) becomes the conjugation identity once the gauge form is
substituted.  All region-level algebra is unconditional on the region/host injectivity; the three
transfer inputs are the genuine content.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem exists_regionConjCoeffIdentity_of_coeffTransfer (A B : Tensor G d) (R : Finset V)
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
    ∃ (hE : A.bondDim f.1 = B.bondDim f.1) (Z : GL (Fin (B.bondDim f.1)) ℂ),
      ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
        (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
        regionInsertedCoeff (G := G) A R f M σ τ =
          regionInsertedCoeff (G := G) B R f
            ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
              (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ := by
  obtain ⟨hE, Z, hZ⟩ := exists_regionEdgeGauge_of_coeffTransfer A B R f hRA hCA hRB hCB hAB
    hposA hposB hDim htransferAB htransferBA hmul
  refine ⟨hE, Z, fun M σ τ => ?_⟩
  -- The forward transfer matches the region-inserted coefficients (`fwd_coeff`); substituting its
  -- gauge form (`hZ`) gives the conjugation identity.
  have hfwd := (regionInsertionTransfer_of_coeffTransfer A B R f hRB hCB hAB hposB hDim
    htransferAB htransferBA hmul).fwd_coeff M σ τ
  rw [hZ M] at hfwd
  exact hfwd

end Generic

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The window-region conjugation coefficient identity from a coefficient transfer.**

The left-end-window instance of `exists_regionConjCoeffIdentity_of_coeffTransfer`: with the
staircase route's coefficient-transfer data on the left end window `W` at the reference edge `e`,
there is a gauge `Z` and an edge bond-dimension equality `hE` realizing the witness's conjugation
coefficient identity.  The host injectivity hypothesis `hCB` is the single-window host injectivity
available at the minimal size by `regionBlockedTensorInjective_windowComplement`, in contrast to the
rectangle red block's host, which fails there.  The three transfer inputs are the §5.1 staircase
residual; given them, the window witness's conjugation identity assembles unconditionally.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1--5.2. -/
theorem exists_windowConjCoeffIdentity_of_coeffTransfer
    {A B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hRA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hCA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hAB : SameState A B)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ N : Matrix (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (B.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
                hbh⟩ M σ τ =
            regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
                hbh⟩ N σ τ)
    (htransferBA : ∀ N : Matrix (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ M : Matrix (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (A.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
                hbh⟩ N σ τ =
            regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
                hbh⟩ M σ τ)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      coeffTransferMap (G := torusGraph width height) A B
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
            hbh⟩ htransferAB (M * M') =
        coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
              hbh⟩ htransferAB M *
          coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
              hbh⟩ htransferAB M') :
    ∃ (hE : A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
        B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))
      (Z : GL (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ),
      ∀ (M : Matrix (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (A.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
        (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
        (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
          (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
        regionInsertedCoeff (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
              hbh⟩ M σ τ =
          regionInsertedCoeff (G := torusGraph width height) B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw
              hbh⟩
            ((Z : Matrix _ _ ℂ) * Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
              (↑Z⁻¹ : Matrix _ _ ℂ)) σ τ :=
  exists_regionConjCoeffIdentity_of_coeffTransfer A B
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh⟩
    hRA hCA hRB hCB hAB hposA hposB hDim htransferAB htransferBA hmul

/-! ### The window witness from the coefficient transfer

Feeding the conjugation coefficient identity of `exists_windowConjCoeffIdentity_of_coeffTransfer`
to the window-region witness producer `windowEdgeCoeffIdentityWitness_of_hypotheses` discharges the
last hypothesis of the witness (the §5.1 peeling `hidZ`), so the witness assembles from the window
injectivity hypotheses and the coefficient-transfer data alone --- no `hidZ` supplied as a free
hypothesis.  This is the §5.2 packaging with the gauge `Z` produced internally.  The transfer-data
inputs `htransferAB`/`htransferBA`/`hmul` are the genuinely-new staircase residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1; everything downstream of them is
mechanical. -/

/-- **The window-region witness from the coefficient transfer.**

With the arc-window injectivity hypotheses and union closure for both tensors, the size hypotheses,
matched bond dimensions, the same state, positive bonds, and the staircase route's
coefficient-transfer data on the left end window at the reference edge `e`, the reference edge
carries an `EdgeCoeffIdentityWitness` whose per-edge and reference gauges are both the gauge `Z`
read off the transfer.  The conjugation coefficient identity `hidZ` of the witness is supplied
by `exists_windowConjCoeffIdentity_of_coeffTransfer`, so no `hidZ` enters as a free hypothesis ---
the §5.2 packaging with the gauge produced from the staircase residual rather than assumed.

The region and host injectivity of the left end window are discharged at the minimal size from the
hypotheses (the host by `regionBlockedTensorInjective_windowComplement`); the gauge `Z`, the
bond-dimension equality, and the conjugation identity come from the coefficient transfer.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1--5.2. -/
theorem exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer
    {A B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (hAB : SameState A B)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ N : Matrix (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (B.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ M σ τ =
            regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ N σ τ)
    (htransferBA : ∀ N : Matrix (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ M : Matrix (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (A.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ N σ τ =
            regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ M σ τ)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      coeffTransferMap (G := torusGraph width height) A B
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
            (by omega) ha0 haw hbh⟩ htransferAB (M * M') =
        coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
              (by omega) ha0 haw hbh⟩ htransferAB M *
          coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
              (by omega) ha0 haw hbh⟩ htransferAB M') :
    ∃ (Z Zref : GL (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
      (hE : A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
        B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)),
      Nonempty (EdgeCoeffIdentityWitness A B
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)
        Z Zref hE) := by
  -- The window's region injectivity for `A` and `B`, from the arc-window hypotheses.
  have hRA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hA.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  -- The gauge, the bond-dimension equality, and the conjugation coefficient identity from the
  -- coefficient transfer; the host injectivity is the single-window complement at the minimal size.
  obtain ⟨hE, Z, hid⟩ := exists_windowConjCoeffIdentity_of_coeffTransfer (by omega) (by omega)
    ha0 haw hbh hRA (hA.regionBlockedTensorInjective_windowComplement hUA hL hK hxw hyh _)
    hRB (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
    hAB hposA hposB hDim htransferAB htransferBA hmul
  refine ⟨Z, Z, hE, ⟨windowEdgeCoeffIdentityWitness_of_hypotheses hB hUB hL hK ha0 haw hbh
    hxw hyh Z hE hposB ?_⟩⟩
  intro M σ τ
  exact hid M σ τ

end PEPS
end TNLean
