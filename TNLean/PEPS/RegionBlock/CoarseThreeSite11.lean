import TNLean.PEPS.RegionBlock.CoarseThreeSite10
import TNLean.PEPS.RegionBlock.ThreeBlockTransfer
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5

/-!
# The single-edge inserted-coefficient transfer and the per-edge gauge

This file is the final assembly of the normal-PEPS edge comparison. It chains the
inserted-coefficient descent `TNLean.PEPS.edgeInsertedCoeff_coarseTensor_descent` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite10`, the single-crossing specialization
`TNLean.PEPS.redBundleInsertedCoeff_singleton` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite8`, and the coarse coefficient transfer
`TNLean.PEPS.coarse_exists_edgeInsertedCoeff_eq` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite` into the single-edge coefficient transfer that
`TNLean.PEPS.bondLocal_iff_coeffTransfer` consumes.

The geometric input is the singleton hypothesis: the red region crosses to the blue
region across the single distinguished edge `e`. It is the source's coordinate blocking
(`Papers/1804.04964/paper_normal.tex:1449--1500`, the three injective regions around an
edge, where the red sites surround one endpoint and the blue sites the other).

## The bridge

The descent reads the inserted matrix through the bond-model-conjugated matrix
`TNLean.PEPS.bondModelMatrix` on the whole red-to-blue crossing bundle. Under the
singleton hypothesis the bundle is a single virtual leg on `e`
(`TNLean.PEPS.singletonCrossingEquiv`), so the bond-model-conjugated matrix is a
single-bundle matrix `TNLean.PEPS.singletonBundleMatrix` of a single-edge matrix on `e`,
obtained by reindexing through the composite of the bond model and the single-leg
crossing equivalence. The single-crossing specialization then reads the descent's
whole-bundle inserted coefficient as the ordinary single-edge region-inserted
coefficient `TNLean.PEPS.regionInsertedCoeff` on `e`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1449--1500
  (the single-crossing blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Positivity of the host-merge fiber product

The host-merge fiber multiplicity `hostMergeFiberProd` is a product of bond dimensions.
Under positive bond dimensions it is positive, so it cancels from both sides of the
descent. -/

/-- The host-merge fiber multiplicity is positive when the bond dimensions are positive:
it is the product of the complement non-incident bond product and the free blue bond
product, both products of positive bond dimensions. -/
theorem hostMergeFiberProd_pos (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    0 < hostMergeFiberProd (G := G) F := by
  rw [hostMergeFiberProd, regionNonIncidentBondProd, hostBlueFreeBondProd]
  exact Nat.mul_pos
    (Finset.prod_pos (fun e _ => hpos e)) (Finset.prod_pos (fun e _ => hpos e))

variable {B : Tensor G d}

/-- The host-merge fiber multiplicity depends only on the blue and complement regions and
the bond dimensions: two coherent frames over `A` and `B` sharing those regions and bond
dimensions have equal host-merge fiber multiplicities. -/
theorem hostMergeFiberProd_eq (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hblue : F.frame.blue = F'.frame.blue) (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) :
    hostMergeFiberProd (G := G) F = hostMergeFiberProd (G := G) F' := by
  rw [hostMergeFiberProd, hostMergeFiberProd, regionNonIncidentBondProd,
    regionNonIncidentBondProd, hostBlueFreeBondProd, hostBlueFreeBondProd, hcompl, hbond]
  rw [hblue]
  congr 1

/-! ### The single-edge bridge matrix

Under the singleton hypothesis, the coarse `r-b` super-bond `Fin (coarseBondDim
coarseEdgeRB)` identifies with the single virtual leg `Fin (A.bondDim e)` through the
composite of the bond model and the single-leg crossing equivalence. -/

/-- The single-edge bridge equivalence: the coarse `r-b` super-bond identified with the
single virtual leg `Fin (A.bondDim e)` through the bond model and the single-leg crossing
equivalence. -/
noncomputable def bridgeEquiv (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e) :
    Fin (F.frame.coarseBondDim coarseEdgeRB) ≃ Fin (A.bondDim e) :=
  (F.bondModel coarseEdgeRB).trans
    (singletonCrossingEquiv (G := G) A F.frame.red F.frame.blue e hsingle)

/-- The bond-model-conjugated matrix of a coarse matrix is the single-bundle matrix of
the single-edge matrix obtained by reindexing through the bridge equivalence. -/
theorem bondModelMatrix_eq_singletonBundleMatrix
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ) :
    bondModelMatrix (G := G) F M =
      singletonBundleMatrix (G := G) A F.frame.red F.frame.blue e hsingle
        (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle) M) := by
  funext p q
  have hbe : ∀ r : CrossingConfig (G := G) A F.frame.red F.frame.blue,
      (bridgeEquiv (G := G) F e hsingle).symm
          (singletonCrossingEquiv (G := G) A F.frame.red F.frame.blue e hsingle r) =
        (F.bondModel coarseEdgeRB).symm r := by
    intro r
    rw [Equiv.symm_apply_eq, bridgeEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [bondModelMatrix_apply, singletonBundleMatrix, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, hbe, hbe]

/-! ### Surjectivity of the descent's physical legs

The descent reads the region-inserted coefficient at the red physical leg
`coarseProj red (s 0)` and the host physical leg
`complPhysical (coarseProj blue (s 1)) (coarseProj complement (s 2))`. As `s` varies,
the red leg ranges over every red physical configuration (`coarseProj_surjective`) and the
host leg over every host physical configuration (`coarseProj_surjective` on the blue and
complement legs followed by `complPhysical_surjective`). -/

/-- Every pair of a red physical configuration `σ` and a host physical configuration `τ`
is realized by the descent's physical legs for some coarse physical assignment `s`. -/
theorem exists_descent_legs (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (hd : 0 < d)
    (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)) :
    ∃ s : Fin 3 → Fin (coarseDim V d),
      coarseProj F.frame.red (s 0) = σ ∧
        (F.frame.toThreeBlockGeometry hP).complPhysical
            (coarseProj F.frame.blue (s 1)) (coarseProj F.frame.complement (s 2)) = τ := by
  obtain ⟨s0, hs0⟩ := coarseProj_surjective (V := V) (d := d) hd F.frame.red σ
  obtain ⟨⟨σblue, σcompl⟩, hτ⟩ :=
    (F.frame.toThreeBlockGeometry hP).complPhysical_surjective (d := d) τ
  obtain ⟨s1, hs1⟩ := coarseProj_surjective (V := V) (d := d) hd F.frame.blue σblue
  obtain ⟨s2, hs2⟩ := coarseProj_surjective (V := V) (d := d) hd F.frame.complement σcompl
  refine ⟨![s0, s1, s2], hs0, ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [hs1, hs2]; exact hτ

/-! ### The single-edge inserted-coefficient descent

Chaining the inserted-coefficient descent with the single-edge bridge: the coarse
edge-inserted coefficient at the red-to-blue super-bond descends, under the singleton
hypothesis, to the host-merge fiber product times the single-edge region-inserted
coefficient of the bridge-reindexed matrix on the single boundary edge `e`. -/

open scoped Classical in
/-- **The single-edge inserted-coefficient descent.** Under the singleton hypothesis,
the coarse edge-inserted coefficient at the red-to-blue super-bond equals the host-merge
fiber product times the single-edge region-inserted coefficient of the bridge-reindexed
matrix on the single boundary edge `e`, with the red physical leg and the fused
blue/complement host leg.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 254--583 and 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeInsertedCoeff_coarseTensor_descent_single
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (s : Fin 3 → Fin (coarseDim V d))
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ) :
    edgeInsertedCoeff (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB s M =
      hostMergeFiberProd F •
        regionInsertedCoeff (G := G) A F.frame.red
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
          (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle) M)
          (coarseProj F.frame.red (s 0))
          ((F.frame.toThreeBlockGeometry hP).complPhysical
            (coarseProj F.frame.blue (s 1)) (coarseProj F.frame.complement (s 2))) := by
  rw [edgeInsertedCoeff_coarseTensor_descent F hP s M,
    bondModelMatrix_eq_singletonBundleMatrix F e hsingle M,
    redBundleInsertedCoeff_singleton F.frame.red F.frame.blue e hsingle]

/-! ### Region transport of the single-edge inserted coefficient

The single-edge region-inserted coefficient transports along an equality of regions:
relabel the inserted boundary edge and the two physical configurations along the
equality. -/

/-- The single-edge region-inserted coefficient is unchanged, up to relabelling the region,
the boundary edge, and the physical configurations, along a region equality. -/
theorem regionInsertedCoeff_congr {R R' : Finset V} (h : R = R')
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) A R' ⟨f.1, h ▸ f.2⟩ M
        (regionPhysicalConfigCongr (d := d) h σ)
        (regionPhysicalConfigCongr (d := d) (by rw [h]) τ) := by
  subst h
  rfl

/-! ### The single-edge coefficient transfer between two coherent frames

Two coherent frames over `A` and `B` sharing the three regions, the bond dimensions, and
the single-crossing edge `e`, with `A` and `B` generating the same state, give the
single-edge coefficient transfer on `e`: for every matrix inserted on `e` of the first
tensor there is a matrix on the second whose single-edge region-inserted coefficient
matches at every red and host physical configuration. -/

/-- The single-crossing hypothesis transports across coherent frames sharing the red and
blue regions: if the red region crosses the blue region of the first frame across the
single edge `e`, the same holds for the second frame's shared regions. -/
theorem hsingle_transport (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B) (e : Edge G)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (g : Edge G) :
    IsCrossingEdge (G := G) B F'.frame.red F'.frame.blue g ↔ g = e := by
  rw [IsCrossingEdge, ← hred, ← hblue]
  exact hsingle g

open scoped Classical in
/-- **The single-edge coefficient identity from a coarse identity.** If a coarse matrix
`Ncoarse` on the second frame reproduces, at every coarse physical assignment, the coarse
edge-inserted coefficient of the bond-model lift of `M`, then the single-edge
region-inserted coefficient of `M` on `A` equals that of the bond-model image of `Ncoarse`
on `B`, at every red and host physical configuration. The descent and the cancellation of
the shared positive host-merge fiber product carry the coarse identity down to the single
edge.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_coarse_eq
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hd : 0 < d)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (Mcoarse : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (Ncoarse : Matrix (Fin (F'.frame.coarseBondDim coarseEdgeRB))
      (Fin (F'.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (hN : ∀ s : Fin 3 → Fin (coarseDim V d),
      edgeInsertedCoeff (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB s Mcoarse =
        edgeInsertedCoeff (G := coarseGraph) (F'.frame.coarseTensor) coarseEdgeRB s Ncoarse)
    (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)) :
    regionInsertedCoeff (G := G) A F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
        (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle) Mcoarse) σ τ =
      regionInsertedCoeff (G := G) B F'.frame.red
        (singleBoundaryEdge (G := G) B F'.frame.red F'.frame.blue e
          (hsingle_transport F F' e hred hblue hsingle))
        (Matrix.reindexAlgEquiv ℂ ℂ
          (bridgeEquiv (G := G) F' e (hsingle_transport F F' e hred hblue hsingle)) Ncoarse)
        (regionPhysicalConfigCongr (d := d) hred σ)
        (regionPhysicalConfigCongr (d := d)
          (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ) := by
  classical
  set hsingle' := hsingle_transport F F' e hred hblue hsingle with hsingle'_def
  -- Realize `(σ, τ)` by the descent's physical legs on the first frame.
  obtain ⟨s, hsσ, hsτ⟩ := exists_descent_legs F hP hd σ τ
  -- The same coarse assignment realizes the transported legs on the second frame.
  have hsσ' : coarseProj F'.frame.red (s 0) = regionPhysicalConfigCongr (d := d) hred σ := by
    rw [← hsσ]; funext w; rfl
  have hsτ' : (F'.frame.toThreeBlockGeometry hP').complPhysical
        (coarseProj F'.frame.blue (s 1)) (coarseProj F'.frame.complement (s 2)) =
      regionPhysicalConfigCongr (d := d)
        (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ := by
    funext w
    rw [regionPhysicalConfigCongr_apply, ← hsτ]
    -- Both fused host legs read `coarseDecode` on the same branch (blue/complement shared).
    simp only [ThreeBlockGeometry.complPhysical, coarseProj]
    by_cases hb : w.1 ∈ F'.frame.blue
    · rw [dif_pos (show w.1 ∈ (F'.frame.toThreeBlockGeometry hP').blue from hb),
        dif_pos (show w.1 ∈ (F.frame.toThreeBlockGeometry hP).blue by rw [show
          (F.frame.toThreeBlockGeometry hP).blue = F.frame.blue from rfl, hblue]; exact hb)]
    · rw [dif_neg (show w.1 ∉ (F'.frame.toThreeBlockGeometry hP').blue from hb),
        dif_neg (show w.1 ∉ (F.frame.toThreeBlockGeometry hP).blue by rw [show
          (F.frame.toThreeBlockGeometry hP).blue = F.frame.blue from rfl, hblue]; exact hb)]
  -- The host-merge fiber products of the two frames coincide and are positive.
  have hfiber : hostMergeFiberProd (G := G) F = hostMergeFiberProd (G := G) F' :=
    hostMergeFiberProd_eq F F' hblue hcompl hbond
  have hfpos : 0 < hostMergeFiberProd (G := G) F := hostMergeFiberProd_pos F hpos
  -- Cancel the shared positive fiber product after the descent on both frames.
  refine nsmul_right_injective (M := ℂ) (Nat.pos_iff_ne_zero.mp hfpos) ?_
  -- The descent rewrites each side to a coarse edge-inserted coefficient.
  have hlhs : hostMergeFiberProd (G := G) F •
        regionInsertedCoeff (G := G) A F.frame.red
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
          (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle) Mcoarse) σ τ =
      edgeInsertedCoeff (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB s Mcoarse := by
    rw [← hsσ, ← hsτ,
      ← edgeInsertedCoeff_coarseTensor_descent_single F hP e hsingle s Mcoarse]
  have hrhs : hostMergeFiberProd (G := G) F •
        regionInsertedCoeff (G := G) B F'.frame.red
          (singleBoundaryEdge (G := G) B F'.frame.red F'.frame.blue e hsingle')
          (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F' e hsingle') Ncoarse)
          (regionPhysicalConfigCongr (d := d) hred σ)
          (regionPhysicalConfigCongr (d := d)
            (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ) =
      edgeInsertedCoeff (G := coarseGraph) (F'.frame.coarseTensor) coarseEdgeRB s Ncoarse := by
    rw [hfiber, ← hsσ', ← hsτ',
      ← edgeInsertedCoeff_coarseTensor_descent_single F' hP' e hsingle' s Ncoarse]
  change hostMergeFiberProd (G := G) F • _ = hostMergeFiberProd (G := G) F • _
  rw [hlhs, hrhs]
  exact hN s

open scoped Classical in
/-- **The single-edge coefficient transfer.** Two coherent frames over `A` and `B`
sharing the three regions, the bond dimensions, and the single-crossing edge `e`, with
`A` and `B` generating the same state, give: for every matrix `M` inserted on `e` of `A`
there is a matrix `N` on `B` whose single-edge region-inserted coefficient matches at
every red physical configuration `σ` and host physical configuration `τ`.

The transfer chains the single-edge descent on both frames, the coarse coefficient
transfer `coarse_exists_edgeInsertedCoeff_eq`, and the cancellation of the shared positive
host-merge fiber product. No single-vertex injectivity is used: the descent rests on the
blocked-region injectivities of the frames.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionInsertedCoeff_eq_of_coherentFrames
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∃ N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
      ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
        regionInsertedCoeff (G := G) A F.frame.red
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
          regionInsertedCoeff (G := G) B F'.frame.red
            (singleBoundaryEdge (G := G) B F'.frame.red F'.frame.blue e
              (hsingle_transport F F' e hred hblue hsingle))
            N
            (regionPhysicalConfigCongr (d := d) hred σ)
            (regionPhysicalConfigCongr (d := d)
              (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ) := by
  classical
  -- The coarse coefficient transfer gives a coarse matrix `Ncoarse` on the second frame.
  have hsame : SameState (F.frame.coarseTensor) (F'.frame.coarseTensor) :=
    coarseTensor_sameState_of_sameState F F' hP hP' hred hblue hcompl hbond hAB
  obtain ⟨Ncoarse, hN⟩ := coarse_exists_edgeInsertedCoeff_eq F.frame F'.frame hsame
    (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M)
  refine ⟨Matrix.reindexAlgEquiv ℂ ℂ
    (bridgeEquiv (G := G) F' e (hsingle_transport F F' e hred hblue hsingle)) Ncoarse,
    fun σ τ => ?_⟩
  have hMrecover : Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle)
      (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M) = M := by
    rw [← Matrix.reindexAlgEquiv_symm, AlgEquiv.apply_symm_apply]
  rw [← hMrecover]
  exact regionInsertedCoeff_eq_of_coarse_eq F F' hP hP' hred hblue hcompl hbond hd hpos e
    hsingle _ Ncoarse hN σ τ

/-- **The single-region single-edge coefficient transfer.** Restating the coefficient
transfer over the shared red region `R := F.frame.red`: for two coherent frames over `A`
and `B` sharing the three regions, the bond dimensions, and the single-crossing edge `e`,
with `A` and `B` generating the same state, every matrix inserted on `e` of `A` is matched
by a matrix on `B` whose single-edge region-inserted coefficient over `R` agrees at every
red and host physical configuration. This is the shape `bondLocal_iff_coeffTransfer`
consumes.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionInsertedCoeff_eq_sharedRegion
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∃ N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
      ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
        regionInsertedCoeff (G := G) A F.frame.red
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
          regionInsertedCoeff (G := G) B F.frame.red
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ := by
  obtain ⟨N, hN⟩ := exists_regionInsertedCoeff_eq_of_coherentFrames F F' hP hP' hred hblue
    hcompl hbond hAB hd hpos e hsingle M
  refine ⟨N, fun σ τ => ?_⟩
  rw [hN σ τ, regionInsertedCoeff_congr (A := B) hred
    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ]
  rfl

/-! ### The concrete single-edge transfer and its multiplicativity

The coarse edge-transfer matrix `edgeTransferMatrix` on the coarse `r-b` edge is an
explicit, multiplicative coefficient transfer. Conjugating it by the bond models of the
two frames gives an explicit single-edge transfer on `e`, multiplicative by
`edgeTransferMatrix_mul` and the algebra-equivalence reindexing. -/

/-- **The concrete single-edge transfer.** The coarse edge-transfer matrix on the coarse
`r-b` edge, conjugated by the two frames' bond models into an explicit matrix transfer on
the single edge `e`. -/
noncomputable def regionEdgeTransfer
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ
    (bridgeEquiv (G := G) F' e (hsingle_transport F F' e hred hblue hsingle))
    (edgeTransferMatrix (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
      (F.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
      (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
      F'.frame.coarseTensor_pos_bondDim
      (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M))

open scoped Classical in
/-- **The concrete single-edge transfer matches the region-inserted coefficient.** The
single-edge region-inserted coefficient of `M` on `A` equals that of the concrete transfer
`regionEdgeTransfer M` on `B`, at every red and host physical configuration: the coarse
edge-transfer matrix matches the coarse edge-inserted coefficient
(`edgeTransferMatrix_edgeInsertedCoeff`), and the descent carries it down to the edge.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionEdgeTransfer_regionInsertedCoeff
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)) :
    regionInsertedCoeff (G := G) A F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
      regionInsertedCoeff (G := G) B F'.frame.red
        (singleBoundaryEdge (G := G) B F'.frame.red F'.frame.blue e
          (hsingle_transport F F' e hred hblue hsingle))
        (regionEdgeTransfer F F' hred hblue e hsingle M)
        (regionPhysicalConfigCongr (d := d) hred σ)
        (regionPhysicalConfigCongr (d := d)
          (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ) := by
  classical
  have hsame : SameState (F.frame.coarseTensor) (F'.frame.coarseTensor) :=
    coarseTensor_sameState_of_sameState F F' hP hP' hred hblue hcompl hbond hAB
  set Mcoarse := Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M with hMc
  set Ncoarse := edgeTransferMatrix (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
    (F.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
    (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
    F'.frame.coarseTensor_pos_bondDim Mcoarse with hNc
  have hMrecover :
      Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle) Mcoarse = M := by
    rw [hMc, ← Matrix.reindexAlgEquiv_symm, AlgEquiv.apply_symm_apply]
  have hRtransfer : regionEdgeTransfer F F' hred hblue e hsingle M =
      Matrix.reindexAlgEquiv ℂ ℂ
        (bridgeEquiv (G := G) F' e (hsingle_transport F F' e hred hblue hsingle)) Ncoarse := rfl
  rw [hRtransfer]
  conv_lhs => rw [← hMrecover]
  refine regionInsertedCoeff_eq_of_coarse_eq F F' hP hP' hred hblue hcompl hbond hd hpos e
    hsingle Mcoarse Ncoarse (fun s => ?_) σ τ
  exact edgeTransferMatrix_edgeInsertedCoeff (F.frame.coarseTensor) (F'.frame.coarseTensor)
    coarseEdgeRB (F.frame.coarseTensor_edgeBlockedThreeSiteInjective)
    (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective) hsame
    F'.frame.coarseTensor_pos_bondDim Mcoarse s

/-- **The concrete single-edge transfer is multiplicative.** The conjugated coarse
edge-transfer matrix sends a product to the product of the transfers: the coarse transfer is
multiplicative (`edgeTransferMatrix_mul`) and the bond-model reindexings are algebra
equivalences.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the homomorphism `X->O`, lines
254--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionEdgeTransfer_mul
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M M' : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    regionEdgeTransfer F F' hred hblue e hsingle (M * M') =
      regionEdgeTransfer F F' hred hblue e hsingle M *
        regionEdgeTransfer F F' hred hblue e hsingle M' := by
  have hsame : SameState (F.frame.coarseTensor) (F'.frame.coarseTensor) :=
    coarseTensor_sameState_of_sameState F F' hP hP' hred hblue hcompl hbond hAB
  rw [regionEdgeTransfer, regionEdgeTransfer, regionEdgeTransfer]
  rw [show Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm (M * M') =
      Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M *
        Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M'
      from map_mul _ _ _]
  rw [show edgeTransferMatrix (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
        (F.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
        (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
        F'.frame.coarseTensor_pos_bondDim
        (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M *
          Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M') =
      edgeTransferMatrix (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
          (F.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
          (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
          F'.frame.coarseTensor_pos_bondDim
          (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M) *
        edgeTransferMatrix (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
          (F.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
          (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective).endpoint_linearIndependent.2
          F'.frame.coarseTensor_pos_bondDim
          (Matrix.reindexAlgEquiv ℂ ℂ (bridgeEquiv (G := G) F e hsingle).symm M') from
      edgeTransferMatrix_mul (F.frame.coarseTensor) (F'.frame.coarseTensor) coarseEdgeRB
        (F.frame.coarseTensor_edgeBlockedThreeSiteInjective)
        (F'.frame.coarseTensor_edgeBlockedThreeSiteInjective) hsame
        F'.frame.coarseTensor_pos_bondDim _ _]
  exact map_mul _ _ _

/-- **The concrete single-edge transfer matches the region-inserted coefficient over the
shared region.** Restating `regionEdgeTransfer_regionInsertedCoeff` over `R := F.frame.red`
for both tensors. -/
theorem regionEdgeTransfer_regionInsertedCoeff_sharedRegion
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)) :
    regionInsertedCoeff (G := G) A F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
      regionInsertedCoeff (G := G) B F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
        (regionEdgeTransfer F F' hred hblue e hsingle M) σ τ := by
  rw [regionEdgeTransfer_regionInsertedCoeff F F' hP hP' hred hblue hcompl hbond hAB hd hpos e
    hsingle M σ τ, regionInsertedCoeff_congr (A := B) hred
    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
    (regionEdgeTransfer F F' hred hblue e hsingle M) σ τ]
  rfl

/-! ### The host-block injectivity of a coherent frame

The set complement of the red block, the union of the blue and complement blocks, is
blocked-tensor injective: the disjoint union lemma applied to the blue and complement
injectivities of the frame. -/

/-- The host block `univ \ red` of a partitioned coherent frame is blocked-tensor
injective. -/
theorem regionInjective_compl_red (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ F.frame.red) := by
  rw [hP.sdiff_red]
  exact regionBlockedTensorInjective_union_disjoint hP.blue_disjoint_complement
    F.frame.blue_injective F.frame.complement_injective hpos

/-- **The backward single-region single-edge coefficient transfer.** The `B → A` direction
of the single-region coefficient transfer over `R := F.frame.red`: every matrix inserted on
`e` of `B` is matched by a matrix on `A`. -/
theorem exists_regionInsertedCoeff_eq_sharedRegion_symm
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :
    ∃ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
      ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
        regionInsertedCoeff (G := G) B F.frame.red
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ =
          regionInsertedCoeff (G := G) A F.frame.red
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ := by
  -- The transported singleton hypothesis on the second frame's regions.
  have hsingle' := hsingle_transport F F' e hred hblue hsingle
  -- The swapped frames give the `B → A` transfer over `F'.frame.red`.
  obtain ⟨M, hM⟩ := exists_regionInsertedCoeff_eq_sharedRegion F' F hP' hP hred.symm hblue.symm
    hcompl.symm hbond.symm hAB.symm hd hposB e hsingle' N
  refine ⟨M, fun σ τ => ?_⟩
  rw [regionInsertedCoeff_congr (A := B) hred
      (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ,
    regionInsertedCoeff_congr (A := A) hred
      (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ]
  exact hM (regionPhysicalConfigCongr (d := d) hred σ)
    (regionPhysicalConfigCongr (d := d)
      (show Finset.univ \ F.frame.red = Finset.univ \ F'.frame.red by rw [hred]) τ)

/-! ### The bond-local transfer kernel and the per-edge gauge

The single-region coefficient transfer feeds `bondLocal_iff_coeffTransfer` to give the
bond-local transfer kernel on the single edge `e`, in both directions, and the per-edge
gauge follows by the multiplicativity of the forward coefficient transfer. -/

open scoped Classical in
/-- **The bond-local transfer kernel of two coherent frames.** Two coherent frames over
`A` and `B` sharing the three regions, the bond dimensions, and the single-crossing edge
`e`, with `A` and `B` generating the same state, give the bond-local transfer kernel on the
single boundary edge `e` of the shared red region: the transfer kernel of every inserted
matrix is the incident-matrix kernel of some bond matrix on `e`.

No single-vertex injectivity is used: the four block injectivities are the frame's
blocked-region injectivities and the host-block disjoint union, and the coefficient
transfer is the single-region transfer above.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines 254--583
of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_coherentFrames
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := G) B F.frame.red)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ F.frame.red)) :
    IsBondLocalTransferKernel (G := G) A B F.frame.red hRB hCB
      (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) := by
  rw [bondLocal_iff_coeffTransfer A B F.frame.red F.frame.red_injective hRB
    (regionInjective_compl_red F hP hposA) hCB hAB hposA hposB hbond
    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)]
  intro M
  exact exists_regionInsertedCoeff_eq_sharedRegion F F' hP hP' hred hblue hcompl hbond hAB
    hd hposA e hsingle M

/-! ### The per-edge gauge from two coherent frames

The single-region coefficient transfers in both directions, with the multiplicative concrete
forward transfer, feed `exists_regionEdgeGauge_of_coeffTransfer`: the forward per-edge matrix
transfer on `e` is conjugation by an invertible gauge matrix, and the bond dimensions on `e`
coincide. The multiplicativity of the chosen forward transfer is the concrete transfer's
multiplicativity, transported through `regionInsertedCoeff_injective`. -/

open scoped Classical in
/-- The chosen forward coefficient transfer equals the concrete multiplicative transfer:
both realize the same region-inserted coefficient on `B`, so block injectivity identifies
them. -/
theorem coeffTransferMap_eq_regionEdgeTransfer
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
        (Fin (A.bondDim (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
          (Fin (B.bondDim
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
          regionInsertedCoeff (G := G) A F.frame.red
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
            regionInsertedCoeff (G := G) B F.frame.red
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    coeffTransferMap (G := G) A B F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M =
      regionEdgeTransfer F F' hred hblue e hsingle M := by
  have hRB : RegionBlockedTensorInjective (G := G) B F.frame.red := by
    rw [hred]; exact F'.frame.red_injective
  have hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ F.frame.red) := by
    rw [hred]; exact regionInjective_compl_red F' hP' hposB
  refine regionInsertedCoeff_injective (G := G) B F.frame.red hRB hCB hposB
    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) _ _ (fun σ τ => ?_)
  rw [← coeffTransferMap_coeff A B F.frame.red
      (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M σ τ,
    ← regionEdgeTransfer_regionInsertedCoeff_sharedRegion F F' hP hP' hred hblue hcompl hbond
      hAB hd hposA e hsingle M σ τ]

open scoped Classical in
/-- **The per-edge gauge from two coherent frames.** Two coherent frames over `A` and `B`
sharing the three regions, the bond dimensions, and the single-crossing edge `e`, with `A`
and `B` generating the same state, give a per-edge gauge on `e`: the forward per-edge matrix
transfer is conjugation by an invertible matrix `Z`, and the bond dimensions on `e` coincide.

No single-vertex injectivity is used: the four block injectivities are the frames'
blocked-region injectivities and the host-block disjoint unions, the two coefficient transfers
are the single-region transfers above, and the forward multiplicativity is the concrete
transfer's multiplicativity carried through `regionInsertedCoeff_injective`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_coherentFrames
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e) :
    ∀ (hRB : RegionBlockedTensorInjective (G := G) B F.frame.red)
      (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ F.frame.red)),
    ∃ htransferAB :
        ∀ M : Matrix (Fin (A.bondDim
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
            (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
          ∃ N : Matrix (Fin (B.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
              (Fin (B.bondDim
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
            ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
              (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
              regionInsertedCoeff (G := G) A F.frame.red
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
                regionInsertedCoeff (G := G) B F.frame.red
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ,
      ∃ htransferBA :
        ∀ N : Matrix (Fin (B.bondDim
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
            (Fin (B.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
          ∃ M : Matrix (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
              (Fin (A.bondDim
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
            ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
              (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
              regionInsertedCoeff (G := G) B F.frame.red
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ =
                regionInsertedCoeff (G := G) A F.frame.red
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ,
      ∃ hmul : ∀ M M' : Matrix (Fin (A.bondDim
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
            (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
          coeffTransferMap (G := G) A B F.frame.red
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle)
              htransferAB (M * M') =
            coeffTransferMap (G := G) A B F.frame.red
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M *
              coeffTransferMap (G := G) A B F.frame.red
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M',
      ∃ hEdge : A.bondDim
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1 =
        B.bondDim (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1,
        ∃ Z : GL (Fin (B.bondDim
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
          ∀ M : Matrix (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
              (Fin (A.bondDim
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
            (regionInsertionTransfer_of_coeffTransfer A B F.frame.red
                (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) hRB hCB hAB
                hposB hbond htransferAB htransferBA hmul).fwd M =
              (Z : Matrix (Fin (B.bondDim
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
                  (Fin (B.bondDim
                    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                ((Z⁻¹ : GL (Fin (B.bondDim
                  (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ) :
                  Matrix (Fin (B.bondDim
                    (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
                    (Fin (B.bondDim
                      (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
                    ℂ) := by
  intro hRB hCB
  set f := singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle with hf
  -- The forward coefficient transfer is the concrete transfer's coefficient identity.
  have htransferAB :
      ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
          ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
            (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
            regionInsertedCoeff (G := G) A F.frame.red f M σ τ =
              regionInsertedCoeff (G := G) B F.frame.red f N σ τ :=
    fun M => exists_regionInsertedCoeff_eq_sharedRegion F F' hP hP' hred hblue hcompl hbond hAB
      hd hposA e hsingle M
  have htransferBA :
      ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∃ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
            (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
            regionInsertedCoeff (G := G) B F.frame.red f N σ τ =
              regionInsertedCoeff (G := G) A F.frame.red f M σ τ :=
    fun N => exists_regionInsertedCoeff_eq_sharedRegion_symm F F' hP hP' hred hblue hcompl hbond
      hAB hd hposB e hsingle N
  -- The forward multiplicativity, via the concrete transfer's multiplicativity.
  have hmul : ∀ M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      coeffTransferMap (G := G) A B F.frame.red f htransferAB (M * M') =
        coeffTransferMap (G := G) A B F.frame.red f htransferAB M *
          coeffTransferMap (G := G) A B F.frame.red f htransferAB M' := by
    intro M M'
    rw [coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
        hposB e hsingle htransferAB (M * M'),
      coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
        hposB e hsingle htransferAB M,
      coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
        hposB e hsingle htransferAB M']
    exact regionEdgeTransfer_mul F F' hP hP' hred hblue hcompl hbond hAB e hsingle M M'
  refine ⟨htransferAB, htransferBA, hmul, ?_⟩
  exact exists_regionEdgeGauge_of_coeffTransfer A B F.frame.red f
    F.frame.red_injective (regionInjective_compl_red F hP hposA) hRB hCB
    hAB hposA hposB hbond htransferAB htransferBA hmul

end PEPS
end TNLean
