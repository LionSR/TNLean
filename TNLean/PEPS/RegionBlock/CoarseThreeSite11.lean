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

end PEPS
end TNLean
