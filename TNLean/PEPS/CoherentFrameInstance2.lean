import TNLean.PEPS.CoherentFrameInstance

/-!
# The per-edge gauge of two one-edge blocking data

This file builds the coherent coarse blocking frame of a one-edge blocking datum
(`TNLean.PEPS.NormalEdgeBlockingData`) over the concrete region-injectivity predicate
of a tensor (`regionInjectivityDataOf A`), and then assembles the per-edge gauge of
two such data through the coherent-frame interface
`TNLean.PEPS.exists_regionEdgeGauge_of_coherentFrames`.

It is the continuation of `TNLean.PEPS.CoherentFrameInstance`, split off to keep both
files within the source-line budget.

The three regions and their blocked-tensor injectivities come directly from the
datum; the partition geometry (pairwise disjointness and coverage) comes from the
datum's disjointness and cover fields.  The single-crossing hypothesis
`IsCrossingEdge A red blue g ↔ g = e` is the coordinate computation supplied
separately by the lattice geometry; here it is a plain hypothesis.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 of `Papers/1804.04964/paper_normal.tex` (the three
  injective regions around an edge partition the lattice)](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The coherent frame of a one-edge blocking datum

A one-edge blocking datum over the concrete region-injectivity predicate of a tensor
supplies the three regions, their blocked-tensor injectivities, the pairwise
disjointness, and the coverage.  Together with positivity it builds the coherent
coarse blocking frame at that edge. -/

/-- The coherent coarse blocking frame of a one-edge blocking datum over
`regionInjectivityDataOf A`.  The three regions and their blocked-tensor
injectivities come from the datum; the partition geometry comes from the datum's
disjointness and coverage fields.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def coherentFrameOfBlockingData {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    CoherentCoarseBlockingFrame (G := G) (d := d) A :=
  coherentFrameOfRegions D.red_injective D.blue_injective D.complement_injective hd hpos
    D.red_disjoint_blue D.red_disjoint_complement D.blue_disjoint_complement D.cover_univ

@[simp] theorem coherentFrameOfBlockingData_red {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    (coherentFrameOfBlockingData D hd hpos).frame.red = D.red := rfl

@[simp] theorem coherentFrameOfBlockingData_blue {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    (coherentFrameOfBlockingData D hd hpos).frame.blue = D.blue := rfl

@[simp] theorem coherentFrameOfBlockingData_complement {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    (coherentFrameOfBlockingData D hd hpos).frame.complement = D.complement := rfl

/-- The coherent frame of a one-edge blocking datum is partitioned. -/
theorem coherentFrameOfBlockingData_isPartition {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    (coherentFrameOfBlockingData D hd hpos).frame.IsPartition :=
  ⟨D.red_disjoint_blue, D.red_disjoint_complement, D.blue_disjoint_complement, D.cover_univ⟩

/-! ### The per-edge gauge of two one-edge blocking data

Two one-edge blocking data over `A` and `B` sharing the three regions and the single
distinguished crossing edge `e`, with `A` and `B` generating the same state, give the
per-edge gauge on `e`: the bond dimensions on `e` coincide and the forward per-edge
matrix transfer is conjugation by an invertible gauge matrix.  This is the
unconditional gauge input the source's edge geometry supplies, with no single-vertex
injectivity of either tensor. -/

variable {B : Tensor G d}

open scoped Classical in
/-- **The per-edge gauge of two one-edge blocking data.**

Two one-edge blocking data over `A` and `B` (over the respective concrete
region-injectivity predicates) sharing the three regions, with
`A.bondDim = B.bondDim`, `SameState A B`, positive bond dimensions, the
single-crossing hypothesis on `e`, and `B`'s red and host blocked-tensor
injectivities, give the bond dimensions on `e` coinciding and an invertible gauge
matrix `Z` on `e` such that the forward per-edge matrix transfer on `e` is conjugation
by `Z`.

The conclusion is the conjugation property of
`exists_regionEdgeGauge_of_coherentFrames` transported to the blocking-datum
interface: the chosen forward coefficient transfer `htransferAB`, its backward
companion `htransferBA`, and the forward multiplicativity `hmul` assemble the
region-insertion transfer datum
`regionInsertionTransfer_of_coeffTransfer`, whose forward map on the boundary edge
`e` is `M ↦ Z * (reindex M) * Z⁻¹`.

No single-vertex injectivity of `A` or `B` is used: the only injectivity inputs are
the blocked-region injectivities carried by the two blocking data and `B`'s red and
host injectivities.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_blockingData {e : Edge G}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue) (hcompl : DA.complement = DB.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A DA.red DA.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := G) B DA.red)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ DA.red)) :
      ∃ htransferAB :
          ∀ M : Matrix (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1))
              (Fin (A.bondDim
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1)) ℂ,
            ∃ N : Matrix (Fin (B.bondDim
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1))
                (Fin (B.bondDim
                  (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1)) ℂ,
              ∀ (σ : RegionPhysicalConfig (V := V) (d := d) DA.red)
                (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ DA.red)),
                regionInsertedCoeff (G := G) A DA.red
                    (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) M σ τ =
                  regionInsertedCoeff (G := G) B DA.red
                    (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) N σ τ,
        ∃ htransferBA :
          ∀ N : Matrix (Fin (B.bondDim
              (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1))
              (Fin (B.bondDim
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1)) ℂ,
            ∃ M : Matrix (Fin (A.bondDim
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1))
                (Fin (A.bondDim
                  (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1)) ℂ,
              ∀ (σ : RegionPhysicalConfig (V := V) (d := d) DA.red)
                (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ DA.red)),
                regionInsertedCoeff (G := G) B DA.red
                    (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) N σ τ =
                  regionInsertedCoeff (G := G) A DA.red
                    (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) M σ τ,
        ∃ hmul : ∀ M M' : Matrix (Fin (A.bondDim
              (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1))
              (Fin (A.bondDim
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle).1)) ℂ,
            coeffTransferMap (G := G) A B DA.red
                (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle)
                htransferAB (M * M') =
              coeffTransferMap (G := G) A B DA.red
                  (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) htransferAB M *
                coeffTransferMap (G := G) A B DA.red
                  (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) htransferAB M',
        ∃ hEdge : A.bondDim e = B.bondDim e,
          ∃ Z : GL (Fin (B.bondDim e)) ℂ,
            ∀ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
              (regionInsertionTransfer_of_coeffTransfer A B DA.red
                  (singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle) hRB hCB hAB
                  hposB hbond htransferAB htransferBA hmul).fwd M =
                (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  set F := coherentFrameOfBlockingData DA hd hposA with hF
  set F' := coherentFrameOfBlockingData DB hd hposB with hF'
  have hPF : F.frame.IsPartition := coherentFrameOfBlockingData_isPartition DA hd hposA
  have hPF' : F'.frame.IsPartition := coherentFrameOfBlockingData_isPartition DB hd hposB
  have hr : F.frame.red = F'.frame.red := by simp [hF, hF', hred]
  have hb : F.frame.blue = F'.frame.blue := by simp [hF, hF', hblue]
  have hc : F.frame.complement = F'.frame.complement := by simp [hF, hF', hcompl]
  -- `F.frame.red = DA.red` and `F.frame.blue = DA.blue` hold definitionally, so the
  -- coherent-frames conclusion over `F` is the stated conclusion over `DA.red`/`DA.blue`.
  exact exists_regionEdgeGauge_of_coherentFrames F F' hPF hPF' hr hb hc hbond hAB hd hposA hposB
    e hsingle hRB hCB

end PEPS
end TNLean
