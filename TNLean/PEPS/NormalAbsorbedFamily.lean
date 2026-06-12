import TNLean.PEPS.NormalPairBlocking
import TNLean.PEPS.CoherentFrameInstance2
import TNLean.PEPS.NormalEdgeGaugeFamily
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# The absorbed gauge family of a general normal PEPS blocking

This file builds, from the general normal PEPS blocking hypotheses on an
arbitrary finite simple graph (arXiv:1804.04964, Section 3, theorem labelled
`normal`, lines 1576--1583 of `Papers/1804.04964/paper_normal.tex`), a single
per-edge gauge family `X` with the bare-edge absorbed equality at *every* edge:

> `edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`.

Each edge receives its own absorbing gauge from the coherent-frame per-edge
engine (`exists_regionEdgeGauge_of_blockingData`) fed the shared one-edge
blocking datum of the pair predicate, and the conversion to the bare-edge
absorbed form is the graph-generic `edgeAbsorbed_of_conjIdentity`.  Because the
bare-edge identity at an edge constrains only the family's value there, the
per-edge choices combine into one family with no compatibility conditions.
This is the graph-general counterpart of the open-lattice family
`exists_normalSquareInteriorAbsorbedGaugeFamily`, with no interior restriction:
the blocking hypotheses supply a frame at every edge.

**Single crossing edge (the source's chain blocking):** the hypothesis that
the distinguished edge `e` is the *only* edge between the red and blue blocks
is the chain structure carried by the source phrase "blocked into three
partite injective MPS *around every edge*", not an added restriction.  The
source's blocking around an edge takes the two endpoints of the chosen edge as
the first two parties of the chain, so the chosen edge is the bond between
them (arXiv:1804.04964, lines 981--1009 of
`Papers/1804.04964/paper_normal.tex`); the Theorem 3 regions enlarge the first
two parties to injective blocks meeting only along the distinguished edge
(lines 1475--1498); and the proof reads the gauge of the isomorphism lemma as
living on that edge of the original network (lines 1037 and 1498), which
presupposes that the bond between the first two parties is the edge's own
virtual leg.  Since every edge between the red and blue blocks lies in the
red-to-blue bond of the chain, the edge being the entire bond is equivalent to
the single-crossing condition.  The recorded blocking bundle does not carry
the condition as a field, so it is stated separately; the reading is recorded
in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, theorem labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

open scoped Classical in
/-- **The absorbing gauge at an edge of a shared blocking datum.**

A one-edge blocking datum over the pair predicate of two tensors, whose
distinguished edge is the single red-to-blue crossing, admits an invertible
matrix `Ze` such that every per-edge gauge family `X` with `X e = Ze` satisfies
the bare-edge absorbed equality at `e` against `applyGauge B X`: inserting `N`
on `A`'s edge `e` matches inserting the reindexed `N` on `applyGauge B X`'s
edge `e`, for every global physical configuration.

The per-edge gauge comes from the coherent-frame engine
(`exists_regionEdgeGauge_of_blockingData`) fed the two single-tensor
projections of the shared datum; `Ze` is the orientation-adapted absorbing
gauge of the engine gauge (`absorbedBoundaryGauge`), and the conversion is
`edgeAbsorbed_of_conjIdentity`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph` applied around an
edge, lines 1449--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_absorbingGauge_of_pairBlockingDatum
    (A B : Tensor G d) {e : Edge G}
    (D : NormalEdgeBlockingData
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G e)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A D.red D.blue g ↔ g = e)
    (hUB : RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g) :
    ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge G) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := G) A e σ N =
            edgeInsertedCoeff (G := G) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  classical
  let DA := D.pairLeft
  let DB := D.pairRight
  have hred : DA.red = DB.red := rfl
  have hblue : DA.blue = DB.blue := rfl
  have hcompl : DA.complement = DB.complement := rfl
  have hRB : RegionBlockedTensorInjective (G := G) B DA.red :=
    regionBlockedTensorInjective_red DB
  have hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ DA.red) :=
    regionBlockedTensorInjective_host DB hUB
  obtain ⟨htransferAB, htransferBA, hmul, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData (A := A) (B := B) (e := e) DA DB
      hred hblue hcompl hbond hAB hd hposA hposB hsingle hRB hCB
  have hEeq : hEdge = congr_fun hbond e := Subsingleton.elim _ _
  subst hEeq
  set f := singleBoundaryEdge (G := G) A DA.red DA.blue e hsingle with hfdef
  have hcoeff : ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) DA.red)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ DA.red)),
      regionInsertedCoeff (G := G) A DA.red f M σ τ =
        regionInsertedCoeff (G := G) B DA.red f
          ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) σ τ := by
    intro M σ τ
    have hfwd := (regionInsertionTransfer_of_coeffTransfer A B DA.red f
      hRB hCB hAB hposB hbond htransferAB htransferBA hmul).fwd_coeff M σ τ
    rw [hZ M] at hfwd
    exact hfwd
  refine ⟨absorbedBoundaryGauge (G := G) B DA.red f Z, fun X hXe σ N => ?_⟩
  exact edgeAbsorbed_of_conjIdentity A B DA.red f hbond Z X hXe hposA
    (fun M σ' τ' => hcoeff M σ' τ') σ N

open scoped Classical in
/-- **The absorbed gauge family of the general normal blocking hypotheses.**

For two tensors on a finite simple graph satisfying the general normal PEPS
blocking hypotheses over the pair predicate, with each distinguished edge the
single red-to-blue crossing of its frame, matched bond dimensions, the same
state, and positive bonds, there is a per-edge gauge family `X` over the second
tensor's bonds with the bare-edge absorbed equality at every edge.

The family is built edge by edge from
`exists_absorbingGauge_of_pairBlockingDatum`; the bare-edge identity at an edge
constrains only the family's value there, so the choices need no compatibility.

**Single crossing edge (the source's chain blocking):** the single-crossing
condition `hsingle` is the formal content of blocking *around* each edge — the
distinguished edge is the entire bond between the first two parties of the
chain (arXiv:1804.04964, lines 981--1009 and 1475--1498 of
`Papers/1804.04964/paper_normal.tex`); see the module docstring and
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583, via the proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_normalAbsorbedGaugeFamily
    (A B : Tensor G d)
    (h : NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G)
    (hsingle : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (h.edgeBlocking.red e) (h.edgeBlocking.blue e) g ↔ g = e)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g) :
    ∃ X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ,
      ∀ (e : Edge G) (σ : V → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := G) A e σ N =
          edgeInsertedCoeff (G := G) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  classical
  have hUB : RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  have hsel : ∀ e : Edge G, ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge G) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := G) A e σ N =
            edgeInsertedCoeff (G := G) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) :=
    fun e => exists_absorbingGauge_of_pairBlockingDatum A B
      (h.edgeBlocking.blockingData e) (hsingle e) hUB hbond hAB hd hposA hposB
  choose X hX using hsel
  exact ⟨X, fun e σ N => hX e X rfl σ N⟩

end PEPS
end TNLean
