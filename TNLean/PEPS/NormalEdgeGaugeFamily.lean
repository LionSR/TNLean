import TNLean.PEPS.NormalEdgeBlockingInterior
import TNLean.PEPS.NormalEdgeSingleCrossing
import TNLean.PEPS.CoherentFrameInstance2
import TNLean.Algebra.ScalarCommutant

/-!
# The per-edge gauge family at the interior edges of the square lattice

This file assembles the per-edge gauge of two normal PEPS at every interior edge of
the finite rectangular square lattice.  Each interior edge — a translated horizontal
or vertical edge with two rows and columns of margin around its blocking frame —
carries cover-free red, blue, and complementary blocking data
(`TNLean.PEPS.NormalEdgeBlockingInterior`).  Around that edge the three blocks are
injective, partition the lattice, and meet only along the distinguished edge
(`TNLean.PEPS.NormalEdgeSingleCrossing`).  Feeding the two data of the two tensors to
the coherent-frame gauge interface
(`TNLean.PEPS.exists_regionEdgeGauge_of_blockingData`) gives, on that edge, the bond
dimensions of the two tensors coinciding and the forward per-edge matrix transfer
realized as conjugation by an invertible gauge matrix.

The geometry layer builds its blocking data over the canonical product decidable
equality on `Fin width × Fin height`, whereas the gauge interface synthesizes a
decidable equality from the lattice's linear order.  These now coincide
definitionally (`TNLean.PEPS.instLinearOrderSquareLatticeVertex` pins its
`toDecidableEq` field to the product instance), so the interior data feed the gauge
interface directly.

**Scope restriction (interior edges):** the present open rectangular coordinate model
admits the cover-free interior data only at edges whose blocking frame fits with two
rows and columns of margin on every side.  Boundary edges fall outside the interior
margin predicates; that boundary geometry is the residual open part of the every-edge
construction, recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`,
Section "Remaining mathematical obligations".  The translation-invariant reduction of
these per-edge gauges to one horizontal and one vertical matrix, and the total gauge
family over *all* edges that such a reduction expects, are the next mathematical
steps above this interior gauge family, recorded in the same note.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair
  states generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3,
  lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ}

/-- The set complement of the red block of a one-edge blocking datum is the union of
its blue and complementary blocks.  This is the host region whose blocked-tensor
injectivity the gauge interface consumes alongside the red injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex` (the three blocks partition the lattice). -/
theorem blockingData_univ_sdiff_red {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {ι : RegionInjectivityData V} {G : SimpleGraph V} {e : Edge G}
    (D : NormalEdgeBlockingData ι G e) :
    Finset.univ \ D.red = D.blue ∪ D.complement := by
  have hcov := D.cover_univ
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro _
    have hmem : v ∈ D.red ∪ D.blue ∪ D.complement := by rw [hcov]; exact Finset.mem_univ v
    simp only [Finset.mem_union] at hmem
    tauto
  · rintro (hb | hc)
    · exact fun hr => Finset.disjoint_left.mp D.red_disjoint_blue hr hb
    · exact fun hr => Finset.disjoint_left.mp D.red_disjoint_complement hr hc

/-- The host region `univ \ red` of a one-edge blocking datum over
`regionInjectivityDataOf B` is blocked-tensor injective for `B`, derived from the blue
and complementary injectivities through union closure.  This is the second host
injectivity the gauge interface consumes for the second tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_host {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj] {B : Tensor G d} {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hUB : RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) B)) :
    RegionBlockedTensorInjective (G := G) B (Finset.univ \ DB.red) := by
  rw [blockingData_univ_sdiff_red DB]
  have hi := hUB.union_injective DB.blue_injective DB.complement_injective
  rwa [regionInjectivityDataOf_isInjective] at hi

/-! ### Uniqueness of the per-edge gauge up to a scalar

The gauge realizing the forward per-edge transfer as conjugation is determined up
to a multiplicative constant.  If two invertible matrices `Z` and `Z'` conjugate
every bond matrix to the same value, then `Z⁻¹Z'` commutes with the whole bond
matrix algebra, hence is a scalar (`Matrix.isScalar_of_commute_span_eq_top`,
the center of the full matrix algebra is the scalars), so `Z'` and `Z` differ by
a nonzero scalar.  This is the source's *"`X` and `Y` are unique up to a
multiplicative constant"* (arXiv:1804.04964, Section 3, Theorem 3) at the level of
a single edge.  It is the algebraic input to the orientation-uniform selection. -/

/-- **Uniqueness up to scalar of a conjugating matrix.**

If two invertible matrices `Z` and `Z'` of the same size induce the same
conjugation map `N ↦ Z N Z⁻¹ = Z' N Z'⁻¹` on every matrix `N`, then they differ by
a nonzero scalar: `Z' = c • Z` for some `c : ℂˣ`.  The matrix `Z⁻¹Z'` commutes with
every `N`, so it lies in the center of the full matrix algebra, which is the
scalar matrices.

Source: arXiv:1804.04964, Section 3, Theorem 3 ("`X` and `Y` are unique up to a
multiplicative constant"), the per-edge centralizer step. -/
theorem gl_conj_unique_scalar {n : ℕ} (Z Z' : GL (Fin n) ℂ)
    (h : ∀ N : Matrix (Fin n) (Fin n) ℂ,
      (Z : Matrix (Fin n) (Fin n) ℂ) * N * (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) =
        (Z' : Matrix (Fin n) (Fin n) ℂ) * N * (↑Z'⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ c : ℂˣ, (Z' : Matrix (Fin n) (Fin n) ℂ) = (c : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ) := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (↑Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  set Zim : Matrix (Fin n) (Fin n) ℂ := (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) with hZim
  set Z'm : Matrix (Fin n) (Fin n) ℂ := (↑Z' : Matrix (Fin n) (Fin n) ℂ) with hZ'm
  set Z'im : Matrix (Fin n) (Fin n) ℂ := (↑Z'⁻¹ : Matrix (Fin n) (Fin n) ℂ) with hZ'im
  have hZZi : Zm * Zim = 1 := by
    rw [hZm, hZim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZiZ : Zim * Zm = 1 := by
    rw [hZm, hZim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZ'iZ' : Z'im * Z'm = 1 := by
    rw [hZ'm, hZ'im, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- `W := Z⁻¹ Z'` commutes with every matrix.
  set W : Matrix (Fin n) (Fin n) ℂ := Zim * Z'm with hW
  have hcomm : ∀ N ∈ (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)), W * N = N * W := by
    intro N _
    have hN : N = Zim * (Z'm * N * Z'im) * Zm := by
      rw [← h N]
      rw [show Zim * (Zm * N * Zim) * Zm = (Zim * Zm) * N * (Zim * Zm) by
        simp [Matrix.mul_assoc], hZiZ, Matrix.one_mul, Matrix.mul_one]
    calc W * N = Zim * (Z'm * N) := by rw [hW, Matrix.mul_assoc]
      _ = Zim * (Z'm * N * Z'im) * Z'm := by
            rw [show Zim * (Z'm * N * Z'im) * Z'm = Zim * (Z'm * N) * (Z'im * Z'm) by
              simp [Matrix.mul_assoc], hZ'iZ', Matrix.mul_one]
      _ = Zim * (Z'm * N * Z'im) * (Zm * Zim) * Z'm := by rw [hZZi, Matrix.mul_one]
      _ = (Zim * (Z'm * N * Z'im) * Zm) * (Zim * Z'm) := by simp [Matrix.mul_assoc]
      _ = N * W := by rw [← hN, hW]
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top W
    (S := Set.univ) (by rw [Submodule.span_univ]) hcomm
  have hscal : (Matrix.scalar (Fin n)) c = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]; rfl
  have hWunit : IsUnit W := by
    rw [hW, hZim, hZ'm]; exact (Z⁻¹).isUnit.mul Z'.isUnit
  -- The scalar is nonzero: when the bond space is empty pick `1`, else use `det W`.
  rcases isEmpty_or_nonempty (Fin n) with hempty | hne
  · exact ⟨1, by simp only [Units.val_one, one_smul]; exact Subsingleton.elim _ _⟩
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [hc, hscal, zero_smul] at hWunit
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_zero hne] at hWunit
      exact not_isUnit_zero hWunit
    refine ⟨Units.mk0 c hc0, ?_⟩
    have hZ'mZmW : Z'm = Zm * W := by
      rw [hW, ← Matrix.mul_assoc, hZZi, Matrix.one_mul]
    rw [hZ'mZmW, hc, hscal, Matrix.mul_smul, Matrix.mul_one, Units.val_mk0]

/-- **Uniqueness up to scalar of the per-edge gauge.**

Two gauges `Z` and `Z'` realizing the *same* forward per-edge transfer map `fwd`
on one edge --- where `fwd M = Z · (reindex M) · Z⁻¹ = Z' · (reindex M) · Z'⁻¹`
across the bond-dimension equalities `hE` and `hE'` --- differ by a nonzero
scalar.  The reindexing is an algebra equivalence, hence surjective, so the two
conjugation maps agree on every target bond matrix; `gl_conj_unique_scalar` then
gives the scalar.

This is the source's *"`X` and `Y` are unique up to a multiplicative constant"*
(arXiv:1804.04964, Section 3, Theorem 3) applied at a single edge: the per-edge
gauge produced by
`exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge` (and its vertical
counterpart) is determined by its transfer map up to a scalar. -/
theorem edgeGauge_unique_scalar {a b : ℕ} (hE hE' : a = b) (Z Z' : GL (Fin b) ℂ)
    (h : ∀ M : Matrix (Fin a) (Fin a) ℂ,
        (Z : Matrix (Fin b) (Fin b) ℂ) * Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix (Fin b) (Fin b) ℂ) =
          (Z' : Matrix (Fin b) (Fin b) ℂ) * Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE') M *
            (↑Z'⁻¹ : Matrix (Fin b) (Fin b) ℂ)) :
    ∃ c : ℂˣ, (Z' : Matrix (Fin b) (Fin b) ℂ) = (c : ℂ) • (Z : Matrix (Fin b) (Fin b) ℂ) := by
  refine gl_conj_unique_scalar Z Z' ?_
  intro N
  -- `reindexAlgEquiv` is surjective: every target matrix `N` is some `reindex M`.
  -- The proofs `hE` and `hE'` are equal by proof irrelevance, so both reindexings
  -- along them coincide and `h M` closes the goal directly.
  obtain ⟨M, rfl⟩ := (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE)).surjective N
  exact h M

open scoped Classical in
/-- **The per-edge gauge at a translated horizontal interior edge.**

Two normal PEPS `A` and `B` with the square-lattice rectangular-injectivity
hypotheses, union closure, matched bond dimensions, the same state, positive bonds,
and a translated horizontal blocking frame with two rows and columns of margin admit,
on the distinguished horizontal edge `e` of that frame, the per-edge gauge.  The two
interior data of `A` and `B` share the red, blue, and complementary blocks (the blocks
are coordinate regions, independent of the tensor), so feeding them to
`exists_regionEdgeGauge_of_blockingData` yields the bond dimensions of `A` and `B` on
`e` coinciding and a forward region-insertion transfer `fwd` realized as conjugation
by an invertible gauge matrix `Z`.  No single-vertex injectivity is used; the only
injectivity inputs are the blocked-region injectivities of the interior data and `B`'s
red and host injectivities.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g)
    (e : Edge (squareLatticeGraph width height))
    (he : e = normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e)
        (Z : GL (Fin (B.bondDim e)) ℂ)
        (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
        ∀ M, fwd M =
            (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  classical
  subst he
  have hew : xStart + 3 ≤ width := by omega
  have heh : yStart + 3 ≤ height := by omega
  let e := normalSquareHorizontalTranslatedEdge xStart yStart hew heh
  change ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
      (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
        Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
      ∀ M, fwd M =
          (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
            ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
              Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)
  let DA := normalSquareHorizontalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf A) hA hUA hx0 hy0 hxw hyh
  let DB := normalSquareHorizontalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf B) hB hUB hx0 hy0 hxw hyh
  have hDAred : DA.red = normalSquareHorizontalTranslatedEdgeRed xStart yStart := rfl
  have hDAblue : DA.blue = normalSquareHorizontalTranslatedEdgeBlue xStart yStart := rfl
  have hred : DA.red = DB.red := rfl
  have hblue : DA.blue = DB.blue := rfl
  have hcompl : DA.complement = DB.complement := rfl
  have hsingle : ∀ g, IsCrossingEdge (G := squareLatticeGraph width height) A DA.red DA.blue g
      ↔ g = e := by
    intro g
    rw [hDAred, hDAblue]
    exact isCrossingEdge_normalSquareHorizontalTranslatedEdge (width := width) (height := height)
      A (xStart := xStart) (yStart := yStart) hew heh g
  have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B DA.red := by
    rw [hred]; exact regionBlockedTensorInjective_red DB
  have hCB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ DA.red) := by
    rw [hred]; exact regionBlockedTensorInjective_host DB hUB
  obtain ⟨_, _, _, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData (A := A) (B := B) (e := e) DA DB
      hred hblue hcompl hbond hAB hd hposA hposB hsingle hRB hCB
  exact ⟨hEdge, Z, _, hZ⟩

open scoped Classical in
/-- **The per-edge gauge at a translated vertical interior edge.**

The rotated counterpart of `exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge`:
a translated vertical blocking frame with two rows and columns of margin admits, on its
distinguished vertical edge `e`, the per-edge gauge — the bond dimensions of `A` and
`B` on `e` coincide and a forward region-insertion transfer is conjugation by an
invertible gauge matrix.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_normalSquareVerticalTranslatedEdge
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g)
    (e : Edge (squareLatticeGraph width height))
    (he : e = normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e)
        (Z : GL (Fin (B.bondDim e)) ℂ)
        (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
        ∀ M, fwd M =
            (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  classical
  subst he
  have hew : xStart + 3 ≤ width := by omega
  have heh : yStart + 3 ≤ height := by omega
  let e := normalSquareVerticalTranslatedEdge xStart yStart hew heh
  change ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
      (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
        Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
      ∀ M, fwd M =
          (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
            ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
              Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)
  let DA := normalSquareVerticalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf A) hA hUA hx0 hy0 hxw hyh
  let DB := normalSquareVerticalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf B) hB hUB hx0 hy0 hxw hyh
  have hDAred : DA.red = normalSquareVerticalTranslatedEdgeRed xStart yStart := rfl
  have hDAblue : DA.blue = normalSquareVerticalTranslatedEdgeBlue xStart yStart := rfl
  have hred : DA.red = DB.red := rfl
  have hblue : DA.blue = DB.blue := rfl
  have hcompl : DA.complement = DB.complement := rfl
  have hsingle : ∀ g, IsCrossingEdge (G := squareLatticeGraph width height) A DA.red DA.blue g
      ↔ g = e := by
    intro g
    rw [hDAred, hDAblue]
    exact isCrossingEdge_normalSquareVerticalTranslatedEdge (width := width) (height := height)
      A (xStart := xStart) (yStart := yStart) hew heh g
  have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B DA.red := by
    rw [hred]; exact regionBlockedTensorInjective_red DB
  have hCB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ DA.red) := by
    rw [hred]; exact regionBlockedTensorInjective_host DB hUB
  obtain ⟨_, _, _, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData (A := A) (B := B) (e := e) DA DB
      hred hblue hcompl hbond hAB hd hposA hposB hsingle hRB hCB
  exact ⟨hEdge, Z, _, hZ⟩

end PEPS
end TNLean
