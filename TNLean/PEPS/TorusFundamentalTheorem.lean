import TNLean.PEPS.RegionScalarCondition
import TNLean.PEPS.TorusLatticeGraph
import TNLean.PEPS.RegionBlock.ScalarExtraction
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# The scalar condition of the normal PEPS Fundamental Theorem on the discrete torus

This file proves the scalar condition of the translationally invariant normal
PEPS Fundamental Theorem on the discrete torus (arXiv:1804.04964, Section 3,
Theorem 3, lines 1453--1471 of `Papers/1804.04964/paper_normal.tex`): if a single
scalar `λ` relates `A` to the gauge action of the second tensor at every torus
vertex, then `λ^{width·height} = 1`.

The per-vertex relation `A_v = λ · gaugeVertex B Z v` is the output of the `R`/`S`
region comparison (`RegionComplementComparison.regionComplement_comparison`); the
three layers here take it, or the comparison data producing it, as a hypothesis and
discharge the scalar condition on top.  The nonvanishing state coefficient needed
for the scalar cancellation is supplied by region injectivity of a single
comparison region and its complement
(`prod_perVertexScalar_eq_one_of_regionInjective`), so no vertex injectivity of `A`
is assumed: only injectivity after blocking, as the source requires.  The
unconditional torus theorem consuming these layers is
`fundamentalTheorem_normalTorusPEPS_unconditional`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Theorem 3,
  lines 1449--1471 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]

/-! ### The number of torus sites -/

/-- The number of vertices of the discrete `width × height` torus is
`width · height`. -/
theorem card_torusVertex (width height : ℕ) [NeZero width] [NeZero height] :
    Fintype.card (TorusVertex width height) = width * height := by
  simp [TorusVertex, Fintype.card_prod, ZMod.card]

/-! ### The scalar condition `λ^{width·height} = 1` on the torus -/

/-- **The scalar condition `λ^{width·height} = 1` on the torus.**

If a single scalar `λ` relates `A` to the gauge action of the second tensor at
every torus vertex (`A_v = λ · gaugeVertex B Z v`, the translationally invariant
per-vertex relation, all `c_v` equal to `λ`), then under the same state, positive
bonds, and a single comparison region `R` whose block and complement block are both
blocked-tensor injective, `λ` raised to the number of torus sites is one:
`λ^{width·height} = 1`.

This is the torus scalar condition of arXiv:1804.04964, Section 3, Theorem 3
(line 1471: `λ^{n·m} = 1`). It follows from
`prod_perVertexScalar_eq_one_of_regionInjective`: under translation invariance the
per-vertex scalars are all equal to `λ`, so their product over the `width × height`
torus is `λ^{width·height}`, and the region-injective nonvanishing state equality
forces that product to be one.

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem lambda_pow_card_torus_eq_one [Fact (1 < width)] [Fact (1 < height)]
    (A B : Tensor (torusGraph width height) d)
    (R : Finset (TorusVertex width height))
    (hRA : RegionBlockedTensorInjective (G := torusGraph width height) A R)
    (hCA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ R))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hAB : SameState A B)
    (Z : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (lam : ℂ)
    (hPV : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B Z v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    lam ^ (width * height) = 1 := by
  have hprod := prod_perVertexScalar_eq_one_of_regionInjective A B R hRA hCA hpos hAB Z hbd
    (fun _ => lam) hPV
  rw [Finset.prod_const, Finset.card_univ, card_torusVertex width height] at hprod
  exact hprod

/-! ### The scalar condition from the per-vertex two-block proportionalities

The per-vertex relation `hPV` of `lambda_pow_card_torus_eq_one` is itself the output
of the one-site quotient: at every vertex `v` the comparison at the one-site-different
regions `R_v` and `insert v R_v` delivers two two-block scalar proportionalities of the
blocked weights against the gauge-absorbed tensor, with a common ratio `λ = c_S / c_R`.
The inserted-site scalar extraction
(`component_eq_gaugeVertex_of_twoBlockProportional`) turns each pair into the
per-vertex gauge relation, so the scalar condition follows directly from those
proportionalities. -/

/-- **The torus scalar condition from the per-vertex two-block proportionalities.**

At every torus vertex `v`, suppose a region `R_v` (not containing `v`) is supplied
together with the two-block scalar proportionalities of the blocked weights of `A` and
of the gauge-absorbed tensor `applyGauge B X` over `R_v` and over `insert v R_v`, with
nonzero ratios `c_R(v)`, `c_S(v)` whose quotient is the single scalar `λ`, and with the
gauge-absorbed region block injective.  Then under the same state, positive bonds, and a
single comparison region `R` whose block and complement block are blocked-tensor
injective, `λ` raised to the number of torus sites is one.

The proportionalities are the outputs of the `R`/`S` region comparison
`regionComplement_comparison`; the inserted-site scalar extraction
`component_eq_gaugeVertex_of_twoBlockProportional` turns each pair into the per-vertex
gauge relation `A.component v η σ = λ · gaugeVertex B X v (η) σ`, after which the scalar
condition is `lambda_pow_card_torus_eq_one`.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem lambda_pow_card_torus_eq_one_of_twoBlockProportional
    [Fact (1 < width)] [Fact (1 < height)]
    (A B : Tensor (torusGraph width height) d)
    (R : Finset (TorusVertex width height))
    (hRA : RegionBlockedTensorInjective (G := torusGraph width height) A R)
    (hCA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ R))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hAB : SameState A B)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (lam : ℂ)
    (Rv : TorusVertex width height → Finset (TorusVertex width height))
    (cR cS : TorusVertex width height → ℂ)
    (hvR : ∀ v, v ∉ Rv v)
    (hcR : ∀ v, cR v ≠ 0)
    (hlam : ∀ v, cS v / cR v = lam)
    (hCinj : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) (Rv v))
    (hRprop : ∀ v, TwoBlockScalarProportional
      (regionTwoBlock (G := torusGraph width height) A (Rv v))
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) (Rv v)) (cR v))
    (hSprop : ∀ v, TwoBlockScalarProportional
      (regionTwoBlock (G := torusGraph width height) A (insert v (Rv v)))
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd)
        (insert v (Rv v))) (cS v)) :
    lam ^ (width * height) = 1 := by
  refine lambda_pow_card_torus_eq_one A B R hRA hCA hpos hAB X hbd lam ?_
  intro v η σ
  have hv := component_eq_gaugeVertex_of_twoBlockProportional A B (Rv v) (hvR v) hbd X
    (cR v) (cS v) (hcR v) hpos (hCinj v) (hRprop v) (hSprop v) η σ
  rw [hv, hlam v]

/-! ### The scalar condition from the edge-level absorbed equality

The two-block proportionalities of `lambda_pow_card_torus_eq_one_of_twoBlockProportional` are
themselves the output of the region comparison `regionComplement_comparison`, whose load-bearing
`hregion` hypothesis is the absorbed plain region-inserted coefficient equality.  This in turn
follows, at every comparison region, from the bare-edge absorbed equality
(`twoBlockProportional_of_edgeAbsorbed`, the region-independence of the absorbed equality).  This
layer consumes that bare-edge equality directly: at every torus vertex `v`, the comparison at the
one-site-different regions `R_v` and `insert v R_v` delivers, from the edge-level absorbed equality,
the two proportionalities with a common ratio `λ`, after which the scalar condition is
`lambda_pow_card_torus_eq_one_of_twoBlockProportional`. -/

open scoped Classical in
/-- **The torus scalar condition from the edge-level absorbed equality.**

At every torus vertex `v`, suppose a region `R_v` (not containing `v`, with at least one boundary
edge, and likewise for `insert v R_v`) is supplied together with the blocked-tensor injectivity of
`A` and of the reindexed gauge-absorbed tensor over `R_v`, over `insert v R_v`, and over their
complements.  Suppose moreover the bare-edge absorbed equality holds against `applyGauge B X` at
every edge of the torus, and that the proportionality scalars `c_R(v)`, `c_S(v)` produced by the
region comparison have a common quotient `λ`.  Then under the same state, positive bonds, and a
single comparison region `R` whose block and complement block are blocked-tensor injective, `λ`
raised to the number of torus sites is one.

The bare-edge absorbed equality feeds `twoBlockProportional_of_edgeAbsorbed` at `R_v` and at
`insert v R_v`, producing the two two-block scalar proportionalities; their common ratio `λ` and
`lambda_pow_card_torus_eq_one_of_twoBlockProportional` then give the scalar condition.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem lambda_pow_card_torus_eq_one_of_edgeAbsorbed
    [Fact (1 < width)] [Fact (1 < height)]
    (A B : Tensor (torusGraph width height) d)
    (R : Finset (TorusVertex width height))
    (hRA : RegionBlockedTensorInjective (G := torusGraph width height) A R)
    (hCA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ R))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hAB : SameState A B)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (lam : ℂ)
    (Rv : TorusVertex width height → Finset (TorusVertex width height))
    (hvR : ∀ v, v ∉ Rv v)
    (hNeR : ∀ v, Nonempty {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) (Rv v) f})
    (hNeS : ∀ v, Nonempty {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) (insert v (Rv v)) f})
    (hRvA : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height) A (Rv v))
    (hSvA : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height) A
      (insert v (Rv v)))
    (hCRvA : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ Rv v))
    (hCSvA : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ insert v (Rv v)))
    (hRvB : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) (Rv v))
    (hSvB : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) (insert v (Rv v)))
    (hCRvB : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) (Finset.univ \ Rv v))
    (hCSvB : ∀ v, RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd)
      (Finset.univ \ insert v (Rv v)))
    (hedge : ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A e σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N))
    (hlam : ∀ v,
      (twoBlockProportional_of_edgeAbsorbed A B hbd X (insert v (Rv v))
          (hSvA v) (hCSvA v) (hSvB v) (hCSvB v) hedge).choose /
        (twoBlockProportional_of_edgeAbsorbed A B hbd X (Rv v)
          (hRvA v) (hCRvA v) (hRvB v) (hCRvB v) hedge).choose = lam) :
    lam ^ (width * height) = 1 := by
  classical
  refine lambda_pow_card_torus_eq_one_of_twoBlockProportional A B R hRA hCA hpos hAB X hbd lam
    Rv
    (fun v => (twoBlockProportional_of_edgeAbsorbed A B hbd X (Rv v)
      (hRvA v) (hCRvA v) (hRvB v) (hCRvB v) hedge).choose)
    (fun v => (twoBlockProportional_of_edgeAbsorbed A B hbd X (insert v (Rv v))
      (hSvA v) (hCSvA v) (hSvB v) (hCSvB v) hedge).choose)
    hvR
    (fun v => (twoBlockProportional_of_edgeAbsorbed A B hbd X (Rv v)
      (hRvA v) (hCRvA v) (hRvB v) (hCRvB v) hedge).choose_spec.1)
    hlam
    (fun v => hRvB v)
    (fun v => (twoBlockProportional_of_edgeAbsorbed A B hbd X (Rv v)
      (hRvA v) (hCRvA v) (hRvB v) (hCRvB v) hedge).choose_spec.2)
    (fun v => (twoBlockProportional_of_edgeAbsorbed A B hbd X (insert v (Rv v))
      (hSvA v) (hCSvA v) (hSvB v) (hCSvB v) hedge).choose_spec.2)

end PEPS
end TNLean
