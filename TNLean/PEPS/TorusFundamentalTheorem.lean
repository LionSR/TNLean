import TNLean.PEPS.RegionScalarCondition
import TNLean.PEPS.TorusWitnessCapstone
import TNLean.PEPS.RegionBlock.ScalarExtraction

/-!
# The normal PEPS Fundamental Theorem on the discrete torus

This file assembles the scalar condition of the translationally invariant normal
PEPS Fundamental Theorem on the discrete torus (arXiv:1804.04964, Section 3,
Theorem 3, lines 1453--1471 of `Papers/1804.04964/paper_normal.tex`).

The source theorem concludes that two normal translationally invariant PEPS that
generate the same state on an `n × m` region with `n, m ≥ 7` are related by a
gauge transformation `B = λ · (X, Y\text{-action on } A)` with `λ^{n·m} = 1` and
`X, Y` invertible, unique up to a multiplicative constant. The orientation-uniform
gauge family `(X, Y)` on the torus is produced unconditionally from the rectangle
injectivity hypotheses (`isTorusOrientationUniformGaugeFamilyModScalar_torus_rectangle`).
The final region comparison \(A \propto \widetilde B\) of the `R`/`S` regions gives the per-vertex
relation `A_v = λ · gaugeVertex B Z v`; this file consumes that relation and proves
the scalar condition `λ^{width·height} = 1`.

The per-vertex relation is the output of the `R`/`S` region comparison
(`RegionComplementComparison.regionComplement_comparison`); this capstone takes it
as a hypothesis, exactly as the square-lattice
`fundamentalTheorem_normalSquarePEPS` does, and discharges the scalar condition on
top of it. The nonvanishing state coefficient needed for the scalar cancellation
is supplied by region injectivity of a single comparison region and its complement
(`prod_perVertexScalar_eq_one_of_regionInjective`), so no vertex injectivity of `A`
is assumed: only injectivity after blocking, as the source requires.

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

/-! ### The torus Fundamental Theorem

The capstone gathers the two layers of Theorem 3 on the torus: the
orientation-uniform gauge family `(X, Y)` produced from the rectangle injectivity
hypotheses, and the scalar condition `λ^{width·height} = 1` produced from the
per-vertex comparison relation. -/

/-- **Normal PEPS Fundamental Theorem on the torus.**

For a translation-invariant pair `A`, `B` on the discrete torus with matched bond
dimensions, positive bonds, the same state, and both satisfying the
rectangular-injectivity hypotheses with union closure, there is an
orientation-uniform-up-to-scalar gauge family `X` (the source's horizontal and
vertical matrices, the same on every edge of each orientation class), and for any
single scalar `λ` whose gauge action relates `A` to `B` at every vertex against
that family --- the output of the `R`/`S` region comparison
\(A \propto \widetilde B\) --- and any
comparison region `R` whose block and complement block over `A` are blocked-tensor
injective, `λ` satisfies the scalar condition `λ^{width·height} = 1`.

This is the torus form of Theorem 3 (arXiv:1804.04964, Section 3, lines 1453--1471
of `Papers/1804.04964/paper_normal.tex`): `B = λ · (X, Y\text{-action on } A)` with
`λ^{n·m} = 1`. The gauge family is produced unconditionally from the rectangle
hypotheses (`isTorusOrientationUniformGaugeFamilyModScalar_torus_rectangle`). The
per-vertex relation `hPV` is the conditional input, the comparison output
\(A \propto \widetilde B\),
exactly as in the square-lattice `fundamentalTheorem_normalSquarePEPS`; the scalar
condition is discharged on top of it by `lambda_pow_card_torus_eq_one`, whose
nonvanishing state coefficient comes from region injectivity rather than vertex
injectivity.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalTorusPEPS [Fact (1 < width)] [Fact (1 < height)]
    {A B : Tensor (torusGraph width height) d} {xhStart yhStart xvStart yvStart : ℕ}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hxh0 : 2 ≤ xhStart) (hyh0 : 1 ≤ yhStart)
    (hxhw : xhStart + 5 < width) (hyhh : yhStart + 5 < height)
    (hxhw' : xhStart + 7 ≤ width) (hyhh' : yhStart + 7 ≤ height)
    (hxv0 : 2 ≤ xvStart) (hyv0 : 2 ≤ yvStart)
    (hxvw : xvStart + 5 < width) (hyvh : yvStart + 5 < height)
    (hxvw' : xvStart + 7 ≤ width) (hyvh' : yvStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (R : Finset (TorusVertex width height))
    (hRA : RegionBlockedTensorInjective (G := torusGraph width height) A R)
    (hCA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ R)) :
    ∃ (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ),
      IsTorusOrientationUniformGaugeFamilyModScalar
          (torusUniformBondDim_of_translationInvariant hB) X ∧
        ∀ (lam : ℂ),
          (∀ (v : TorusVertex width height)
            (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
            (σ : Fin d),
            A.component v η σ =
              lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ) →
            lam ^ (width * height) = 1 := by
  obtain ⟨X, hX⟩ := isTorusOrientationUniformGaugeFamilyModScalar_torus_rectangle
    hA hB hAr hBr hUA hUB hxh0 hyh0 hxhw hyhh hxhw' hyhh' hxv0 hyv0 hxvw hyvh hxvw' hyvh'
    hbond hAB hd hposA hposB
  refine ⟨X, hX, fun lam hPV => ?_⟩
  exact lambda_pow_card_torus_eq_one A B R hRA hCA hposA hAB X hbond lam hPV

end PEPS
end TNLean
