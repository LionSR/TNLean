import TNLean.PEPS.NormalSquareTIAbsorption
import TNLean.PEPS.RegionComplementComparison

/-!
# Square-lattice normal PEPS Fundamental Theorem (translation-invariant)

This file assembles the translationally invariant normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`). The proof has four ingredients, built in the
preceding files:

1. the per-edge gauges from the edge blocking reduce, by translation invariance, to
   one horizontal matrix `X` and one vertical matrix `Y`
   (`NormalSquareTI.IsOrientationUniformGaugeFamily`);
2. those gauges are absorbed into the second tensor, giving `B̃`
   (`NormalSquareTIAbsorption.tiAbsorb`, `tiNormalGaugeAbsorption`);
3. the one-site-different injective regions `R` and `S` give `A_R ∝ B̃_R` and
   `A_S ∝ B̃_S` (`RegionComplementComparison.regionComplement_comparison`), whose
   combination is `A ∝ B̃`;
4. the proportionality constant `λ` satisfies `λ^{nm} = 1` (Theorem 3).

The per-edge gauge family produced by the edge blocking is the open kernel piece of
the normal route (remaining obligation 5 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`); this file is therefore
**conditional** on that gauge family, taken with the shape it will deliver. The
scalar condition `λ^{nm} = 1` is the square-lattice content of remaining obligation
7. The source's Theorem 3 proof likewise consumes the output of its
`lem:inj_isomorph` and packages the final scalar condition separately.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Theorem 3,
  lines 1449--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height : ℕ} {d : ℕ}

/-! ### The scalar condition `λ^{nm} = 1`

In the translationally invariant case all per-vertex scalars are a single `λ`, so
their product over the `width × height` lattice is `λ` raised to the number of
vertices. The injective theorem forces that product to be one
(`prod_perVertexScalar_eq_one`), giving `λ^{width·height} = 1`. -/

/-- The number of vertices of the finite `width × height` square lattice. -/
theorem card_squareLatticeVertex :
    Fintype.card (SquareLatticeVertex width height) = width * height := by
  simp [SquareLatticeVertex, Fintype.card_prod]

/-- **The scalar condition `λ^{nm} = 1`.**

If a single scalar `λ` relates `A` to the gauge action of the absorbed second
tensor at every vertex (the translationally invariant per-vertex relation, all
`c_v` equal to `λ`), then `λ` raised to the number of lattice sites is one:
`λ^{width·height} = 1`.

This is the square-lattice scalar condition of arXiv:1804.04964, Section 3,
Theorem 3 (line 1471: `λ^{n·m} = 1`). It follows from
`prod_perVertexScalar_eq_one`: under translation invariance the per-vertex scalars
are all equal, so their product is `λ^{width·height}`.

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem lambda_pow_card_eq_one
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : IsVertexInjective A)
    (hpos : ∀ e : Edge (squareLatticeGraph width height), 0 < A.bondDim e)
    (hAB : SameState A B)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (lam : ℂ)
    (hPV : ∀ (v : SquareLatticeVertex width height)
      (η : (ie : IncidentEdge (squareLatticeGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B Z v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    lam ^ (width * height) = 1 := by
  have hprod := prod_perVertexScalar_eq_one A B hA hpos hAB Z hbd (fun _ => lam) hPV
  rw [Finset.prod_const, Finset.card_univ, card_squareLatticeVertex] at hprod
  exact hprod

/-! ### The square-lattice Fundamental Theorem skeleton

The conditional theorem records the full structure of the translationally invariant
proof of Theorem 3 with the per-edge gauge family and the per-vertex single-scalar
relation as the named inputs. -/

/-- **Translation-invariant normal PEPS Fundamental Theorem (square lattice),
conditional on the per-edge gauge family.**

Given:

* a tensor `A` and an orientation-uniform gauge absorption datum producing `B̃`
  (the reduction of the per-edge gauges to one horizontal and one vertical matrix,
  absorbed into the second tensor) --- `huni` records the uniform bond dimensions of
  `B` and `dataAbs` the orientation-uniform gauge with the post-absorption
  edge-insertion equality;
* a single scalar `λ` whose gauge action relates `A` to the absorbed tensor at every
  vertex (the output of the `R`/`S` region comparison, `A ∝ B̃`),

then `λ` satisfies the scalar condition `λ^{width·height} = 1`.

The orientation-uniform gauge family and the per-vertex single-scalar relation are
the conditional kernel inputs (open remaining obligations 5--6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`); the scalar condition is the
square-lattice content of obligation 7. This theorem records the top-down
assembly: with the kernel inputs in hand the scalar condition follows.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalSquarePEPS
    (A B : Tensor (squareLatticeGraph width height) d) {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim B.bondDim Dh Dv)
    (hA : IsVertexInjective A)
    (hpos : ∀ e : Edge (squareLatticeGraph width height), 0 < A.bondDim e)
    (hAB : SameState A B)
    (hbd : A.bondDim = B.bondDim)
    (dataAbs : TINormalGaugeAbsorptionData A B huni)
    (lam : ℂ)
    (hPV : ∀ (v : SquareLatticeVertex width height)
      (η : (ie : IncidentEdge (squareLatticeGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B dataAbs.gauge v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    lam ^ (width * height) = 1 :=
  lambda_pow_card_eq_one A B hA hpos hAB dataAbs.gauge hbd lam hPV

end PEPS
end TNLean
