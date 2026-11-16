/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciActionTrees
import TNLean.MPS.MPDO.BoundaryActionLMatrix

/-!
# The L-symbol of the Fibonacci regular module equals its F-symbol up to gauge

**Source.** Garre-Rubio, Lootens and Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex`:
* lines 517–546, `eq:F_symbol2` and `1Fsymbol`: the L-symbol
  `(L_{abx}^y)_{c,kμ}^{z,ij}` is the normalized contraction of the sequential action tree
  `x → z → y` (action of `b`, then of `a`) against the fusion-then-action tree
  (`a b → c`, then `c · x → y`);
* lines 593–605: the action tensors are fixed up to invertible changes of basis of the
  multiplicity spaces, under which `L` becomes
  `X_{az}^y X_{bx}^z \hat{X}_{cx}^y \hat{Y}_{ab}^c L`, and in the regular module, with one state block
  `x_a` for every operator block `a` and action `a · x_b = ∑_c N_{ab}^c x_c`, "the L-symbols
  are equal to the F-symbols", which is read up to this gauge freedom;
* lines 1991–1993: for the Fibonacci algebra this regular module, with
  `τ · x_1 = x_τ` and `τ · x_τ = x_1 + x_τ`, is the only realization.

The F-symbols are those of Bultinck et al. (arXiv:1511.08090), Appendix D.1.1,
`References/1511.08090/AnyonsPEPS.tex` lines 1245–1257, recorded in
`Examples/FibonacciFSymbol.lean`: `F^{abc}_d` with entries indexed by the intermediate labels
`e` of `a b` and `f` of `b c`, equal to `[[1/φ, 1/√φ], [1/√φ, -1/φ]]` on the block
`F^{τττ}_τ` and to the admissibility deltas elsewhere.

**Formalized here.** For the exact fusion and action trees of
`Examples/FibonacciActionTrees.lean`, the L matrix `L_{ττx}^y` is computed at every pair of
state blocks `x, y`: it is `1` on the three one-dimensional blocks and
`[[1/φ, φ], [1/φ², -1/φ]]` on the block `x = y = x_τ`. With multiplicity-gauge scalars
`X_{ax}^y ∈ {1, φ^{3/2}}` and trivial fusion gauge, it is the source's gauge transform of
`F^{ττx}_y`, with the sequential label `z` in the place of `f` and the fusion label `c` in the
place of `e`. Both matrices have the gauge-invariant cross ratio `-1/φ` on the block
`x = y = x_τ`. The multiplicity spaces of this module are one-dimensional, so the gauge
matrices of lines 593–605 are nonzero scalars and the hatted gauge `\hat{X}` is the inverse of `X`.

The comparison is made for one choice of exact trees. Independence of the choice is the joint
gauge law `MPOTensor.exists_actionLMatrix_fusionFMatrix_regauge_of_isInjective`, which asks
for injective blocks; the Fibonacci blocks are normal but not injective at length one, so this
file does not assert it.

**Local fix (provenance):** the operator blocks and the two states are those of
`Examples/Fibonacci.lean` and `Examples/FibonacciAction.lean`, whose entries the source does
not print; documented in `docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main definitions

* `FibonacciCompression.fibLGolden`: the L-symbol values over `ℤ[σ]`.
* `FibonacciCompression.fibLGauge`: the multiplicity-gauge scalars.

## Main statements

* `FibonacciCompression.fib_actionLMatrix_eq`: the computed L matrix.
* `FibonacciCompression.fib_actionLMatrix_eq_gauge_fSymbol`: the L-symbol is the gauge
  transform of the F-symbol.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor


/-- The sequential analysis tree `x → z → y` over the golden integers, in the
fusion-then-action bond coordinates, as in `MPOTensor.sequentialActionAnalysis`. -/
def fibSequentialAnalysisGolden (a b x z y : Fin 2) :
    Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) GoldenInt :=
  (fibActAnalysisGolden a z y * idKronR (fibBlockDim a) (fibActAnalysisGolden b x z)) *
    mulTensorAssocInvMatrixR (fibBlockDim a) (fibBlockDim b) (fibNimDim x)

/-- The fusion-then-action synthesis tree `a b → c`, `c · x → y` over the golden integers, as
in `MPOTensor.fusionThenActionSynthesis`. -/
def fibFusionActionSynthesisGolden (a b x c y : Fin 2) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) (Fin (fibNimDim y)) GoldenInt :=
  kronIdR (fibFusionSynthesisGolden a b c) (fibNimDim x) * fibActSynthesisGolden c x y

/-- The values of the L-symbol `(L_{ττx}^y)_c^z` over the golden integers, written
`⟨c₀, c₁, c₂, c₃⟩ = c₀ + c₁ σ + c₂ σ² + c₃ σ³` with `σ = φ^{-1/2}`: `1` on the three
one-dimensional blocks, and `σ² = 1/φ`, `1 + σ² = φ`, `1 - σ² = 1/φ²` and `-σ² = -1/φ` on the
block `x = y = x_τ`; `0` at inadmissible labels. -/
def fibLGolden : Fin 2 → Fin 2 → Fin 2 → Fin 2 → GoldenInt
  | 0, 0, 1, 0 => ⟨1, 0, 0, 0⟩
  | 0, 1, 1, 1 => ⟨1, 0, 0, 0⟩
  | 1, 0, 1, 1 => ⟨1, 0, 0, 0⟩
  | 1, 1, 0, 0 => ⟨0, 0, 1, 0⟩
  | 1, 1, 0, 1 => ⟨1, 0, 1, 0⟩
  | 1, 1, 1, 0 => ⟨1, 0, -1, 0⟩
  | 1, 1, 1, 1 => ⟨0, 0, -1, 0⟩
  | _, _, _, _ => 0

set_option maxRecDepth 8000 in
/-- The unnormalized contractions of the two trees are the L values times the bond dimension of
the final state block. -/
theorem trace_fibSequentialAnalysisGolden_mul (x y z c : Fin 2) :
    (fibSequentialAnalysisGolden 1 1 x z y * fibFusionActionSynthesisGolden 1 1 x c y).trace =
      (fibNimDim y : GoldenInt) * fibLGolden x y z c := by
  revert x y z c
  decide +kernel

/-- **The L-symbol of the Fibonacci regular module.** The normalized contraction of the exact
trees of `Examples/FibonacciActionTrees.lean` is the recorded value `fibLGolden x y z c`.
Source: arXiv:2203.12563, `1Fsymbol`, lines 517–546. -/
theorem fib_actionLMatrix_eq (x y : Fin 2)
    (p : SequentialActionMultiplicity fibMult 1 1 x y)
    (q : FusionActionMultiplicity fibMult fibMult
      1 1 x y) :
    actionLMatrix (χ := fibBlockDim) (D := fibNimDim) fibFusionSynthesis fibActAnalysis
        fibActSynthesis 1 1 x y p q =
      goldenToComplex (fibLGolden x y p.1 q.1) := by
  obtain ⟨z, i, j⟩ := p
  obtain ⟨c, k, μ⟩ := q
  have hseq : sequentialActionAnalysis (χ := fibBlockDim) (D := fibNimDim) fibActAnalysis 1 1 x
      (sequentialActionPathEquiv 1 1 x ⟨y, ⟨z, i, j⟩⟩) =
        complexOfGolden (fibSequentialAnalysisGolden 1 1 x z y) := by
    rw [fibSequentialAnalysisGolden, complexOfGolden]
    erw [complexOfRing_mul, complexOfRing_mul, complexOfRing_idKronR,
      complexOfRing_mulTensorAssocInvMatrixR]
    rfl
  have hsyn : fusionThenActionSynthesis (χ := fibBlockDim) (D := fibNimDim) fibFusionSynthesis
      fibActSynthesis 1 1 x (fusionActionPathEquiv 1 1 x ⟨y, ⟨c, k, μ⟩⟩) =
        complexOfGolden (fibFusionActionSynthesisGolden 1 1 x c y) := by
    rw [fibFusionActionSynthesisGolden, complexOfGolden]
    erw [complexOfRing_mul, complexOfRing_kronIdR]
    rfl
  have hD : (fibNimDim y : ℂ) ≠ 0 := by fin_cases y <;> norm_num [fibNimDim]
  unfold actionLMatrix
  rw [hseq, hsyn]
  erw [← complexOfGolden_mul]
  erw [trace_complexOfRing, trace_fibSequentialAnalysisGolden_mul]
  rw [map_mul, map_natCast, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]

/-- The multiplicity-gauge scalars `X_{ax}^y` over the golden integers: `φ^{3/2} = 2σ + σ³` on
`1 · x_1 → x_1`, `1 · x_τ → x_τ` and `τ · x_1 → x_τ`, and `1` otherwise. -/
def fibLGaugeGolden : Fin 2 → Fin 2 → Fin 2 → GoldenInt
  | 0, 0, 0 => ⟨0, 2, 0, 1⟩
  | 0, 1, 1 => ⟨0, 2, 0, 1⟩
  | 1, 0, 1 => ⟨0, 2, 0, 1⟩
  | _, _, _ => 1

/-- The inverses of the gauge scalars: `φ^{-3/2} = σ³`. -/
def fibLGaugeInvGolden : Fin 2 → Fin 2 → Fin 2 → GoldenInt
  | 0, 0, 0 => sigma ^ 3
  | 0, 1, 1 => sigma ^ 3
  | 1, 0, 1 => sigma ^ 3
  | _, _, _ => 1

theorem fibLGaugeGolden_mul_inv (a x y : Fin 2) :
    fibLGaugeGolden a x y * fibLGaugeInvGolden a x y = 1 := by
  revert a x y
  decide +kernel

/-- The complex multiplicity-gauge scalars `X_{ax}^y`. -/
def fibLGauge (a x y : Fin 2) : ℂ := goldenToComplex (fibLGaugeGolden a x y)

theorem fibLGauge_inv (a x y : Fin 2) :
    (fibLGauge a x y)⁻¹ = goldenToComplex (fibLGaugeInvGolden a x y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [fibLGauge, ← map_mul, fibLGaugeGolden_mul_inv, map_one]

/-- At admissible labels, the L values times the hatted gauge are the gauged F-symbol, over
the golden integers. -/
theorem fibLGolden_eq_gauge_fSymbol (x y z c : Fin 2) (hzy : fibMult 1 z y ≠ 0)
    (hxz : fibMult 1 x z ≠ 0) (hxy : fibMult c x y ≠ 0) (hc : fibMult 1 1 c ≠ 0) :
    fibLGolden x y z c =
      fibLGaugeGolden 1 z y * fibLGaugeGolden 1 x z * fibLGaugeInvGolden c x y *
        fibFSymbolGolden 1 1 x y c z := by
  revert x y z c
  decide +kernel

/-- **The L-symbol of the Fibonacci regular module is its F-symbol up to gauge.** For the
exact fusion and action trees of the two-block realization, every entry of the L-symbol
`(L_{ττx}^y)_{c,kμ}^{z,ij}` is the source's gauge transform
`X_{τz}^y X_{τx}^z X̂_{cx}^y F^{ττx}_y` of the F-symbol with the fusion label `c` in the place
of `e` and the sequential label `z` in the place of `f`, where the multiplicity gauges are
the scalars `fibLGauge`, the hatted gauge is the inverse, and the fusion gauge is trivial.
Source: arXiv:2203.12563, lines 593–605 ("the L-symbols are equal to the F-symbols") and
lines 1991–1993; arXiv:1511.08090, `AnyonsPEPS.tex` lines 1245–1257. -/
theorem fib_actionLMatrix_eq_gauge_fSymbol (x y : Fin 2)
    (p : SequentialActionMultiplicity fibMult 1 1 x y)
    (q : FusionActionMultiplicity fibMult fibMult
      1 1 x y) :
    actionLMatrix (χ := fibBlockDim) (D := fibNimDim) fibFusionSynthesis fibActAnalysis
        fibActSynthesis 1 1 x y p q =
      fibLGauge 1 p.1 y * fibLGauge 1 x p.1 * (fibLGauge q.1 x y)⁻¹ *
        goldenToComplex (fibFSymbolGolden 1 1 x y q.1 p.1) := by
  obtain ⟨z, i, j⟩ := p
  obtain ⟨c, k, μ⟩ := q
  rw [fib_actionLMatrix_eq, fibLGauge_inv, fibLGauge, fibLGauge, ← map_mul, ← map_mul,
    ← map_mul]
  exact congrArg goldenToComplex (fibLGolden_eq_gauge_fSymbol x y z c
    (Fin.pos i).ne' (Fin.pos j).ne' (Fin.pos k).ne' (Fin.pos μ).ne')

end FibonacciCompression
