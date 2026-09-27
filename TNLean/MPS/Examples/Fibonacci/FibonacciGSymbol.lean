/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.Examples.Fibonacci.FibonacciDimension
import TNLean.MPS.Examples.Fibonacci.FibonacciFSymbol
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.Symmetry.MPOSymmetry.Similarity

/-!
# Fibonacci string-net: the source's G-symbol tensor and the F-symbol blocks

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Section 6.2 ("String-nets") and Appendix D.1.1,
`References/1511.08090/AnyonsPEPS.tex` lines 1044–1050 and 1257–1268: the string-net operator
tensor is drawn (figure file `StringNetMPO_RHS.pdf`) as the crossing of the horizontal operator
line `f` with a vertical edge line `e`, with corner plaquettes `b` (upper left), `a` (upper
right), `c` (lower left) and `d` (lower right), and entry `G^{abc}_{def} √(v_a v_b v_c v_d)`, where
`G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)` and `v_i = √d_i`; after removing zero rows and columns
the blocks `B_1`, `B_τ` have bond dimensions `2` and `3` and satisfy the Fibonacci fusion rules.
Review: arXiv:2011.12127, Appendix A, "The MPO for the Fibonacci model"
(`Papers/2011.12127/TN-Review-main.tex` lines 2613–2625): the operator tensor (figure file
`fig3_mpo.pdf`, plaquettes `A` upper left, `B` upper right, `C` lower left, `D` lower right,
vertical line `α`, operator line `a`) has entry `(1/√(d_A d_D)) (F^{aCα}_B)^{D}_{A}`; lines 1309
and 1341 state the fusion rules `O_a O_b = ∑_c N_{ab}^c O_c` for the operators of this tensor.

**Formalized here.** The source's tensor over the physical letters (plaquette, edge label), and
the review's tensor at the edge label `τ`, both over `ℂ` with the factors `v_a = d_a^{1/2}`.
A diagonal bond similarity `h(x', x) = (v_{x'}/v_x)^{1/2}` carries every letter of the source's
tensor to the F-symbol blocks `fibOne`, `fibTau` extended to the four letters: at edge label `τ`
to their letters, at edge label `1`, where the plaquettes on both sides of the edge coincide, to
the diagonal matrix units `E_{pp}` at the bond letter `p`. So the periodic operators are equal at
every length. The four compression data of the products of the F-symbol blocks extend to the
sixteen letters of the extended products with the same gauges, block upper triangular with a
nonzero nilpotent remainder at edge label `1`, and the source's blocks satisfy the Fibonacci
fusion rules on the full alphabet (`isMPOFusionAlgebra_fibStringNetTensor`). For the review's
prefactor the periodic operator is the congruence `O_a^{rev} = W^{-1/2} O_a W^{-1/2}`,
`W = diag ∏_k d_{x_k}`, of the F-symbol operator `O_a`; it fails the fusion rules already at one
site, while the composed operator `O_a^{rev} W = W^{-1/2} O_a W^{1/2}`, a similarity transform of
`O_a`, satisfies them.

**Local fix (review normalization):** read literally in the orthonormal basis of plaquette
configurations, the review's prefactor `1/√(d_A d_D)` gives operators that contradict the fusion
rules the review states for them (`TN-Review-main.tex` lines 1309, 1341); the fusion rules hold
for the composed operators `O_a^{rev} W = W^{-1/2} O_a W^{1/2}`, which are similar to `O_a`.
The review's printed selection rule for
the F-symbols (line 2623) is garbled, and the F-symbols used are those of the source,
`fibFSymbolGolden`. Documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

The physical legs of the drawn tensor are double lines carrying the plaquette labels on both
sides of the vertical line. On a periodic chain the upper-right plaquette `a` of a site is the
upper-left plaquette of the next site, and the bond indices `(b, f, c)`, `(a, f, d)` identify
them, so a physical letter records the left plaquette and the edge label; a bond letter records
the pair of plaquettes above and below the operator line, restricted to the admissible pairs
(`N_{bc}^f > 0`), which is the removal of zero rows and columns of line 1266.

## Main definitions

* `FibonacciCompression.fibLoopFactor`: the closed-loop factors `v_a = √d_a`.
* `FibonacciCompression.fibGSymbol`: the complex G-symbols `G^{abc}_{def}`.
* `FibonacciCompression.fibStringNetTensor`: the source's tensor `G^{abc}_{def} √(v_a v_b v_c v_d)`
  on the letters (plaquette, edge label).
* `FibonacciCompression.fibStringNetEdgeTau`: its letters at edge label `τ`.
* `FibonacciCompression.fibBlockFull`: the F-symbol blocks extended to the four letters, with
  the diagonal matrix units at edge label `1`.
* `FibonacciCompression.fibReviewTensor`: the review's tensor `(1/√(d_A d_D)) F` at edge label `τ`.

## Main results

* `FibonacciCompression.fibGSymbolGolden_tetrahedral`: `G^{abc}_{def} = G^{fce}_{abd}`.
* `FibonacciCompression.fibStringNetEdgeTau_conj`: the diagonal bond similarity to the F-symbol
  blocks.
* `FibonacciCompression.mpo_fibStringNetTensor_edgeTau`: on edge label `τ` the source's periodic
  operators are those of the F-symbol blocks.
* `FibonacciCompression.fibStringNetTensor_conj`, `FibonacciCompression.mpo_fibStringNetTensor`:
  the diagonal bond similarity to the extended blocks on the full alphabet.
* `FibonacciCompression.isMPOFusionAlgebra_fibBlockFull`: the extended blocks satisfy the
  Fibonacci fusion rules.
* `FibonacciCompression.isMPOFusionAlgebra_fibStringNetTensor`: the source's blocks form a fusion
  algebra with the Fibonacci fusion rules (arXiv:1511.08090, `AnyonsPEPS.tex` line 1268).
* `FibonacciCompression.mpo_fibReviewTensor`: the review's operator is `W^{-1/2} O_a W^{-1/2}`.
* `FibonacciCompression.not_isMPOFusionAlgebra_fibReviewTensor`: the review's operators do not
  satisfy the fusion rules.
* `FibonacciCompression.isMPOFusionAlgebra_fibReviewWeightedTensor`: the operators `O_a^{rev} W` do.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-! ### Closed-loop factors and G-symbols -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1049–1050 and 1257–1260. The closed-loop
factors `v_a = √d_a` of the quantum dimensions `d_1 = 1`, `d_τ = φ` (`fibDim`). -/
def fibLoopFactor (a : Fin 2) : ℝ := Real.sqrt (fibDim a)

/-- The square root `v_a^{1/2} = d_a^{1/4}` of the closed-loop factor. -/
def fibLoopFactorSqrt (a : Fin 2) : ℝ := Real.sqrt (fibLoopFactor a)

theorem fibLoopFactor_pos (a : Fin 2) : 0 < fibLoopFactor a :=
  Real.sqrt_pos.2 (fibDim_pos a)

theorem fibLoopFactorSqrt_pos (a : Fin 2) : 0 < fibLoopFactorSqrt a :=
  Real.sqrt_pos.2 (fibLoopFactor_pos a)

theorem fibLoopFactor_eq_sq (a : Fin 2) : fibLoopFactor a = fibLoopFactorSqrt a ^ 2 :=
  (Real.sq_sqrt (Real.sqrt_nonneg _)).symm

/-- `√(v_a v_b v_c v_d)` is the product of the square roots of the four factors. -/
theorem sqrt_fibLoopFactor_mul (a b c e : Fin 2) :
    Real.sqrt (fibLoopFactor a * fibLoopFactor b * fibLoopFactor c * fibLoopFactor e) =
      fibLoopFactorSqrt a * fibLoopFactorSqrt b * fibLoopFactorSqrt c * fibLoopFactorSqrt e := by
  have h : ∀ x, 0 ≤ fibLoopFactor x := fun x => Real.sqrt_nonneg _
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (h a) (h b)) (h c)),
    Real.sqrt_mul (mul_nonneg (h a) (h b)), Real.sqrt_mul (h a)]
  rfl

/-- Bridge: the golden integers `1/v_a` of `fibQuantumDimInvSqrt` are the inverse closed-loop
factors. -/
theorem goldenToComplex_fibQuantumDimInvSqrt (a : Fin 2) :
    goldenToComplex (fibQuantumDimInvSqrt a) = (((fibLoopFactor a)⁻¹ : ℝ) : ℂ) := by
  fin_cases a
  · simp [fibQuantumDimInvSqrt, fibLoopFactor, fibDim]
  · simp [fibQuantumDimInvSqrt, fibLoopFactor, fibDim, goldenSigmaComplex,
      goldenSigmaReal_eq_inv_sqrt_goldenRatio]

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1257–1260, eq. `eq:Gsymbol`. The complex
G-symbols `G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)`. -/
def fibGSymbol (a b c d e f : Fin 2) : ℂ := goldenToComplex (fibGSymbolGolden a b c d e f)

/-- The Fibonacci G-symbols have the tetrahedral symmetry `G^{abc}_{def} = G^{fce}_{abd}`. -/
theorem fibGSymbolGolden_tetrahedral :
    ∀ a b c d e f : Fin 2, fibGSymbolGolden a b c d e f = fibGSymbolGolden f c e a b d := by
  decide

/-! ### The source's tensor -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1266–1267. The bond letters of the block
labelled `f`: the pairs `(u, l)` of plaquettes above and below the operator line with
`N_{ul}^f > 0`, namely `(1, 1)`, `(τ, τ)` for `f = 1` and the letters `fibLetter` for `f = τ`. -/
def fibBondLetter : (f : Fin 2) → Fin (fibBlockDim f) → Fin 2 × Fin 2
  | 0 => ![(0, 0), (1, 1)]
  | 1 => fibLetter

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1266 (eq. `StringnetMPO`, figure
`StringNetMPO_RHS.pdf`) and line 1040: each physical leg of the string-net operator tensor carries
the label of the plaquette it bounds and the label of the edge the operator line crosses, both in
`{1, τ}`; reading a physical letter as this pair follows the figure. The ordering
`(1, 1)`, `(1, τ)`, `(τ, 1)`, `(τ, τ)` of the pairs on `Fin 4` is a convention of this
development. -/
def fibSiteLetter : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

/-- The physical letter with plaquette `x` and edge label `τ`. -/
def fibEdgeTauLetter : Fin 2 → Fin 4 := ![1, 3]

theorem fibSiteLetter_fibEdgeTauLetter (x : Fin 2) :
    fibSiteLetter (fibEdgeTauLetter x) = (x, 1) := by
  fin_cases x <;> rfl

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1044–1050 and 1262–1265 (figure file
`StringNetMPO_RHS.pdf`). The string-net operator tensor of the block `f`: at the outgoing letter
`(b, e')` (upper-left plaquette, upper edge label), the incoming letter `(c, e)` (lower-left
plaquette, lower edge label), the left bond letter `p` and the right bond letter `q = (a, d)`
(upper-right and lower-right plaquettes), its entry is `G^{abc}_{def} √(v_a v_b v_c v_d)` when the
edge label passes through, `e' = e`, and `p = (b, c)`, and zero otherwise. -/
def fibStringNetTensor (f : Fin 2) : MPOTensor 4 (fibBlockDim f) := fun i j =>
  Matrix.of fun p q =>
    if (fibSiteLetter i).2 = (fibSiteLetter j).2 ∧
        fibBondLetter f p = ((fibSiteLetter i).1, (fibSiteLetter j).1) then
      fibGSymbol (fibBondLetter f q).1 (fibSiteLetter i).1 (fibSiteLetter j).1
          (fibBondLetter f q).2 (fibSiteLetter j).2 f *
        ((Real.sqrt (fibLoopFactor (fibBondLetter f q).1 * fibLoopFactor (fibSiteLetter i).1 *
          fibLoopFactor (fibSiteLetter j).1 * fibLoopFactor (fibBondLetter f q).2) : ℝ) : ℂ)
    else 0

/-- The letters of the source's tensor `fibStringNetTensor` at edge label `τ`, indexed by the
outgoing and incoming plaquettes `(x', x)`. -/
def fibStringNetEdgeTau (f : Fin 2) : MPOTensor 2 (fibBlockDim f) := fun x' x =>
  fibStringNetTensor f (fibEdgeTauLetter x') (fibEdgeTauLetter x)

theorem fibStringNetEdgeTau_apply (f x' x : Fin 2) (p q : Fin (fibBlockDim f)) :
    fibStringNetEdgeTau f x' x p q =
      if fibBondLetter f p = (x', x) then
        fibGSymbol (fibBondLetter f q).1 x' x (fibBondLetter f q).2 1 f *
          ((Real.sqrt (fibLoopFactor (fibBondLetter f q).1 * fibLoopFactor x' *
            fibLoopFactor x * fibLoopFactor (fibBondLetter f q).2) : ℝ) : ℂ)
      else 0 := by
  simp [fibStringNetEdgeTau, fibStringNetTensor, fibSiteLetter_fibEdgeTauLetter]

/-! ### The F-symbol blocks -/

/-- Bridge: the trivial block `fibOneGolden` is built from the F-symbols in the same way as the
`τ` block (`fibTauGolden_eq_fSymbol`), with the bond letters `(1, 1)`, `(τ, τ)`. -/
theorem fibOneGolden_eq_fSymbol (x' x : Fin 2) :
    fibOneGolden x' x = Matrix.of fun p q : Fin 2 =>
      if fibBondLetter 0 p = (x', x) then
        fibFSymbolGolden 0 x 1 (fibBondLetter 0 q).1 x' (fibBondLetter 0 q).2
      else 0 := by
  fin_cases x' <;> fin_cases x <;> decide

/-- The entrywise form of `fibOneGolden_eq_fSymbol`. -/
theorem fibOneGolden_apply_eq_fSymbol (x' x p q : Fin 2) :
    fibOneGolden x' x p q =
      if fibBondLetter 0 p = (x', x) then
        fibFSymbolGolden 0 x 1 (fibBondLetter 0 q).1 x' (fibBondLetter 0 q).2
      else 0 := by
  rw [fibOneGolden_eq_fSymbol, Matrix.of_apply]

/-- The entrywise form of `fibTauGolden_eq_fSymbol`. -/
theorem fibTauGolden_apply_eq_fSymbol (x' x : Fin 2) (p q : Fin 3) :
    fibTauGolden x' x p q =
      if fibLetter p = (x', x) then
        fibFSymbolGolden 1 x 1 (fibLetter q).1 x' (fibLetter q).2
      else 0 := by
  rw [fibTauGolden_eq_fSymbol, Matrix.of_apply]

/-- Bridge: every entry of both blocks `fibBlock f` is the F-symbol
`[F^{f x τ}_{a}]_{x'}^{d}` at the letter `(x', x)` and the bond letters `p = (x', x)`,
`q = (a, d)`, and zero when `p ≠ (x', x)`. -/
theorem fibBlock_apply_eq_fSymbol (f x' x : Fin 2) (p q : Fin (fibBlockDim f)) :
    fibBlock f x' x p q =
      if fibBondLetter f p = (x', x) then
        goldenToComplex (fibFSymbolGolden f x 1 (fibBondLetter f q).1 x' (fibBondLetter f q).2)
      else 0 := by
  match f, p, q with
  | 0, p, q =>
    exact (congrArg goldenToComplex (fibOneGolden_apply_eq_fSymbol x' x p q)).trans
      ((apply_ite goldenToComplex _ _ _).trans (by rw [map_zero]))
  | 1, p, q =>
    exact (congrArg goldenToComplex (fibTauGolden_apply_eq_fSymbol x' x p q)).trans
      ((apply_ite goldenToComplex _ _ _).trans (by rw [map_zero]; rfl))

/-! ### The bond similarity -/

/-- The diagonal bond gauge `h(u, l) = (v_u / v_l)^{1/2}` of the block `f`. -/
def fibStringNetGauge (f : Fin 2) (p : Fin (fibBlockDim f)) : ℂ :=
  ((fibLoopFactorSqrt (fibBondLetter f p).1 / fibLoopFactorSqrt (fibBondLetter f p).2 : ℝ) : ℂ)

theorem fibStringNetGauge_ne_zero (f : Fin 2) (p : Fin (fibBlockDim f)) :
    fibStringNetGauge f p ≠ 0 :=
  Complex.ofReal_ne_zero.2
    (div_pos (fibLoopFactorSqrt_pos _) (fibLoopFactorSqrt_pos _)).ne'

/-- Bridge: on edge label `τ`, the diagonal bond similarity `h(u, l) = (v_u/v_l)^{1/2}` carries
every letter of the source's tensor (arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1265) to the
letter of the F-symbol block: `h S^{x'x} h⁻¹ = B_f^{x'x}`. The G-symbol is moved to the
F-symbol slots of `fibBlock_eq_fSymbol` by the tetrahedral symmetry, and the factors
`√(v_a v_b v_c v_d)/(v_{x'} v_d)` are absorbed by `h`. -/
theorem fibStringNetEdgeTau_conj (f x' x : Fin 2) :
    Matrix.diagonal (fibStringNetGauge f) * fibStringNetEdgeTau f x' x *
        Matrix.diagonal (fibStringNetGauge f)⁻¹ = fibBlock f x' x := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, fibStringNetEdgeTau_apply,
    fibBlock_apply_eq_fSymbol]
  split_ifs with hp
  · rw [fibGSymbol, fibGSymbolGolden_tetrahedral, fibGSymbolGolden, map_mul, map_mul,
      goldenToComplex_fibQuantumDimInvSqrt, goldenToComplex_fibQuantumDimInvSqrt,
      sqrt_fibLoopFactor_mul, fibLoopFactor_eq_sq, fibLoopFactor_eq_sq]
    simp only [fibStringNetGauge, hp, Pi.inv_apply]
    have h1 := (fibLoopFactorSqrt_pos x').ne'
    have h2 := (fibLoopFactorSqrt_pos x).ne'
    have h3 := (fibLoopFactorSqrt_pos (fibBondLetter f q).1).ne'
    have h4 := (fibLoopFactorSqrt_pos (fibBondLetter f q).2).ne'
    push_cast
    field_simp
    rw [div_eq_iff (by simp [h1, h2, h3, h4])]
    ring
  · simp

/-- Bridge: on edge label `τ` the periodic operators of the source's blocks
(arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1268) equal those of the F-symbol blocks
`fibBlock`, at every length, by `MPOTensor.mpo_eq_of_conj`. -/
theorem mpo_fibStringNetEdgeTau (f : Fin 2) (L : ℕ) :
    mpo (fibStringNetEdgeTau f) L = mpo (fibBlock f) L :=
  mpo_eq_of_diagonal_conj _ (fibStringNetGauge_ne_zero f) (fibStringNetEdgeTau_conj f) L

/-- Bridge: the periodic operator of the source's tensor on the four letters (plaquette, edge
label), restricted to the configurations with every edge label `τ`, is the periodic operator of
the F-symbol block `fibBlock f`. -/
theorem mpo_fibStringNetTensor_edgeTau (f : Fin 2) (L : ℕ) (σ τ : Fin L → Fin 2) :
    mpo (fibStringNetTensor f) L (fibEdgeTauLetter ∘ σ) (fibEdgeTauLetter ∘ τ) =
      mpo (fibBlock f) L σ τ := by
  rw [mpo_apply_comp]
  exact congrFun (congrFun (mpo_fibStringNetEdgeTau f L) σ) τ

/-! ### Both edge labels -/

/-- The physical letter with plaquette `x` and edge label `1`. -/
def fibEdgeOneLetter : Fin 2 → Fin 4 := ![0, 2]

theorem fibSiteLetter_fibEdgeOneLetter (x : Fin 2) :
    fibSiteLetter (fibEdgeOneLetter x) = (x, 0) := by
  fin_cases x <;> rfl

/-- Every physical letter carries the edge label `1` or the edge label `τ`. -/
theorem exists_fibEdgeOneLetter_or_fibEdgeTauLetter (i : Fin 4) :
    (∃ x, i = fibEdgeOneLetter x) ∨ ∃ x, i = fibEdgeTauLetter x := by
  fin_cases i
  exacts [Or.inl ⟨0, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨1, rfl⟩]

/-- A family of letters on the four physical letters (plaquette, edge label) that conserves the
edge label: `T (x', x)` at edge label `τ`, `U (x', x)` at edge label `1`, and zero when the edge
label changes, as for the source's tensor `fibStringNetTensor`. As everywhere in this development
the label `0 : Fin 2` is the trivial label `1` and `1 : Fin 2` is `τ`, so the test
`(fibSiteLetter j).2 = 1` selects the edge label `τ`. -/
def fibEdgeGraded {α : Type*} [Zero α] (T U : Fin 2 → Fin 2 → α) (i j : Fin 4) : α :=
  if (fibSiteLetter i).2 = (fibSiteLetter j).2 then
    if (fibSiteLetter j).2 = 1 then T (fibSiteLetter i).1 (fibSiteLetter j).1
    else U (fibSiteLetter i).1 (fibSiteLetter j).1
  else 0

section EdgeGraded

variable {α : Type*} [Zero α] (T U : Fin 2 → Fin 2 → α)

theorem fibEdgeGraded_edgeTau (x' x : Fin 2) :
    fibEdgeGraded T U (fibEdgeTauLetter x') (fibEdgeTauLetter x) = T x' x := by
  simp [fibEdgeGraded, fibSiteLetter_fibEdgeTauLetter]

theorem fibEdgeGraded_edgeOne (x' x : Fin 2) :
    fibEdgeGraded T U (fibEdgeOneLetter x') (fibEdgeOneLetter x) = U x' x := by
  simp [fibEdgeGraded, fibSiteLetter_fibEdgeOneLetter]

theorem fibEdgeGraded_edgeOne_edgeTau (x' x : Fin 2) :
    fibEdgeGraded T U (fibEdgeOneLetter x') (fibEdgeTauLetter x) = 0 := by
  simp [fibEdgeGraded, fibSiteLetter_fibEdgeOneLetter, fibSiteLetter_fibEdgeTauLetter]

theorem fibEdgeGraded_edgeTau_edgeOne (x' x : Fin 2) :
    fibEdgeGraded T U (fibEdgeTauLetter x') (fibEdgeOneLetter x) = 0 := by
  simp [fibEdgeGraded, fibSiteLetter_fibEdgeOneLetter, fibSiteLetter_fibEdgeTauLetter]

end EdgeGraded

/-- The letter at edge label `1` of a block with bond letters `bond`: the diagonal matrix unit
`E_{pp}` at the bond letter `p = (x', x)`, and zero when `(x', x)` is not a bond letter. -/
def fibEdgeOneGolden {D : ℕ} (bond : Fin D → Fin 2 × Fin 2) (x' x : Fin 2) :
    Matrix (Fin D) (Fin D) GoldenInt :=
  Matrix.diagonal fun p => if bond p = (x', x) then 1 else 0

/-- The trivial block on the four physical letters over `ℤ[σ]`: the letters of `fibOneGolden` at
edge label `τ` and the diagonal matrix units at edge label `1`. -/
def fibOneFullGolden : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) GoldenInt :=
  fibEdgeGraded fibOneGolden (fibEdgeOneGolden (fibBondLetter 0))

/-- The `τ` block on the four physical letters over `ℤ[σ]`. -/
def fibTauFullGolden : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) GoldenInt :=
  fibEdgeGraded fibTauGolden (fibEdgeOneGolden fibLetter)

/-- The trivial block on the four physical letters. -/
def fibOneFull : MPOTensor 4 2 := fun i j => complexOfGolden (fibOneFullGolden i j)

/-- The `τ` block on the four physical letters. -/
def fibTauFull : MPOTensor 4 3 := fun i j => complexOfGolden (fibTauFullGolden i j)

/-- The F-symbol blocks `B_1`, `B_τ` extended to the four physical letters (plaquette, edge
label): at edge label `τ` their letters are those of `fibBlock`, at edge label `1` the diagonal
matrix units `E_{pp}` at the bond letter `p = (x', x)`. -/
def fibBlockFull : (f : Fin 2) → MPOTensor 4 (fibBlockDim f)
  | 0 => fibOneFull
  | 1 => fibTauFull

/-- At edge label `τ` the extended blocks are the F-symbol blocks. -/
theorem fibBlockFull_edgeTau (f x' x : Fin 2) :
    fibBlockFull f (fibEdgeTauLetter x') (fibEdgeTauLetter x) = fibBlock f x' x := by
  fin_cases f
  · exact congrArg complexOfGolden (fibEdgeGraded_edgeTau _ _ x' x)
  · exact congrArg complexOfGolden (fibEdgeGraded_edgeTau _ _ x' x)

/-- The entries of the edge-label-`1` letter `fibEdgeOneGolden`. -/
theorem goldenToComplex_fibEdgeOneGolden {D : ℕ} (bond : Fin D → Fin 2 × Fin 2) (x' x : Fin 2)
    (p q : Fin D) :
    goldenToComplex (fibEdgeOneGolden bond x' x p q) =
      if p = q ∧ bond p = (x', x) then 1 else 0 := by
  rw [fibEdgeOneGolden, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hb : bond p = (x', x) <;> simp [hb]
  · simp [hpq]

/-- The entries of the extended blocks at edge label `1`. -/
theorem fibBlockFull_edgeOne_apply (f x' x : Fin 2) (p q : Fin (fibBlockDim f)) :
    fibBlockFull f (fibEdgeOneLetter x') (fibEdgeOneLetter x) p q =
      if p = q ∧ fibBondLetter f p = (x', x) then 1 else 0 := by
  match f, p, q with
  | 0, p, q =>
    change goldenToComplex (fibOneFullGolden (fibEdgeOneLetter x') (fibEdgeOneLetter x) p q) = _
    rw [fibOneFullGolden, fibEdgeGraded_edgeOne]
    exact goldenToComplex_fibEdgeOneGolden _ x' x p q
  | 1, p, q =>
    change goldenToComplex (fibTauFullGolden (fibEdgeOneLetter x') (fibEdgeOneLetter x) p q) = _
    rw [fibTauFullGolden, fibEdgeGraded_edgeOne]
    exact goldenToComplex_fibEdgeOneGolden _ x' x p q

/-- The extended blocks vanish when the edge label changes. -/
theorem fibBlockFull_edgeOne_edgeTau (f x' x : Fin 2) :
    fibBlockFull f (fibEdgeOneLetter x') (fibEdgeTauLetter x) = 0 := by
  have h0 : ∀ D : ℕ, complexOfGolden (0 : Matrix (Fin D) (Fin D) GoldenInt) = 0 := fun _ => by
    ext
    exact map_zero goldenToComplex
  match f with
  | 0 => exact (congrArg complexOfGolden (fibEdgeGraded_edgeOne_edgeTau _ _ x' x)).trans (h0 _)
  | 1 => exact (congrArg complexOfGolden (fibEdgeGraded_edgeOne_edgeTau _ _ x' x)).trans (h0 _)

theorem fibBlockFull_edgeTau_edgeOne (f x' x : Fin 2) :
    fibBlockFull f (fibEdgeTauLetter x') (fibEdgeOneLetter x) = 0 := by
  have h0 : ∀ D : ℕ, complexOfGolden (0 : Matrix (Fin D) (Fin D) GoldenInt) = 0 := fun _ => by
    ext
    exact map_zero goldenToComplex
  match f with
  | 0 => exact (congrArg complexOfGolden (fibEdgeGraded_edgeTau_edgeOne _ _ x' x)).trans (h0 _)
  | 1 => exact (congrArg complexOfGolden (fibEdgeGraded_edgeTau_edgeOne _ _ x' x)).trans (h0 _)

/-- At edge label `1` the G-symbol forces the right bond letter to equal the left one:
`G^{abc}_{d1f} = δ_{(a,d),(b,c)} / (v_b v_c)` when `(b, c)` is a bond letter of the block `f`. -/
theorem fibGSymbolGolden_edgeOne :
    ∀ (f : Fin 2) (p q : Fin (fibBlockDim f)) (b c : Fin 2), fibBondLetter f p = (b, c) →
      fibGSymbolGolden (fibBondLetter f q).1 b c (fibBondLetter f q).2 0 f =
        if q = p then fibQuantumDimInvSqrt b * fibQuantumDimInvSqrt c else 0 := by
  intro f
  fin_cases f <;> decide

/-- Bridge: on edge label `1` the diagonal bond similarity `h` leaves the letters of the source's
tensor unchanged, and they are the diagonal matrix units of `fibBlockFull`:
`G^{bbc}_{c1f} v_b v_c = 1` whenever `(b, c)` is a bond letter of the block `f`. -/
theorem fibStringNetTensor_edgeOne_conj (f b c : Fin 2) :
    Matrix.diagonal (fibStringNetGauge f) *
        fibStringNetTensor f (fibEdgeOneLetter b) (fibEdgeOneLetter c) *
        Matrix.diagonal ((fibStringNetGauge f)⁻¹) =
      fibBlockFull f (fibEdgeOneLetter b) (fibEdgeOneLetter c) := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, fibBlockFull_edgeOne_apply]
  simp only [fibStringNetTensor, Matrix.of_apply, fibSiteLetter_fibEdgeOneLetter, true_and,
    Pi.inv_apply]
  by_cases hp : fibBondLetter f p = (b, c)
  · rw [ite_eq_left hp, fibGSymbol, fibGSymbolGolden_edgeOne f p q b c hp]
    by_cases hq : q = p
    · subst hq
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hp⟩, map_mul, goldenToComplex_fibQuantumDimInvSqrt,
        goldenToComplex_fibQuantumDimInvSqrt, hp, sqrt_fibLoopFactor_mul, fibLoopFactor_eq_sq,
        fibLoopFactor_eq_sq]
      have h1 := (fibLoopFactorSqrt_pos b).ne'
      have h2 := (fibLoopFactorSqrt_pos c).ne'
      have hg := fibStringNetGauge_ne_zero f q
      push_cast
      field_simp
      exact div_self (mul_ne_zero (Complex.ofReal_ne_zero.2 h1) (Complex.ofReal_ne_zero.2 h2))
    · rw [ite_eq_right hq, ite_eq_right fun h => hq h.1.symm, map_zero]
      simp
  · rw [ite_eq_right hp, ite_eq_right fun h => hp h.2]
    simp

/-- Bridge: the diagonal bond similarity `h(u, l) = (v_u/v_l)^{1/2}` carries every letter of the
source's tensor (arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1265), at both edge labels, to
the letter of the extended F-symbol block: `h S_f^{ij} h⁻¹ = B_f^{ij}`. -/
theorem fibStringNetTensor_conj (f : Fin 2) (i j : Fin 4) :
    Matrix.diagonal (fibStringNetGauge f) * fibStringNetTensor f i j *
        Matrix.diagonal ((fibStringNetGauge f)⁻¹) = fibBlockFull f i j := by
  rcases exists_fibEdgeOneLetter_or_fibEdgeTauLetter i with ⟨x', rfl⟩ | ⟨x', rfl⟩ <;>
    rcases exists_fibEdgeOneLetter_or_fibEdgeTauLetter j with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact fibStringNetTensor_edgeOne_conj f x' x
  · rw [fibBlockFull_edgeOne_edgeTau]
    ext p q
    simp [fibStringNetTensor, fibSiteLetter_fibEdgeOneLetter, fibSiteLetter_fibEdgeTauLetter]
  · rw [fibBlockFull_edgeTau_edgeOne]
    ext p q
    simp [fibStringNetTensor, fibSiteLetter_fibEdgeOneLetter, fibSiteLetter_fibEdgeTauLetter]
  · rw [fibBlockFull_edgeTau]
    exact fibStringNetEdgeTau_conj f x' x

/-- Bridge: the periodic operators of the source's blocks (arXiv:1511.08090, `AnyonsPEPS.tex`
lines 1262–1268) on the four physical letters equal those of the extended F-symbol blocks at
every length, by `MPOTensor.mpo_eq_of_diagonal_conj`. -/
theorem mpo_fibStringNetTensor (f : Fin 2) (L : ℕ) :
    mpo (fibStringNetTensor f) L = mpo (fibBlockFull f) L :=
  mpo_eq_of_diagonal_conj _ (fibStringNetGauge_ne_zero f) (fibStringNetTensor_conj f) L

/-! ### Fusion of the extended blocks

The four compression data of `Fibonacci.lean` and `FibonacciUnit.lean` extend to the sixteen
letters of the stacked products of the extended blocks with the same gauges. At the letters with
edge label `τ` the conjugated letters are the recorded block-diagonal ones; at the letters with
edge label `1` they are block upper triangular, with the edge-label-`1` letters of the target
blocks on the diagonal and further entries only in the columns of the zero slots, so the
remainder no longer vanishes but the trace identity of the compression still holds. -/

/-- The conjugated letters of a stacked product on the four physical letters: the recorded
letters `Kτ` of the product of the F-symbol blocks at edge label `τ` (indexed by the pair
alphabet `Fin 4`), the letters `K₁` at edge label `1`, and zero when the edge label changes. -/
def fibConjFull {n : ℕ} (Kτ : Fin 4 → Matrix (Fin n) (Fin n) GoldenInt)
    (K₁ : Fin 2 → Fin 2 → Matrix (Fin n) (Fin n) GoldenInt) :
    Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) GoldenInt :=
  fibEdgeGraded (fun x' x => Kτ (finProdFinEquiv (x', x))) K₁

/-- The conjugated letters of `1 ⊗ 1` at edge label `1`. -/
def fibOneOneEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 4) (Fin 4) GoldenInt
  | 0, 0 => Matrix.single 0 0 1 + Matrix.single 0 2 1 + Matrix.single 0 3 1
  | 1, 1 => Matrix.single 1 1 1
  | _, _ => 0

/-- The conjugated letters of `1 ⊗ τ` at edge label `1`. -/
def fibOneTauEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 0 0 1 + Matrix.single 0 3 1 + Matrix.single 0 4 1 + Matrix.single 0 5 1
  | 1, 0 => Matrix.single 1 1 1 + Matrix.single 1 5 ⟨0, 1, 0, 1⟩
  | 1, 1 => Matrix.single 2 2 1 + Matrix.single 2 5 (-1)
  | _, _ => 0

/-- The conjugated letters of `τ ⊗ 1` at edge label `1`. -/
def fibTauOneEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 0 0 1 + Matrix.single 0 5 ⟨-1, 0, 1, 0⟩
  | 1, 0 => Matrix.single 1 1 1 + Matrix.single 1 3 1 + Matrix.single 1 4 ⟨0, -1, 0, 0⟩ +
      Matrix.single 1 5 ⟨0, 0, 0, -1⟩
  | 1, 1 => Matrix.single 2 2 1 + Matrix.single 2 5 ⟨1, 0, -1, 0⟩
  | _, _ => 0

/-- The conjugated letters of `τ ⊗ τ` at edge label `1`. -/
def fibTauTauEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 9) (Fin 9) GoldenInt
  | 0, 0 => Matrix.single 0 0 1 + Matrix.single 0 8 ⟨-1, 0, -1, 0⟩
  | 0, 1 => Matrix.single 2 2 1 + Matrix.single 2 7 ⟨0, 0, 0, 1⟩ + Matrix.single 2 8 ⟨-1, 0, 1, 0⟩
  | 1, 0 => Matrix.single 3 3 1 + Matrix.single 3 7 ⟨0, 0, -1, 0⟩
  | 1, 1 => Matrix.single 1 1 1 + Matrix.single 1 5 ⟨0, 0, 0, -1⟩ +
      Matrix.single 1 6 ⟨0, 0, -1, 0⟩ + Matrix.single 4 4 1 + Matrix.single 4 5 ⟨0, 0, 0, 1⟩ +
      Matrix.single 4 6 ⟨0, 0, 1, 0⟩ +
      Matrix.single 4 8 1

/-- The stacked letters of `1 ⊗ 1` on the four physical letters over `ℤ[σ]`. -/
def fibOneOneFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 4) (Fin 4) GoldenInt :=
  mulGoldenTensor fibOneFullGolden fibOneFullGolden a.divNat a.modNat

/-- The conjugated letters of `1 ⊗ 1` on the four physical letters. -/
def fibOneOneFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 4) (Fin 4) GoldenInt :=
  fibConjFull fibOneOneConjGolden fibOneOneEdgeOneConjGolden a.divNat a.modNat

theorem fibOneOneFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibOneOneFullStackGolden a * fibOneOneGaugeInvGolden =
      fibOneOneGaugeInvGolden * fibOneOneFullConjGolden a := by
  revert a
  decide +kernel

private theorem fibOneOneFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 2) oneSlot 2) (h : unitOrd 2 y.1 < unitOrd 2 x.1) :
    fibOneOneFullConjGolden a (unitCoord 2 2 x) (unitCoord 2 2 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibOneOneFull_matched (a : Fin (4 * 4)) (p q : Fin 2) :
    fibOneOneFullConjGolden a (unitCoord 2 2 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 2 2 ⟨Sum.inl oneSlotMem, q⟩) = fibOneFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibOneOneFull_unmatched (a : Fin (4 * 4)) (t : Fin 2) (p q : Fin 1) :
    fibOneOneFullConjGolden a (unitCoord 2 2 ⟨Sum.inr t, p⟩)
      (unitCoord 2 2 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `1 ⊗ 1` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibOneOneFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibOneFull fibOneFull).toMPSTensor oneSlot
      (fun _ : Unit => fibOneFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 2 (unitOrd 2) (unitCoord 2 2) fibOneOneFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibOneFullGolden fibOneFullGolden _ _)
    (fun _ a => fibOneFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibOneOneGaugeGolden fibOneOneGaugeInvGolden fibOneOneGauge_mul_inv fibOneOneGaugeInv_mul
    fibOneOneFullConjGolden fibOneOneFullStack_mul_gaugeInv fibOneOneFull_triangular
    (fun a s _ p q => by cases s; exact fibOneOneFull_matched a p q) fibOneOneFull_unmatched

/-- The stacked letters of `1 ⊗ τ` on the four physical letters over `ℤ[σ]`. -/
def fibOneTauFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  mulGoldenTensor fibOneFullGolden fibTauFullGolden a.divNat a.modNat

/-- The conjugated letters of `1 ⊗ τ` on the four physical letters. -/
def fibOneTauFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  fibConjFull fibOneTauConjGolden fibOneTauEdgeOneConjGolden a.divNat a.modNat

theorem fibOneTauFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibOneTauFullStackGolden a * fibOneTauGaugeInvGolden =
      fibOneTauGaugeInvGolden * fibOneTauFullConjGolden a := by
  revert a
  decide +kernel

private theorem fibOneTauFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 3) oneSlot 3) (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibOneTauFullConjGolden a (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibOneTauFull_matched (a : Fin (4 * 4)) (p q : Fin 3) :
    fibOneTauFullConjGolden a (unitCoord 3 3 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 3 3 ⟨Sum.inl oneSlotMem, q⟩) = fibTauFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibOneTauFull_unmatched (a : Fin (4 * 4)) (t : Fin 3) (p q : Fin 1) :
    fibOneTauFullConjGolden a (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `1 ⊗ τ` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibOneTauFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibOneFull fibTauFull).toMPSTensor oneSlot
      (fun _ : Unit => fibTauFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibOneTauFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibOneFullGolden fibTauFullGolden _ _)
    (fun _ a => fibTauFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibOneTauGaugeGolden fibOneTauGaugeInvGolden fibOneTauGauge_mul_inv fibOneTauGaugeInv_mul
    fibOneTauFullConjGolden fibOneTauFullStack_mul_gaugeInv fibOneTauFull_triangular
    (fun a s _ p q => by cases s; exact fibOneTauFull_matched a p q) fibOneTauFull_unmatched

/-- The stacked letters of `τ ⊗ 1` on the four physical letters over `ℤ[σ]`. -/
def fibTauOneFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  mulGoldenTensor fibTauFullGolden fibOneFullGolden a.divNat a.modNat

/-- The conjugated letters of `τ ⊗ 1` on the four physical letters. -/
def fibTauOneFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  fibConjFull fibTauOneConjGolden fibTauOneEdgeOneConjGolden a.divNat a.modNat

theorem fibTauOneFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibTauOneFullStackGolden a * fibTauOneGaugeInvGolden =
      fibTauOneGaugeInvGolden * fibTauOneFullConjGolden a := by
  revert a
  decide +kernel

private theorem fibTauOneFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 3) oneSlot 3) (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibTauOneFullConjGolden a (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibTauOneFull_matched (a : Fin (4 * 4)) (p q : Fin 3) :
    fibTauOneFullConjGolden a (unitCoord 3 3 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 3 3 ⟨Sum.inl oneSlotMem, q⟩) = fibTauFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibTauOneFull_unmatched (a : Fin (4 * 4)) (t : Fin 3) (p q : Fin 1) :
    fibTauOneFullConjGolden a (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `τ ⊗ 1` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibTauOneFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibTauFull fibOneFull).toMPSTensor oneSlot
      (fun _ : Unit => fibTauFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibTauOneFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibTauFullGolden fibOneFullGolden _ _)
    (fun _ a => fibTauFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibTauOneGaugeGolden fibTauOneGaugeInvGolden fibTauOneGauge_mul_inv fibTauOneGaugeInv_mul
    fibTauOneFullConjGolden fibTauOneFullStack_mul_gaugeInv fibTauOneFull_triangular
    (fun a s _ p q => by cases s; exact fibTauOneFull_matched a p q) fibTauOneFull_unmatched

/-- The golden letters of the extended blocks, indexed by the label. -/
def fibBlockFullGolden : (s : Fin 2) → Fin 4 → Fin 4 →
    Matrix (Fin (fibBlockDim s)) (Fin (fibBlockDim s)) GoldenInt
  | 0 => fibOneFullGolden
  | 1 => fibTauFullGolden

theorem fibBlockFull_toMPSTensor_eq (s : Fin 2) (a : Fin (4 * 4)) :
    (fibBlockFull s).toMPSTensor a = complexOfGolden (fibBlockFullGolden s a.divNat a.modNat) := by
  fin_cases s <;> rfl

/-- The stacked letters of `τ ⊗ τ` on the four physical letters over `ℤ[σ]`. -/
def fibTauTauFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 9) (Fin 9) GoldenInt :=
  mulGoldenTensor fibTauFullGolden fibTauFullGolden a.divNat a.modNat

/-- The conjugated letters of `τ ⊗ τ` on the four physical letters. -/
def fibTauTauFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 9) (Fin 9) GoldenInt :=
  fibConjFull fibConjGolden fibTauTauEdgeOneConjGolden a.divNat a.modNat

theorem fibTauTauFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibTauTauFullStackGolden a * fibGaugeInvGolden =
      fibGaugeInvGolden * fibTauTauFullConjGolden a := by
  revert a
  decide +kernel

private theorem fibTauTauFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace fibBlockDim fibSlots 4) (h : fibOrd y.1 < fibOrd x.1) :
    fibTauTauFullConjGolden a (fibCoord x) (fibCoord y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibTauTauFull_matched (a : Fin (4 * 4)) (s : Fin 2)
    (p q : Fin (fibBlockDim s)) :
    fibTauTauFullConjGolden a (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩) =
      fibBlockFullGolden s a.divNat a.modNat p q := by
  revert a
  fin_cases s <;> revert p q <;> decide +kernel

private theorem fibTauTauFull_unmatched (a : Fin (4 * 4)) (t : Fin 4) (p q : Fin 1) :
    fibTauTauFullConjGolden a (fibCoord ⟨Sum.inr t, p⟩) (fibCoord ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `τ ⊗ τ` on the four physical letters, onto both extended blocks. -/
def fibTauTauFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibTauFull fibTauFull).toMPSTensor fibSlots
      (fun s => (fibBlockFull s).toMPSTensor) :=
  MultiBlockCompression.ofGolden 4 fibOrd fibCoord fibTauTauFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibTauFullGolden fibTauFullGolden _ _)
    (fun s a => fibBlockFullGolden s a.divNat a.modNat) fibBlockFull_toMPSTensor_eq
    fibGaugeGolden fibGaugeInvGolden fibGauge_mul_inv fibGaugeInv_mul fibTauTauFullConjGolden
    fibTauTauFullStack_mul_gaugeInv fibTauTauFull_triangular
    (fun a s _ p q => fibTauTauFull_matched a s p q) fibTauTauFull_unmatched

/-- **The Fibonacci fusion rules of the extended blocks.** On the four physical letters
(plaquette, edge label), the periodic operators of the extended F-symbol blocks satisfy
`O_1 O_1 = O_1`, `O_1 O_τ = O_τ O_1 = O_τ` and `O_τ O_τ = O_1 + O_τ` at every positive length. -/
theorem isMPOFusionAlgebra_fibBlockFull : IsMPOFusionAlgebra fibBlockFull fibNim := by
  intro a b L hL
  match a, b with
  | 0, 0 =>
    simp only [fibBlockFull, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, add_zero]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibOneFull)
      fibOneOneFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 0, 1 =>
    simp only [fibBlockFull, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, zero_add]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTauFull)
      fibOneTauFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 1, 0 =>
    simp only [fibBlockFull, fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, Nat.cast_zero, one_smul, zero_smul, zero_add]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTauFull)
      fibTauOneFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 1, 1 =>
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fibBlockFull)
      fibTauTauFull_compression L hL
    rw [show fibSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
    simp only [fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, one_smul]
    exact h

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1268: the blocks `B_1`, `B_τ` of the
string-net operator tensor `G^{abc}_{def} √(v_a v_b v_c v_d)` satisfy the Fibonacci fusion rules,
on the full alphabet of four physical letters (plaquette, edge label) per site. This is
`isMPOFusionAlgebra_fibBlockFull` transported along `mpo_fibStringNetTensor`. -/
theorem isMPOFusionAlgebra_fibStringNetTensor :
    IsMPOFusionAlgebra fibStringNetTensor fibNim :=
  isMPOFusionAlgebra_fibBlockFull.of_mpo_eq_mul_mul (fun _ => 1) (fun _ => 1)
    (fun _ _ => Matrix.one_mul 1) fun a L _ => by
      rw [mpo_fibStringNetTensor, Matrix.one_mul, Matrix.mul_one]

/-! ### The review's prefactor -/

/-- Source: arXiv:2011.12127, `TN-Review-main.tex` lines 2613–2621 (figure file `fig3_mpo.pdf`),
with `𝒞 = ℳ = 𝒟` the Fibonacci category (lines 2621–2625) and the vertical label `α = τ`. The
review's operator tensor of the block `a = f`: at the outgoing plaquette `A = x'`, the incoming
plaquette `C = x`, the left bond letter `p` and the right bond letter `q = (B, D)`, its entry is
`(1/√(d_A d_D)) (F^{aCα}_B)^{D}_{A}` when `p = (A, C)`, and zero otherwise. The F-symbols are
the source's `fibFSymbolGolden`, with the selection rule `δ_{abe} δ_{cde} δ_{adf} δ_{bcf}` of
`AnyonsPEPS.tex` lines 1245–1257, in place of the rule printed at `TN-Review-main.tex` line 2623
(the Local fix of the module header). -/
def fibReviewTensor (f : Fin 2) : MPOTensor 2 (fibBlockDim f) := fun x' x =>
  Matrix.of fun p q =>
    if fibBondLetter f p = (x', x) then
      (((Real.sqrt (fibDim x' * fibDim (fibBondLetter f q).2))⁻¹ : ℝ) : ℂ) *
        goldenToComplex (fibFSymbolGolden f x 1 (fibBondLetter f q).1 x' (fibBondLetter f q).2)
    else 0

theorem fibLoopFactor_complex_inv_ne_zero (a : Fin 2) : (fibLoopFactor a : ℂ)⁻¹ ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.2 (fibLoopFactor_pos a).ne')

/-- The diagonal matrix `W^{-1/2} = diag ∏_k d_{x_k}^{-1/2}` on the configurations of `L`
plaquettes. -/
def fibReviewWeight (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  Matrix.diagonal fun σ => ∏ k, (fibLoopFactor (σ k) : ℂ)⁻¹

/-- The bond gauge `g(u, l) = d_l^{-1/2}` that turns the review's prefactor into a letterwise
scalar. -/
theorem fibReviewTensor_conj (f x' x : Fin 2) :
    Matrix.diagonal (fun p => (fibLoopFactor (fibBondLetter f p).2 : ℂ)⁻¹) *
        fibReviewTensor f x' x *
        Matrix.diagonal (fun p => (fibLoopFactor (fibBondLetter f p).2 : ℂ)⁻¹)⁻¹ =
      ((fibLoopFactor x' : ℂ)⁻¹ * (fibLoopFactor x : ℂ)⁻¹) • fibBlock f x' x := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, fibBlock_apply_eq_fSymbol]
  simp only [fibReviewTensor, Matrix.of_apply, Pi.inv_apply]
  split_ifs with hp
  · rw [hp]
    have h1 := Real.sqrt_pos.2 (fibDim_pos x')
    have h2 := Real.sqrt_pos.2 (fibDim_pos x)
    have h3 := Real.sqrt_pos.2 (fibDim_pos (fibBondLetter f q).2)
    have c1 : ((Real.sqrt (fibDim x') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h1.ne'
    have c2 : ((Real.sqrt (fibDim x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h2.ne'
    have c3 : ((Real.sqrt (fibDim (fibBondLetter f q).2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 h3.ne'
    rw [Real.sqrt_mul (fibDim_pos x').le]
    simp only [fibLoopFactor, smul_eq_mul]
    push_cast
    field_simp
  · simp

/-- Project result: the periodic operator of the review's tensor (arXiv:2011.12127,
`TN-Review-main.tex` lines 2613–2621) at edge label `τ` is the congruence
`W^{-1/2} O_f W^{-1/2}` of the operator of the F-symbol block, with
`W^{-1/2} = diag ∏_k d_{x_k}^{-1/2}`. -/
theorem mpo_fibReviewTensor (f : Fin 2) (L : ℕ) :
    mpo (fibReviewTensor f) L = fibReviewWeight L * mpo (fibBlock f) L * fibReviewWeight L := by
  rw [mpo_eq_of_diagonal_conj _ (fun _ => fibLoopFactor_complex_inv_ne_zero _)
    (fibReviewTensor_conj f) L]
  ext σ τ
  rw [mpo_letterwise_smul, fibReviewWeight, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Finset.prod_mul_distrib]
  ring

/-- The periodic operator of a tensor on one site is the trace of its letter. -/
private theorem mpo_one_apply {D : ℕ} (M : MPOTensor 2 D) (σ τ : Fin 1 → Fin 2) :
    mpo M 1 σ τ = Matrix.trace (M (σ 0) (τ 0)) := by
  simp [mpoMatrixEntry]

/-- Project result: the review's prefactored operators (arXiv:2011.12127, `TN-Review-main.tex`
lines 2613–2621), read as operators in the orthonormal basis of plaquette configurations, do
not satisfy the Fibonacci fusion rules. At one site the unit operator is
`W^{-1/2} O_1 W^{-1/2} = diag(0, 1/φ)`, whose square has the entry `1/φ² ≠ 1/φ`. -/
theorem not_isMPOFusionAlgebra_fibReviewTensor :
    ¬ IsMPOFusionAlgebra fibReviewTensor fibNim := by
  intro h
  set τ₀ : Fin 1 → Fin 2 := fun _ => 1 with hτ₀
  have key : ∀ σ : Fin 1 → Fin 2, σ = τ₀ ↔ σ 0 = 1 := fun σ =>
    ⟨fun h => h ▸ rfl, fun h => funext fun k => by rw [Subsingleton.elim k 0, h]⟩
  have hphi := Real.goldenRatio_pos
  have hO : ∀ σ ρ : Fin 1 → Fin 2, mpo (fibReviewTensor 0) 1 σ ρ =
      if σ 0 = 1 ∧ ρ 0 = 1 then ((Real.goldenRatio : ℝ) : ℂ)⁻¹ else 0 := by
    intro σ ρ
    rw [mpo_fibReviewTensor, fibReviewWeight, Matrix.mul_diagonal, Matrix.diagonal_mul,
      mpo_one_apply]
    simp only [Fin.prod_univ_one]
    generalize σ 0 = a
    generalize ρ 0 = b
    change (fibLoopFactor a : ℂ)⁻¹ * Matrix.trace (fibOne a b) * (fibLoopFactor b : ℂ)⁻¹ = _
    have hd0 : (fibLoopFactor 0 : ℂ)⁻¹ = 1 := by simp [fibLoopFactor, fibDim]
    have hd1 : (fibLoopFactor 1 : ℂ)⁻¹ * (fibLoopFactor 1 : ℂ)⁻¹ =
        ((Real.goldenRatio : ℝ) : ℂ)⁻¹ := by
      simpa [fibLoopFactor, fibDim] using
        Complex.ofReal_sqrt_inv_mul_self (fibDim 1) (fibDim_pos 1).le
    fin_cases a <;> fin_cases b <;> simp [fibOne, fibOneGolden, Matrix.trace_fin_two, hd0, hd1]
  have h00 := congrFun (congrFun (h 0 0 1 one_pos) τ₀) τ₀
  rw [Matrix.mul_apply, Fintype.sum_eq_single τ₀ (fun ρ hρ => by
      have hρ0 : ¬ ρ 0 = 1 := fun h => hρ ((key ρ).2 h)
      rw [hO τ₀ ρ]
      simp [hρ0]),
    Matrix.sum_apply, Fin.sum_univ_two] at h00
  simp only [Matrix.smul_apply, hO, hτ₀, fibNim, Matrix.one_apply_eq,
    Matrix.one_apply_ne zero_ne_one, and_self, ite_true, Nat.cast_one, Nat.cast_zero, one_smul,
    zero_smul, add_zero] at h00
  have hne : ((Real.goldenRatio : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hphi.ne'
  have hne1 : ((Real.goldenRatio : ℝ) : ℂ) ≠ 1 :=
    fun h1 => Real.one_lt_goldenRatio.ne' (by exact_mod_cast h1)
  field_simp at h00
  exact hne1 (by linear_combination -h00)

/-- The review's tensor with the letterwise factor `d_x` of the incoming plaquette, whose
periodic operator is `O_f^{rev} W`. -/
def fibReviewWeightedTensor (f : Fin 2) : MPOTensor 2 (fibBlockDim f) := fun x' x =>
  ((fibDim x : ℝ) : ℂ) • fibReviewTensor f x' x

/-- Project result: the review's operators become a Fibonacci fusion algebra after multiplying
by `W` on the right, `O_f^{rev} W = W^{-1/2} O_f W^{1/2}`, which is similar to the operator of
the F-symbol block. -/
theorem isMPOFusionAlgebra_fibReviewWeightedTensor :
    IsMPOFusionAlgebra fibReviewWeightedTensor fibNim := by
  refine isMPOFusionAlgebra_fibBlock.of_mpo_eq_mul_mul fibReviewWeight
    (fun L => Matrix.diagonal (fun σ : Fin L → Fin 2 => ∏ k, (fibLoopFactor (σ k) : ℂ)⁻¹)⁻¹)
    (fun L _ => Matrix.diagonal_inv_mul_diagonal fun σ =>
      Finset.prod_ne_zero_iff.2 fun k _ => fibLoopFactor_complex_inv_ne_zero _)
    (fun a L _ => ?_)
  ext σ τ
  have hd : ∀ x : Fin 2,
      ((fibDim x : ℝ) : ℂ) * (fibLoopFactor x : ℂ)⁻¹ = ((fibLoopFactor x : ℂ)⁻¹)⁻¹ := by
    intro x
    have h1 : (fibLoopFactor x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (fibLoopFactor_pos x).ne'
    rw [inv_inv, ← Complex.ofReal_sqrt_sq _ (fibDim_pos x).le]
    change (fibLoopFactor x : ℂ) ^ 2 * _ = _
    field_simp
  have hmpo := congrFun (congrFun (mpo_fibReviewTensor a L) σ) τ
  rw [show fibReviewWeightedTensor a = fun i j =>
      (fun _ x => ((fibDim x : ℝ) : ℂ)) i j • fibReviewTensor a i j from rfl,
    mpo_letterwise_smul, hmpo]
  simp only [fibReviewWeight, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
  have hprod : (∏ k, ((fibDim (τ k) : ℝ) : ℂ)) * ∏ k, (fibLoopFactor (τ k) : ℂ)⁻¹ =
      (∏ k, (fibLoopFactor (τ k) : ℂ)⁻¹)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => hd (τ k)
  rw [← hprod]
  ring

end FibonacciCompression
