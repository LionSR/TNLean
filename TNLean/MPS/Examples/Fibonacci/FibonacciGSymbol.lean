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
For the source's tensor at edge label `τ` on every site, a diagonal bond similarity
`h(x', x) = (v_{x'}/v_x)^{1/2}` carries every letter to the F-symbol blocks `fibOne`, `fibTau`, so
the periodic operators are equal at every length and the fusion rules of
`isMPOFusionAlgebra_fibBlock` are the source's fusion rules on that sector. For the review's
prefactor the periodic operator is the congruence `Δ^{-1/2} O_a Δ^{-1/2}`,
`Δ = diag ∏_k d_{x_k}`, of the F-symbol operator; it fails the fusion rules already at one site,
while the operator `O_a Δ = Δ^{-1/2} O_a Δ^{1/2}` satisfies them.

**Scope restriction (edge labels τ):** the operator identities for the source's tensor are
stated on the configurations whose vertical edge labels are all `τ`. The source's tensor also
has edge label `1`, where the two plaquettes on each side of the edge coincide, and its fusion
rules on the full alphabet of four letters per site are not proved here. Documented, with the
elimination plan, in `docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

**Local fix (review normalization):** read literally in the orthonormal basis of plaquette
configurations, the review's prefactor `1/√(d_A d_D)` gives operators that contradict the fusion
rules the review states for them (`TN-Review-main.tex` lines 1309, 1341); the fusion rules hold
for `O_a Δ`, that is, in the `Δ`-weighted inner product. The review's printed selection rule for
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
* `FibonacciCompression.fibReviewTensor`: the review's tensor `(1/√(d_A d_D)) F` at edge label `τ`.

## Main results

* `FibonacciCompression.fibGSymbolGolden_tetrahedral`: `G^{abc}_{def} = G^{fce}_{abd}`.
* `FibonacciCompression.fibStringNetEdgeTau_conj`: the diagonal bond similarity to the F-symbol
  blocks.
* `FibonacciCompression.mpo_fibStringNetTensor_edgeTau`: on edge label `τ` the source's periodic
  operators are those of the F-symbol blocks.
* `FibonacciCompression.isMPOFusionAlgebra_fibStringNetEdgeTau`: the source's blocks at edge label
  `τ` form a fusion algebra with the Fibonacci fusion rules.
* `FibonacciCompression.mpo_fibReviewTensor`: the review's operator is `Δ^{-1/2} O_a Δ^{-1/2}`.
* `FibonacciCompression.not_isMPOFusionAlgebra_fibReviewTensor`: the review's operators do not
  satisfy the fusion rules.
* `FibonacciCompression.isMPOFusionAlgebra_fibReviewWeightedTensor`: the operators `O_a Δ` do.

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

/-- The physical letters of the source's tensor: pairs (plaquette, edge label) in the order
`(1, 1)`, `(1, τ)`, `(τ, 1)`, `(τ, τ)`. -/
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

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1268: the blocks `B_1`, `B_τ` of the source's
tensor satisfy the Fibonacci fusion rules, here on edge label `τ` (the Scope restriction of the
module header). This is `isMPOFusionAlgebra_fibBlock` transported along
`mpo_fibStringNetEdgeTau`. -/
theorem isMPOFusionAlgebra_fibStringNetEdgeTau :
    IsMPOFusionAlgebra fibStringNetEdgeTau fibNim :=
  isMPOFusionAlgebra_fibBlock.of_mpo_eq_mul_mul (fun _ => 1) (fun _ => 1)
    (fun _ _ => Matrix.one_mul 1) fun a L _ => by
      rw [mpo_fibStringNetEdgeTau, Matrix.one_mul, Matrix.mul_one]

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

/-- The diagonal matrix `Δ^{-1/2} = diag ∏_k d_{x_k}^{-1/2}` on the configurations of `L`
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
`Δ^{-1/2} O_f Δ^{-1/2}` of the operator of the F-symbol block, with
`Δ^{-1/2} = diag ∏_k d_{x_k}^{-1/2}`. -/
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
`Δ^{-1/2} O_1 Δ^{-1/2} = diag(0, 1/φ)`, whose square has the entry `1/φ² ≠ 1/φ`. -/
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
periodic operator is `O_f^{rev} Δ`. -/
def fibReviewWeightedTensor (f : Fin 2) : MPOTensor 2 (fibBlockDim f) := fun x' x =>
  ((fibDim x : ℝ) : ℂ) • fibReviewTensor f x' x

/-- Project result: the review's operators become a Fibonacci fusion algebra after multiplying
by `Δ` on the right, `O_f^{rev} Δ = Δ^{-1/2} O_f Δ^{1/2}`, which is similar to the operator of
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
