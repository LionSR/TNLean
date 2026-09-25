/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.FibonacciAnomaly
import TNLean.MPS.MPDO.DirectSum

/-!
# Fibonacci string-net: the operator tensor from the F-symbols

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` lines 1240–1269:
the Fibonacci fusion rules, the quantum dimensions `d_1 = 1`, `d_τ = φ`, the F-symbols with the
admissibility deltas `δ_{abe} δ_{cde} δ_{adf} δ_{bcf}` and the nontrivial block
`[F^{τττ}_τ] = [[1/φ, 1/√φ], [1/√φ, -1/φ]]`, the G-symbols `G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)`
with `v_i = √d_i`, a projector matrix product operator of bond dimension `5` made of two blocks
`B_1`, `B_τ` of dimensions `2` and `3` obeying the Fibonacci fusion rules, and the weights
`w_1 = 1/(1 + φ²)`, `w_τ = φ/(1 + φ²)` of the projector `P_L = ∑_a w_a O_a^L` of Section 3.2
(`AnyonsPEPS.tex` lines 143–160).
Review: arXiv:2011.12127, Appendix A, "The MPO for the Fibonacci model"
(`Papers/2011.12127/TN-Review-main.tex` lines 2613–2625), which prints the same fusion rules and
the same block `F^{τττ}_τ`.

**Formalized here.** The fusion multiplicities and the F- and G-symbols of the source, in exact
arithmetic over the golden integers `ℤ[σ]`, `σ = φ^{-1/2}`, together with their complex values
`1/φ`, `1/√φ`; the identification of every entry of the `τ` block of
`Examples/Fibonacci.lean` with an F-symbol; a bond-dimension-five tensor `B_1 ⊕ B_τ` whose
`Δ`-weighted periodic operator, with the source's weights `Δ = w_1 1_2 ⊕ w_τ 1_3`, is
`P_L = w_1 O_1^L + w_τ O_τ^L`; and idempotence of `P_L` at every positive length.

**Local fix (provenance):** the source draws the operator tensor only as a diagram and prints no
numeric entries of `B_1`, `B_τ`; the blocks used here place the bare F-symbol
`[F^{τ x τ}_{x'_{j+1}}]_{x'_j}^{x_{j+1}}` at the physical letter `(x', x)` and the bond letters
`(x'_j, x_j)`, `(x'_{j+1}, x_{j+1})`, without the source's closed-loop factors `v_a` and without
the review's prefactor `1/√(d_A d_D)`; it is for these entries that `O_τ² = O_1 + O_τ` holds.
The blocks are not identified with the source's diagram tensor, and no operator statement is made
for a rescaled tensor. Documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

**Local fix (positive length):** the source asks for `P_L² = P_L` for all `L`
(`AnyonsPEPS.tex` lines 152–156); at `L = 0` the periodic operators are the bond dimensions,
`O_1^0 = 2` and `O_τ^0 = 3`, so `P_0 = (2 + 3φ)/(1 + φ²)` is a scalar different from `0` and `1`.
The empty chain is read as a degenerate case, and idempotence (`fibProjector_mul_self`) is
stated for every positive length. Documented in
`docs/paper-gaps/bmwshv17_fibonacci_projector_positive_length.tex`.

## Main definitions

* `FibonacciCompression.fibFTauGolden`, `FibonacciCompression.fibFSymbolGolden`: the F-symbols.
* `FibonacciCompression.fibQuantumDimGolden`, `FibonacciCompression.fibQuantumDimInvSqrt`,
  `FibonacciCompression.fibGSymbolGolden`: quantum dimensions and G-symbols.
* `FibonacciCompression.fibLetter`: the three admissible letters `(x', x)` of the `τ` block.
* `FibonacciCompression.fibPMPO`: the bond-dimension-five tensor `B_1 ⊕ B_τ`.
* `FibonacciCompression.fibDelta`: the boundary matrix `Δ = w_1 1_2 ⊕ w_τ 1_3`.
* `FibonacciCompression.fibProjector`: the weighted projector `w_1 O_1^L + w_τ O_τ^L`.

## Main results

* `FibonacciCompression.fibNim_eq_ite`: the multiplicities `N_{ab}^c` of the source.
* `FibonacciCompression.complexOfGolden_fibFTauGolden`: the block `F^{τττ}_τ` has the printed
  entries `1/φ`, `1/√φ`, `-1/φ`.
* `FibonacciCompression.fibTauGolden_eq_fSymbol`, `FibonacciCompression.fibTau_eq_fSymbol`: every
  entry of the `τ` block is an F-symbol.
* `FibonacciCompression.mpo_fibPMPO`: without `Δ`, the operator of the bond-five tensor is
  `O_1 + O_τ`.
* `FibonacciCompression.fibProjector_eq_trace_fibDelta`: the `Δ`-weighted operator of the
  locally chosen bond-five tensor is `P_L`.
* `FibonacciCompression.fibProjector_mul_self`: `P_L` is idempotent at every positive length.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*

## Provenance

The placement of the F-symbols in the `τ` block was fixed by the search recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §3.1, and the resulting entries are
recorded in §3.2; these are verification records, not the source.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-! ### Fusion rules -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1240–1244 (review arXiv:2011.12127,
`TN-Review-main.tex` line 2622). The Fibonacci fusion multiplicities are
`N_{11}^1 = N_{τ1}^τ = N_{1τ}^τ = N_{ττ}^1 = N_{ττ}^τ = 1`, all others zero; the label `0` is
the trivial label and `1` is `τ`. -/
theorem fibNim_eq_ite (a b c : Fin 2) :
    fibNim a b c =
      if (a, b, c) ∈ ({(0, 0, 0), (1, 0, 1), (0, 1, 1), (1, 1, 0), (1, 1, 1)} :
          Finset (Fin 2 × Fin 2 × Fin 2)) then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-! ### Quantum dimensions, F-symbols and G-symbols -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1244. The quantum dimensions `d_1 = 1` and
`d_τ = φ`, written in the golden integers as `φ = 1 + σ²`. -/
def fibQuantumDimGolden : Fin 2 → GoldenInt
  | 0 => 1
  | 1 => 1 + sigma ^ 2

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1257–1260. The inverse closed-loop factors
`1/v_a = d_a^{-1/2}`: `1` at the trivial label and `σ = φ^{-1/2}` at `τ`. -/
def fibQuantumDimInvSqrt : Fin 2 → GoldenInt
  | 0 => 1
  | 1 => sigma

/-- The golden ratio satisfies `d_τ² = d_τ + 1` in the golden integers. -/
theorem fibQuantumDimGolden_one_sq :
    fibQuantumDimGolden 1 ^ 2 = fibQuantumDimGolden 1 + 1 := by decide

/-- `(1/v_a)² · d_a = 1`: the inverse closed-loop factors are inverse square roots of the
quantum dimensions. -/
theorem fibQuantumDimInvSqrt_sq_mul (a : Fin 2) :
    fibQuantumDimInvSqrt a ^ 2 * fibQuantumDimGolden a = 1 := by
  fin_cases a <;> decide

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1250–1257 (review arXiv:2011.12127,
`TN-Review-main.tex` line 2625). The nontrivial block `[F^{τττ}_τ]_e^f`, indexed by
`e, f ∈ {1, τ}`, is `[[1/φ, 1/√φ], [1/√φ, -1/φ]]`, that is `[[σ², σ], [σ, -σ²]]`. -/
def fibFTauGolden : Matrix (Fin 2) (Fin 2) GoldenInt :=
  !![sigma ^ 2, sigma; sigma, -sigma ^ 2]

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1245–1257. The F-symbol
`[F^{abc}_d]_e^f = δ_{abe} δ_{cde} δ_{adf} δ_{bcf} F^{abc}_{def}`, with `δ_{ijk} = 1` exactly when
`N_{ij}^k > 0`: it vanishes unless the four fusions are admissible, equals the block
`fibFTauGolden` when `a = b = c = d = τ`, and is `1` otherwise. -/
def fibFSymbolGolden (a b c d e f : Fin 2) : GoldenInt :=
  if fibNim a b e ≠ 0 ∧ fibNim c d e ≠ 0 ∧ fibNim a d f ≠ 0 ∧ fibNim b c f ≠ 0 then
    (if (a, b, c, d) = (1, 1, 1, 1) then fibFTauGolden e f else 1)
  else 0

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1257–1260, eq. `eq:Gsymbol`. The G-symbol
`G^{abc}_{def} = F^{abc}_{def} / (v_e v_f)`. -/
def fibGSymbolGolden (a b c d e f : Fin 2) : GoldenInt :=
  fibQuantumDimInvSqrt e * fibQuantumDimInvSqrt f * fibFSymbolGolden a b c d e f

/-- The block `F^{τττ}_τ` is an involution, `F² = 1`. -/
theorem fibFTauGolden_mul_self : fibFTauGolden * fibFTauGolden = 1 := by decide

/-- The block of F-symbols at `a = b = c = d = τ` is `fibFTauGolden`. -/
theorem fibFSymbolGolden_tau (e f : Fin 2) : fibFSymbolGolden 1 1 1 1 e f = fibFTauGolden e f := by
  fin_cases e <;> fin_cases f <;> decide

/-- Bridge: the golden integer `1 + σ²` is the golden ratio `φ = (1 + √5)/2`. -/
theorem goldenToComplex_fibQuantumDimGolden_one :
    goldenToComplex (fibQuantumDimGolden 1) = (Real.goldenRatio : ℂ) := by
  have h : goldenToComplex (fibQuantumDimGolden 1) =
      ((1 + goldenSigmaReal ^ 2 : ℝ) : ℂ) := by
    simp [fibQuantumDimGolden, goldenSigmaComplex]
  rw [h, goldenSigmaReal_sq, Real.inv_goldenRatio, ← sub_eq_add_neg, Real.one_sub_goldenRatio]

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1250–1257. The complex values of the block
`F^{τττ}_τ` are the printed ones, `[[1/φ, 1/√φ], [1/√φ, -1/φ]]` with `φ = (1 + √5)/2`. -/
theorem complexOfGolden_fibFTauGolden :
    complexOfGolden fibFTauGolden =
      !![((Real.goldenRatio⁻¹ : ℝ) : ℂ), (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ);
        (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ), -((Real.goldenRatio⁻¹ : ℝ) : ℂ)] := by
  have hs2 : goldenSigmaComplex ^ 2 = ((Real.goldenRatio⁻¹ : ℝ) : ℂ) := by
    rw [goldenSigmaComplex, ← Complex.ofReal_pow, goldenSigmaReal_sq]
  have hs : goldenSigmaComplex = (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ) := by
    rw [goldenSigmaComplex, goldenSigmaReal_eq_inv_sqrt_goldenRatio]
  have h : complexOfGolden fibFTauGolden = !![goldenSigmaComplex ^ 2, goldenSigmaComplex;
      goldenSigmaComplex, -goldenSigmaComplex ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [complexOfGolden, fibFTauGolden]
  rw [h, hs2, hs]

/-! ### The `τ` block is built from the F-symbols -/

/-- The three admissible letters `(x', x)` of the `τ` block, `(1, τ)`, `(τ, 1)`, `(τ, τ)`, in the
order of the bond coordinates of `fibTauGolden`; the pair `(1, 1)` is not admissible. -/
def fibLetter : Fin 3 → Fin 2 × Fin 2 := ![(0, 1), (1, 0), (1, 1)]

/-- Bridge: the F-symbols are those of arXiv:1511.08090, `AnyonsPEPS.tex` lines 1245–1257; the
source draws the operator tensor only as a diagram (lines 1262–1268) and prints no block entries.
The entry of the `τ` block at the incoming bond letter `p = (x'_j, x_j)`, the outgoing bond letter
`q = (x'_{j+1}, x_{j+1})` and the physical letter `(x', x)` is the F-symbol
`[F^{τ x τ}_{x'_{j+1}}]_{x'}^{x_{j+1}}` when `p = (x', x)`, and zero otherwise. This placement is
the Local fix (provenance) of the module header, documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`. -/
theorem fibTauGolden_eq_fSymbol (x' x : Fin 2) :
    fibTauGolden x' x = Matrix.of fun p q =>
      if fibLetter p = (x', x) then
        fibFSymbolGolden 1 x 1 (fibLetter q).1 x' (fibLetter q).2
      else 0 := by
  fin_cases x' <;> fin_cases x <;> decide

/-- Bridge: the complex form of `fibTauGolden_eq_fSymbol`. -/
theorem fibTau_eq_fSymbol (x' x : Fin 2) :
    fibTau x' x = complexOfGolden (Matrix.of fun p q =>
      if fibLetter p = (x', x) then
        fibFSymbolGolden 1 x 1 (fibLetter q).1 x' (fibLetter q).2
      else 0) := by
  rw [← fibTauGolden_eq_fSymbol]
  rfl

/-! ### The projector matrix product operator -/

/-- The bond-dimension-five tensor `B_1 ⊕ B_τ`, the block-diagonal sum of the trivial block
`fibOne` and the `τ` block `fibTau`, matching the bond dimension `5 = 2 + 3` and the block
dimensions stated in arXiv:1511.08090, `AnyonsPEPS.tex` lines 1266–1268. Its blocks carry the
entries of the Local fix (provenance) of the module header. -/
def fibPMPO : MPOTensor 2 (2 + 3) := directSum fibOne fibTau

/-- Bridge: the periodic operator of the bond-five tensor without the boundary matrix `Δ` is the
sum `O_1^L + O_τ^L` of the operators of its two blocks, by additivity of the direct sum. The
weighted operator `P_L` of the source's form is obtained only after inserting `Δ`
(`fibProjector_eq_trace_fibDelta`). -/
theorem mpo_fibPMPO (L : ℕ) : mpo fibPMPO L = mpo fibOne L + mpo fibTau L :=
  mpo_directSum fibOne fibTau L

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1269. The weights
`w_1 = 1/(1 + φ²)` and `w_τ = φ/(1 + φ²)`: the quantum dimensions divided by the total quantum
dimension squared. -/
def fibWeight : Fin 2 → ℂ
  | 0 => 1 / (1 + (Real.goldenRatio : ℂ) ^ 2)
  | 1 => (Real.goldenRatio : ℂ) / (1 + (Real.goldenRatio : ℂ) ^ 2)

/-- The weight of the trivial label satisfies `w_1 = w_1² + w_τ²`. -/
private theorem fibWeight_zero_eq :
    fibWeight 0 = fibWeight 0 * fibWeight 0 + fibWeight 1 * fibWeight 1 := by
  have hD : (1 + (Real.goldenRatio : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 : ℝ) + Real.goldenRatio ^ 2 ≠ 0)
  simp only [fibWeight]
  generalize (Real.goldenRatio : ℂ) = x at hD ⊢
  field_simp

/-- The weight of `τ` satisfies `w_τ = 2 w_1 w_τ + w_τ²`, by `φ² = φ + 1`. -/
private theorem fibWeight_one_eq :
    fibWeight 1 = 2 * (fibWeight 0 * fibWeight 1) + fibWeight 1 * fibWeight 1 := by
  have hφ : (Real.goldenRatio : ℂ) ^ 2 = Real.goldenRatio + 1 := by
    exact_mod_cast Real.goldenRatio_sq
  have hD : (1 + (Real.goldenRatio : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 : ℝ) + Real.goldenRatio ^ 2 ≠ 0)
  simp only [fibWeight]
  generalize (Real.goldenRatio : ℂ) = x at hφ hD ⊢
  field_simp
  linear_combination x * hφ

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 159 and line 1269. The weights satisfy
`∑_{a,b} N_{ab}^c w_a w_b = w_c`. -/
theorem fibWeight_fusion (c : Fin 2) :
    ∑ a, ∑ b, (fibNim a b c : ℂ) * fibWeight a * fibWeight b = fibWeight c := by
  fin_cases c
  · simp only [fibNim, fibFusionMatrix, Fin.zero_eta, Fin.isValue, Fin.sum_univ_two,
      Matrix.one_apply_eq, Nat.cast_one, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, CharP.cast_eq_zero, zero_mul, add_zero, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      zero_add]
    linear_combination -fibWeight_zero_eq
  · simp only [fibNim, fibFusionMatrix, Fin.mk_one, Fin.isValue, Fin.sum_univ_two, ne_eq,
      zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, CharP.cast_eq_zero, zero_mul,
      Matrix.one_apply_eq, Nat.cast_one, one_mul, zero_add, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    linear_combination -fibWeight_one_eq

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 144–151 and 1269. The weighted operator
`P_L = w_1 O_1^L + w_τ O_τ^L`. -/
def fibProjector (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  fibWeight 0 • mpo fibOne L + fibWeight 1 • mpo fibTau L

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 132–141 and 1269. The boundary matrix
`Δ = w_1 1_2 ⊕ w_τ 1_3` on the bond space of `fibPMPO`. -/
def fibDelta : Matrix (Fin (2 + 3)) (Fin (2 + 3)) ℂ :=
  (Matrix.fromBlocks (fibWeight 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
    (fibWeight 1 • (1 : Matrix (Fin 3) (Fin 3) ℂ))).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 128–151 and 1268–1269. The weighted
operator `P_L` is the boundary-weighted matrix product operator
`∑ tr(Δ B^{i_1 j_1} ⋯ B^{i_L j_L}) |i⟩⟨j|`, in the source's form, of the locally chosen
bond-five tensor `fibPMPO` with the boundary matrix `Δ = fibDelta`. The blocks of `fibPMPO`
carry the bare F-symbol entries of the module's Local fix (provenance) and are not identified
with the source's diagram tensor. -/
theorem fibProjector_eq_trace_fibDelta (L : ℕ) :
    fibProjector L = Matrix.of fun σ τ =>
      Matrix.trace (fibDelta * evalWord fibPMPO (List.ofFn σ) (List.ofFn τ)) := by
  ext σ τ
  simp only [fibProjector, Matrix.add_apply, Matrix.smul_apply, mpo_apply, mpoMatrixEntry,
    smul_eq_mul, Matrix.of_apply, fibPMPO, evalWord_directSum, fibDelta,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.smul_mul, one_mul, Matrix.trace_fromBlocks_submatrix_finSumFinEquiv,
    Matrix.trace_smul]

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 152–160 and 1268–1269. With the fusion
rules of the two blocks (`fibonacci_fusion_algebra`) and the weight relation
`∑_{a,b} N_{ab}^c w_a w_b = w_c` (`fibWeight_fusion`), the weighted operator is a projector at
every positive length, `P_L² = P_L`. The source asks this for all `L`; at `L = 0` the empty trace
gives the bond dimensions, `O_1^0 = 2` and `O_τ^0 = 3`, so `P_0 = (2 + 3φ)/(1 + φ²) ≠ 1`, and
the empty chain is excluded as a degenerate reading, as recorded in the module's Local fix
(positive length). -/
theorem fibProjector_mul_self (L : ℕ) (hL : 0 < L) :
    fibProjector L * fibProjector L = fibProjector L := by
  simp only [fibProjector, add_mul, mul_add, smul_mul_smul_comm, fibOne_mul_fibOne L hL,
    fibOne_mul_fibTau L hL, fibTau_mul_fibOne L hL, fibonacci_fusion_rule L hL, smul_add]
  match_scalars
  · linear_combination -fibWeight_zero_eq
  · linear_combination -fibWeight_one_eq

end FibonacciCompression
