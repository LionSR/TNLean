/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.GoldenCompression
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.MPDO.OperatorFromWordTrace

/-!
# Example F: the Fibonacci fusion `τ ⊗ τ = 1 ⊕ τ`

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` lines 1240–1269: the
Fibonacci F-symbols, and a projector matrix product operator of bond dimension `5` made of two
blocks `B_1`, `B_τ` of dimensions `2` and `3` that satisfy the Fibonacci fusion rules.
Review: arXiv:2011.12127, Appendix A, "The MPO for the Fibonacci model"
(`Papers/2011.12127/TN-Review-main.tex` lines 2613–2625). Garre-Rubio, Lootens and Molnár
(arXiv:2203.12563), `Papers/2203.12563/REsubmission.tex` line 1993, record the pair of normal
states invariant under this symmetry.

**Formalized here.** The source's claim that the two blocks `B_1`, `B_τ` satisfy the Fibonacci
fusion rules, in the form `O_τ O_τ = O_1 + O_τ` at every positive length, for the blocks with the
entries of the Local fix below, via the multi-block compression theorem. The identification of
the entries of the `τ` block with the source's F-symbols is `Examples/FibonacciFSymbol.lean`.

**Local fix (provenance):** the source draws the operator tensor only as a diagram and prints no
numeric entries of `B_1`, `B_τ`; the `τ` block here places the bare F-symbol
`[F^{τ x τ}_{x'_{j+1}}]_{x'_j}^{x_{j+1}}` at the physical letter `(x', x)` and the bond letters
`(x'_j, x_j)`, `(x'_{j+1}, x_{j+1})`, without the source's closed-loop factors, and `B_1` is the
admissibility projector of bond dimension two; documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

**Local fix (positive length):** the source derives the fusion rules `O_a O_b = ∑_c N_{ab}^c O_c`
from the projector identity required for all `L` (`References/1511.08090/AnyonsPEPS.tex`
lines 152–160); at `L = 0` the periodic operators are the bond dimensions, and
`O_τ^0 O_τ^0 = 9 ≠ 5 = O_1^0 + O_τ^0`. The empty chain is read as a degenerate case, and the
fusion rule (`fibonacci_fusion_rule`) is stated for every positive length; documented in
`docs/paper-gaps/bmwshv17_fibonacci_projector_positive_length.tex`.

A machine-checked instance of the multi-block asymmetric compression theorem (P5 note,
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for the
Fibonacci string-net matrix product operator algebra of arXiv:1511.08090, Appendix D.1.

This is the simplest fusion of matrix product operators that is not invertible: the two operator
families `O_1` and `O_τ` of the Fibonacci category obey `O_τ O_τ = O_1 + O_τ`, so the square of
the `τ` family is a sum of two inequivalent blocks rather than a single one. The unit of the
algebra is not the identity operator: `O_1` is the projector onto the admissible configurations
of the chain, those with no two neighbouring trivial labels, and it is a bond-dimension-two
matrix product operator. The `τ` family has bond dimension three, its one-site matrices are the
rows of the Fibonacci vertex weight, and the stacked tensor of the square has bond dimension
nine. Of those nine directions, two carry the trivial block, three carry the `τ` block, and the
remaining four are annihilated by every letter: they are the inadmissible configurations killed
by the vertex weights.

The entries of the tensors are not rational. They lie in the ring `ℤ[σ]` of `GoldenRing.lean`,
where `σ = φ^{-1/2}` and `φ` is the golden ratio, so every matrix identity below is decided in
exact arithmetic over that ring and then transported to the complex matrices along the embedding
`goldenToComplex`. A golden integer is written in the coordinates `⟨c₀, c₁, c₂, c₃⟩` of
`c₀ + c₁ σ + c₂ σ² + c₃ σ³`; the values occurring in the gauge are

`1 = ⟨1, 0, 0, 0⟩`, `σ = φ^{-1/2} = ⟨0, 1, 0, 0⟩`, `φ⁻¹ = σ² = ⟨0, 0, 1, 0⟩`,
`φ^{-3/2} = σ³ = ⟨0, 0, 0, 1⟩`, `φ⁻² = σ⁴ = ⟨1, 0, -1, 0⟩`, `φ^{-5/2} = σ⁵ = ⟨0, 1, 0, -1⟩`,
`φ⁻³ = σ⁶ = ⟨-1, 0, 2, 0⟩`, `φ^{-7/2} = σ⁷ = ⟨0, -1, 0, 2⟩`, `φ^{1/2} = σ⁻¹ = ⟨0, 1, 0, 1⟩`,
`φ = σ⁻² = ⟨1, 0, 1, 0⟩`, `φ^{3/2} = ⟨0, 2, 0, 1⟩` and `φ² = ⟨2, 0, 1, 0⟩`.

## Main definitions

* `FibonacciCompression.fibOne`, `FibonacciCompression.fibTau`: the two blocks of the Fibonacci
  algebra, of bond dimensions two and three.
* `FibonacciCompression.fibStack`: the stacked product tensor of `τ ⊗ τ`, of bond dimension nine.
* `FibonacciCompression.fibFusionRight`, `FibonacciCompression.fibFusionLeft`: the fusion tensors
  of the Fibonacci algebra, one pair for each block.

## Main results

* `FibonacciCompression.fibTauMPS_apply_one`, `FibonacciCompression.fibTauMPS_apply_three`: the
  complex one-site matrices of the `τ` block are the recorded rows of the Fibonacci vertex
  weight.
* `FibonacciCompression.fibOneMPS_isNormal`, `FibonacciCompression.fibTauMPS_isNormal`: both
  blocks are normal, their length-three words spanning the full matrix algebra.
* `FibonacciCompression.fibonacci_compression`: the multi-block compression datum of Theorem 7.7
  with two target slots and four zero slots.
* `FibonacciCompression.fibStack_trace_evalWord`: the word-trace form of the fusion rule
  `O_τ O_τ = O_1 + O_τ`.
* `FibonacciCompression.fibonacci_fusion_rule`: the same fusion rule as an identity of periodic
  operators at every positive system size.
* `FibonacciCompression.fibonacci_isReduction`: the biorthogonal compression pair of each block.
* `FibonacciCompression.fibonacci_dim_eq`: the dimension count `9 = 2 + 3 + 4`.
* `FibonacciCompression.fibonacci_remainder_eq_zero`: the remainder vanishes, so the extension
  splits.
* `FibonacciCompression.fibStack_mul_fusionRight`,
  `FibonacciCompression.fusionLeft_mul_fibStack`: the fusion tensors intertwine the stacked
  tensor with each block site by site.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*

## Provenance

The placement of the F-symbols in the `τ` block was fixed by the search recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §3.1; the two tensors, the compression
datum and its exact-arithmetic verification are recorded in §3.2–§3.3 of that file and in
`Notes/OpenProblemsTN/checks/p5_more_examples_verify.py`. These are verification records, not the
source.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor

/-! ### The two blocks of the Fibonacci algebra -/

/-- The `τ` tensor of the Fibonacci string-net matrix product operator, of bond dimension three
(arXiv:1511.08090, App. D.1; entries recorded in the data file, §3.2). Its letters are the pairs
`(x', x)` of outgoing and incoming labels, `0` being the trivial label and `1` being `τ`, and its
one-site matrix at the letter `p` carries the row of the reduced vertex weight
`[[0, φ⁻¹, σ], [1, 0, 1], [1, σ, -φ⁻¹]]` indexed by `p`. The placement of these entries is the
Local fix (provenance) of the module header. -/
def fibTauGolden : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) GoldenInt
  | 0, 1 => !![0, sigma ^ 2, sigma; 0, 0, 0; 0, 0, 0]
  | 1, 0 => !![0, 0, 0; 1, 0, 1; 0, 0, 0]
  | 1, 1 => !![0, 0, 0; 0, 0, 0; 1, sigma, -sigma ^ 2]
  | _, _ => 0

/-- The trivial tensor of the Fibonacci string-net matrix product operator, of bond dimension
two: the projector onto the admissible configurations, carrying the admissibility matrix
`[[0, 1], [1, 1]]` on its diagonal letters (data file §3.2). -/
def fibOneGolden : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) GoldenInt
  | 0, 0 => !![0, 1; 0, 0]
  | 1, 1 => !![0, 0; 1, 1]
  | _, _ => 0

/-- The `τ` block as a matrix product operator tensor. -/
def fibTau : MPOTensor 2 3 := fun i j => complexOfGolden (fibTauGolden i j)

/-- The trivial block as a matrix product operator tensor. -/
def fibOne : MPOTensor 2 2 := fun i j => complexOfGolden (fibOneGolden i j)

/-- The `τ` block read as a tensor over the pair alphabet `Fin 4`. -/
def fibTauMPS : MPSTensor 4 3 := fibTau.toMPSTensor

/-- The trivial block read as a tensor over the pair alphabet `Fin 4`. -/
def fibOneMPS : MPSTensor 4 2 := fibOne.toMPSTensor

/-- The golden matrices of the pair-alphabet `τ` block, in the letter order
`(0,0), (0,1), (1,0), (1,1)`. -/
def fibTauGoldenMPS : Fin 4 → Matrix (Fin 3) (Fin 3) GoldenInt
  | 0 => 0
  | 1 => !![0, sigma ^ 2, sigma; 0, 0, 0; 0, 0, 0]
  | 2 => !![0, 0, 0; 1, 0, 1; 0, 0, 0]
  | 3 => !![0, 0, 0; 0, 0, 0; 1, sigma, -sigma ^ 2]

/-- The golden matrices of the pair-alphabet trivial block. -/
def fibOneGoldenMPS : Fin 4 → Matrix (Fin 2) (Fin 2) GoldenInt
  | 0 => !![0, 1; 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 0; 1, 1]

theorem fibTauMPS_eq (a : Fin 4) : fibTauMPS a = complexOfGolden (fibTauGoldenMPS a) := by
  fin_cases a <;> rfl

theorem fibOneMPS_eq (a : Fin 4) : fibOneMPS a = complexOfGolden (fibOneGoldenMPS a) := by
  fin_cases a <;> rfl

/-- The complex one-site matrices of the `τ` block are the recorded ones: the letter `(1, τ)`
carries the first row `[0, φ⁻¹, φ^{-1/2}]` of the reduced vertex weight, with
`φ^{-1/2} = √((√5 - 1)/2)` (data file §3.2). -/
theorem fibTauMPS_apply_one :
    fibTauMPS 1 =
      !![0, goldenSigmaComplex ^ 2, goldenSigmaComplex; 0, 0, 0; 0, 0, 0] := by
  rw [fibTauMPS_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [complexOfGolden, fibTauGoldenMPS]

/-- The letter `(τ, τ)` of the `τ` block carries the third row `[1, φ^{-1/2}, -φ⁻¹]` of the
reduced vertex weight (data file §3.2). -/
theorem fibTauMPS_apply_three :
    fibTauMPS 3 =
      !![0, 0, 0; 0, 0, 0; 1, goldenSigmaComplex, -goldenSigmaComplex ^ 2] := by
  rw [fibTauMPS_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [complexOfGolden, fibTauGoldenMPS]

theorem fibTauMPS_eq_complexOfGolden :
    fibTauMPS = fun a => complexOfGolden (fibTauGoldenMPS a) := funext fibTauMPS_eq

theorem fibOneMPS_eq_complexOfGolden :
    fibOneMPS = fun a => complexOfGolden (fibOneGoldenMPS a) := funext fibOneMPS_eq

/-! ### Normality of the two blocks

Both blocks are normal at word length three (data file §3.2). For the `τ` block the words
`[i + 1, 3, k + 1]` evaluate to a nonzero multiple of the matrix `e_i r_k` built from the `i`-th
coordinate vector and the `k`-th row `r_k` of the vertex weight; those rows are a basis, so the
nine such words span the full three-by-three matrix algebra. For the trivial block four words of
length three already span the two-by-two matrix algebra.
-/

/-- The coefficients expressing the matrix unit `E_{ij}` of the `τ` block as a combination of the
length-three words `[i + 1, 3, k + 1]`, `k = 0, 1, 2`. -/
def fibTauUnitCoeff : Fin 3 → Fin 3 → Fin 3 → GoldenInt
  | 0, 0 => ![⟨0, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩]
  | 0, 1 => ![⟨0, 1, 0, 1⟩, ⟨0, -1, 0, 0⟩, ⟨-1, 0, 0, 0⟩]
  | 0, 2 => ![⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩]
  | 1, 0 => ![⟨0, 0, 0, -1⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩]
  | 1, 1 => ![⟨1, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩]
  | 1, 2 => ![⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 0⟩]
  | 2, 0 => ![⟨0, 1, 0, 0⟩, ⟨0, -1, 0, -1⟩, ⟨1, 0, 0, 0⟩]
  | 2, 1 => ![⟨-1, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 1⟩]
  | 2, 2 => ![⟨0, -1, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨-1, 0, 0, 0⟩]

/-- The four length-three words of the trivial block used to span the two-by-two matrix
algebra. -/
def fibOneWord : Fin 4 → Fin 3 → Fin 4
  | 0 => ![0, 3, 3]
  | 1 => ![0, 3, 0]
  | 2 => ![3, 0, 3]
  | 3 => ![3, 3, 0]

/-- The coefficients expressing the matrix unit `E_{ij}` of the trivial block as a combination of
the four words of `fibOneWord`. -/
def fibOneUnitCoeff : Fin 2 → Fin 2 → Fin 4 → GoldenInt
  | 0, 0 => ![1, -1, 0, 0]
  | 0, 1 => ![0, 1, 0, 0]
  | 1, 0 => ![0, 0, 1, -1]
  | 1, 1 => ![0, 0, 0, 1]

/-- **The `τ` block is normal.** Its length-three words span the full three-by-three matrix
algebra (data file §3.2). -/
theorem fibTauMPS_isNormal : Kraus.IsNormal fibTauMPS :=
  isNormal_of_golden_single fibTauGoldenMPS fibTauMPS_eq (by norm_num : 0 < 3)
    (fun i _ k => ![i.succ, 3, k.succ]) fibTauUnitCoeff (by decide +kernel)

/-- **The trivial block is normal.** Its length-three words span the full two-by-two matrix
algebra (data file §3.2). -/
theorem fibOneMPS_isNormal : Kraus.IsNormal fibOneMPS :=
  isNormal_of_golden_single fibOneGoldenMPS fibOneMPS_eq (by norm_num : 0 < 3)
    (fun _ _ k => fibOneWord k) fibOneUnitCoeff (by decide +kernel)

/-! ### The stacked tensor of the square -/

/-- The stacked product tensor `B^{(x', x)} = ∑_m B_τ^{(x', m)} ⊗ B_τ^{(m, x)}` of the square of
the `τ` family, of bond dimension nine (data file §3.3). -/
def fibStack : MPSTensor 4 9 := (MPOTensor.mulTensor fibTau fibTau).toMPSTensor

/-- The golden matrices of the stacked product tensor, in the bond order `3 i + j`. -/
def fibStackGolden : Fin 4 → Matrix (Fin 9) (Fin 9) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩,
         ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩, ⟨-1, 0, 1, 0⟩,
         ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, -1⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩,
         ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, -1⟩,
         ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, -1⟩, ⟨1, 0, -1, 0⟩]

theorem fibStack_eq (a : Fin 4) : fibStack a = complexOfGolden (fibStackGolden a) := by
  have h : fibStack a = complexOfGolden (mulGoldenTensor fibTauGolden fibTauGolden
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfGolden fibTauGolden fibTauGolden _ _
  have hgolden : ∀ b : Fin 4, mulGoldenTensor fibTauGolden fibTauGolden
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) = fibStackGolden b := by
    decide +kernel
  rw [h, hgolden]

/-! ### The gauge -/

/-- The inverse change of bond coordinates, `G⁻¹ = [V_1 | V_τ | K]`: its columns are the two
fusion tensors of the blocks followed by a basis of the four-dimensional subspace annihilated by
every letter (data file §3.3). -/
def fibGaugeInvGolden : Matrix (Fin 9) (Fin 9) GoldenInt :=
  !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨1, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 1, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -2, 0, -1⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 1, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩, ⟨-1, 0, 0, 0⟩,
       ⟨0, -1, 0, -1⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 1⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩, ⟨2, 0, 1, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]

/-- The change of bond coordinates bringing every letter of the stacked tensor to block diagonal
form (data file §3.3). -/
def fibGaugeGolden : Matrix (Fin 9) (Fin 9) GoldenInt :=
  !![⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩,
       ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩,
       ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩;
     ⟨1, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 2, 0⟩, ⟨0, 0, 0, -1⟩,
       ⟨1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, -2⟩, ⟨1, 0, -1, 0⟩,
       ⟨0, -1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨-1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨1, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, 1, 0⟩,
       ⟨0, -1, 0, -1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 2, 0⟩, ⟨0, 0, 0, -1⟩,
       ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

theorem fibGauge_mul_inv : fibGaugeGolden * fibGaugeInvGolden = 1 := by decide +kernel

theorem fibGaugeInv_mul : fibGaugeInvGolden * fibGaugeGolden = 1 := by decide +kernel

theorem fibGaugeComplex_mul_inv :
    complexOfGolden fibGaugeGolden * complexOfGolden fibGaugeInvGolden = 1 := by
  rw [← complexOfGolden_mul, fibGauge_mul_inv, complexOfGolden_one]

theorem fibGaugeComplex_inv_mul :
    complexOfGolden fibGaugeInvGolden * complexOfGolden fibGaugeGolden = 1 := by
  rw [← complexOfGolden_mul, fibGaugeInv_mul, complexOfGolden_one]

/-! ### The blocks, the slots and the block coordinates -/

/-- The bond dimensions of the two target slots: two for the trivial block, three for the `τ`
block. -/
def fibBlockDim : Fin 2 → ℕ
  | 0 => 2
  | 1 => 3

/-- The two target blocks of the fusion `τ ⊗ τ = 1 ⊕ τ`, each with multiplicity one and
weight one. -/
def fibTargets : (s : Fin 2) → MPSTensor 4 (fibBlockDim s)
  | 0 => fibOneMPS
  | 1 => fibTauMPS

/-- The golden matrices of the two target blocks. -/
def fibTargetsGolden :
    (s : Fin 2) → Fin 4 → Matrix (Fin (fibBlockDim s)) (Fin (fibBlockDim s)) GoldenInt
  | 0 => fibOneGoldenMPS
  | 1 => fibTauGoldenMPS

theorem fibTargets_eq (s : Fin 2) (a : Fin 4) :
    fibTargets s a = complexOfGolden (fibTargetsGolden s a) := by
  fin_cases s
  exacts [fibOneMPS_eq a, fibTauMPS_eq a]

/-- The slots of the fusion: both target blocks. -/
abbrev fibSlots : Finset (Fin 2) := Finset.univ

/-- The block ordering: the trivial block, the `τ` block, then the four zero slots. -/
def fibOrd : BlockIndex fibSlots 4 ≃ Fin 6 where
  toFun := Sum.elim (fun s => ![0, 1] s.1) ![2, 3, 4, 5]
  invFun
    | 0 => Sum.inl ⟨0, Finset.mem_univ 0⟩
    | 1 => Sum.inl ⟨1, Finset.mem_univ 1⟩
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
    | 4 => Sum.inr 2
    | 5 => Sum.inr 3
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The position of the first bond coordinate of each block. -/
def fibOffset : BlockIndex fibSlots 4 → ℕ :=
  Sum.elim (fun s => ![0, 2] s.1) ![5, 6, 7, 8]

/-- The bond coordinate attached to a graded coordinate. -/
def fibCoordNat (x : BlockSpace fibBlockDim fibSlots 4) : ℕ := fibOffset x.1 + (x.2 : ℕ)

theorem fibCoordNat_lt (x : BlockSpace fibBlockDim fibSlots 4) : fibCoordNat x < 9 := by
  revert x
  decide +kernel

/-- The labelling of the nine bond coordinates by the graded block space. -/
def fibCoord : BlockSpace fibBlockDim fibSlots 4 ≃ Fin 9 where
  toFun x := ⟨fibCoordNat x, fibCoordNat_lt x⟩
  invFun
    | 0 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, ⟨1, by decide⟩⟩
    | 2 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨1, by decide⟩⟩
    | 4 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨2, by decide⟩⟩
    | 5 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
    | 6 => ⟨Sum.inr 1, ⟨0, by decide⟩⟩
    | 7 => ⟨Sum.inr 2, ⟨0, by decide⟩⟩
    | 8 => ⟨Sum.inr 3, ⟨0, by decide⟩⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The gauge of the Fibonacci fusion. -/
def fibGauge : (Fin 9 → ℂ) ≃ₗ[ℂ] (BlockSpace fibBlockDim fibSlots 4 → ℂ) :=
  gaugeOfMatrix fibCoord (complexOfGolden fibGaugeGolden) (complexOfGolden fibGaugeInvGolden)
    fibGaugeComplex_mul_inv fibGaugeComplex_inv_mul

/-- The letters of the stacked tensor in the block coordinates: block diagonal, with the trivial
block, the `τ` block and four one-by-one zero blocks on the diagonal (data file §3.3). -/
def fibConjGolden : Fin 4 → Matrix (Fin 9) (Fin 9) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
         ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

/-- Every letter of the stacked tensor carries the adapted basis into itself, block by block: the
core identity of the example, from which the compression datum and the sitewise intertwiners both
follow. -/
theorem fibStack_mul_gaugeInv (i : Fin 4) :
    fibStackGolden i * fibGaugeInvGolden = fibGaugeInvGolden * fibConjGolden i := by
  revert i
  decide +kernel

theorem fibStack_conj_golden (i : Fin 4) :
    fibGaugeGolden * fibStackGolden i * fibGaugeInvGolden = fibConjGolden i := by
  rw [Matrix.mul_assoc, fibStack_mul_gaugeInv, ← Matrix.mul_assoc, fibGauge_mul_inv,
    Matrix.one_mul]

theorem fibStack_conjMatrix (i : Fin 4) :
    conjMatrix fibGauge (fibStack i) =
      (complexOfGolden (fibConjGolden i)).submatrix fibCoord fibCoord := by
  rw [fibGauge, conjMatrix_gaugeOfMatrix, fibStack_eq, ← complexOfGolden_mul,
    ← complexOfGolden_mul, fibStack_conj_golden]

/-! ### The compression datum -/

private theorem fibStack_triangular_golden (i : Fin 4)
    (x y : BlockSpace fibBlockDim fibSlots 4) (h : fibOrd y.1 < fibOrd x.1) :
    fibConjGolden i (fibCoord x) (fibCoord y) = 0 := by
  revert i x y
  decide +kernel

private theorem fibStack_matched_golden (i : Fin 4) (s : Fin 2) (p q : Fin (fibBlockDim s)) :
    fibConjGolden i (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩) = fibTargetsGolden s i p q := by
  revert i
  fin_cases s <;> revert p q <;> decide +kernel

private theorem fibStack_unmatched_golden (i : Fin 4) (t : Fin 4) (p q : Fin 1) :
    fibConjGolden i (fibCoord ⟨Sum.inr t, p⟩) (fibCoord ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q
  decide +kernel

/-- **The multi-block asymmetric compression datum of the Fibonacci fusion** (P5 note,
Theorem 7.7, clauses (i)–(iii); data file §3.3). The stacked tensor of `τ ⊗ τ` compresses onto the
trivial block and the `τ` block, with four one-dimensional zero slots left over. -/
def fibonacci_compression : MultiBlockCompression fibStack fibSlots fibTargets :=
  MultiBlockCompression.ofGolden 4 fibOrd fibCoord fibStackGolden fibStack_eq fibTargetsGolden
    fibTargets_eq fibGaugeGolden fibGaugeInvGolden fibGauge_mul_inv fibGaugeInv_mul fibConjGolden
    fibStack_mul_gaugeInv fibStack_triangular_golden
    (fun i s _ p q => fibStack_matched_golden i s p q) fibStack_unmatched_golden

/-! ### Consequences -/

/-- **The fusion rule `O_τ O_τ = O_1 + O_τ` at the level of word traces** (data file §3.3): at
every positive length the periodic operator of the stacked tensor is the sum of the periodic
operators of the two blocks. -/
theorem fibStack_trace_evalWord (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord fibStack w) =
      Matrix.trace (Kraus.evalWord fibOneMPS w) + Matrix.trace (Kraus.evalWord fibTauMPS w) := by
  have h := fibonacci_compression.trace_evalWord_eq_sum w hw
  rw [show fibSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
  exact h

/-- **The Fibonacci fusion rule** `O_τ O_τ = O_1 + O_τ` as an identity of periodic operators
(data file §3.1). At every positive system size the square of the `τ` operator is the sum of the
admissibility projector and the `τ` operator itself: this is the fusion `τ ⊗ τ = 1 ⊕ τ` of the
Fibonacci category, realised on the matrix product operator algebra. -/
theorem fibonacci_fusion_rule (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo fibTau L * MPOTensor.mpo fibTau L =
      MPOTensor.mpo fibOne L + MPOTensor.mpo fibTau L := by
  rw [← MPOTensor.mpo_mulTensor]
  ext σ τ
  rw [Matrix.add_apply, MPOTensor.mpo_apply_toMPSTensor, MPOTensor.mpo_apply_toMPSTensor,
    MPOTensor.mpo_apply_toMPSTensor]
  exact fibStack_trace_evalWord _ (MPOTensor.ofFn_pairConfig_ne_nil hL σ τ)

/-- The matrix-product-vector form of the fusion rule: at every positive system size the vector
of the stacked tensor is the sum of the vectors of the two blocks. -/
theorem fibStack_mpv (N : ℕ) (hN : 0 < N) (σ : Fin N → Fin 4) :
    mpv fibStack σ = mpv fibOneMPS σ + mpv fibTauMPS σ := by
  have h := fibonacci_compression.mpv_eq_sum N hN σ
  rw [show fibSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
  exact h

/-- **Biorthogonal compression onto each of the two blocks** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem fibonacci_isReduction (s : {s // s ∈ fibSlots}) :
    IsReduction fibStack (fibTargets s.1) (fibonacci_compression.left s)
      (fibonacci_compression.right s) :=
  fibonacci_compression.isReduction s

/-- The two blocks are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem fibonacci_left_mul_right_of_ne {s t : {s // s ∈ fibSlots}} (h : s ≠ t) :
    fibonacci_compression.left s * fibonacci_compression.right t = 0 :=
  fibonacci_compression.left_mul_right_of_ne h

/-- **The dimension count** `9 = 2 + 3 + 4` (P5 note, Theorem 7.7(vii)). -/
theorem fibonacci_dim_eq : (9 : ℕ) = ∑ s ∈ fibSlots, fibBlockDim s + 4 :=
  fibonacci_compression.dim_eq

/-- **Nilpotency of the remainder** (P5 note, Theorem 7.7(vi)): a product of six remainder
matrices vanishes. -/
theorem fibonacci_evalWord_remainder_eq_zero (w : List (Fin 4)) (hw : 6 ≤ w.length) :
    Kraus.evalWord fibonacci_compression.remainder w = 0 := by
  refine fibonacci_compression.evalWord_remainder_eq_zero w ?_
  change (2 : ℕ) + 4 ≤ w.length
  omega

private theorem fibStack_offDiagonal_golden (i : Fin 4)
    (x y : BlockSpace fibBlockDim fibSlots 4) (h : x.1 ≠ y.1) :
    fibConjGolden i (fibCoord x) (fibCoord y) = 0 := by
  revert i x y
  decide +kernel

/-- **The remainder vanishes**: the conjugated letters are block diagonal, not merely block
triangular, so the extension splits completely (data file §3.3). -/
theorem fibonacci_remainder_eq_zero (i : Fin 4) : fibonacci_compression.remainder i = 0 :=
  fibonacci_compression.remainder_eq_zero_of_goldenGauge (hG := fibGauge_mul_inv)
    (hG' := fibGaugeInv_mul) rfl fibStack_eq fibStack_mul_gaugeInv fibStack_offDiagonal_golden i

/-! ### The fusion tensors -/

/-- The fusion tensors of the Fibonacci algebra, one for each block: the columns of the adapted
basis carrying the block (arXiv:1511.08090, App. D.1; data file §3.3). -/
def fibFusionRight : (s : Fin 2) → Matrix (Fin 9) (Fin (fibBlockDim s)) GoldenInt
  | 0 => !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 1, 0, 1⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1 => !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]

/-- The compression maps of the Fibonacci algebra, one for each block: the rows of the gauge
carrying the block (data file §3.3). -/
def fibFusionLeft : (s : Fin 2) → Matrix (Fin (fibBlockDim s)) (Fin 9) GoldenInt
  | 0 => !![⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩,
       ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩,
       ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩]
  | 1 => !![⟨1, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 2, 0⟩, ⟨0, 0, 0, -1⟩,
       ⟨1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, -2⟩, ⟨1, 0, -1, 0⟩,
       ⟨0, -1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨-1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨1, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩]

theorem fibonacci_right_eq (s : {s // s ∈ fibSlots}) :
    fibonacci_compression.right s = complexOfGolden (fibFusionRight s.1) := by
  have hgolden : ∀ t : Fin 2, fibGaugeInvGolden.submatrix id
      (fun j => fibCoord ⟨Sum.inl ⟨t, Finset.mem_univ t⟩, j⟩) = fibFusionRight t := by
    decide +kernel
  have h : fibonacci_compression.right s =
      (complexOfGolden fibGaugeInvGolden).submatrix id fun j => fibCoord ⟨Sum.inl s, j⟩ :=
    fibonacci_compression.right_gaugeOfMatrix (hG := fibGaugeComplex_mul_inv)
      (hG' := fibGaugeComplex_inv_mul) rfl s
  rw [h, ← hgolden]
  rfl

theorem fibonacci_left_eq (s : {s // s ∈ fibSlots}) :
    fibonacci_compression.left s = complexOfGolden (fibFusionLeft s.1) := by
  have hgolden : ∀ t : Fin 2, fibGaugeGolden.submatrix
      (fun i => fibCoord ⟨Sum.inl ⟨t, Finset.mem_univ t⟩, i⟩) id = fibFusionLeft t := by
    decide +kernel
  have h : fibonacci_compression.left s =
      (complexOfGolden fibGaugeGolden).submatrix (fun i => fibCoord ⟨Sum.inl s, i⟩) id :=
    fibonacci_compression.left_gaugeOfMatrix (hG := fibGaugeComplex_mul_inv)
      (hG' := fibGaugeComplex_inv_mul) rfl s
  rw [h, ← hgolden s.1]
  rfl

private theorem fibStack_mul_fusionRight_golden (i : Fin 4) (s : Fin 2) :
    fibStackGolden i * fibFusionRight s = fibFusionRight s * fibTargetsGolden s i := by
  revert i
  fin_cases s <;> decide +kernel

private theorem fusionLeft_mul_fibStack_golden (i : Fin 4) (s : Fin 2) :
    fibFusionLeft s * fibStackGolden i = fibTargetsGolden s i * fibFusionLeft s := by
  revert i
  fin_cases s <;> decide +kernel

/-- **The fusion tensors are sitewise right intertwiners** (data file §3.3): each letter of the
stacked tensor carries the fusion tensor of a block through to the same letter of that block. -/
theorem fibStack_mul_fusionRight (i : Fin 4) (s : {s // s ∈ fibSlots}) :
    fibStack i * fibonacci_compression.right s =
      fibonacci_compression.right s * fibTargets s.1 i := by
  rw [fibonacci_right_eq, fibStack_eq, fibTargets_eq, ← complexOfGolden_mul,
    ← complexOfGolden_mul, fibStack_mul_fusionRight_golden]

/-- **The compression maps are sitewise left intertwiners** (data file §3.3). -/
theorem fusionLeft_mul_fibStack (i : Fin 4) (s : {s // s ∈ fibSlots}) :
    fibonacci_compression.left s * fibStack i =
      fibTargets s.1 i * fibonacci_compression.left s := by
  rw [fibonacci_left_eq, fibStack_eq, fibTargets_eq, ← complexOfGolden_mul,
    ← complexOfGolden_mul, fusionLeft_mul_fibStack_golden]

end FibonacciCompression
