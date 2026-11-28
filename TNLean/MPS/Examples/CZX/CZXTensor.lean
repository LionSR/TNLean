/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import TNLean.MPS.FundamentalTheorem.Compression.ExplicitGauge
import TNLean.MPS.Operator.Product.OperatorProduct

/-!
# CZX: the undecorated matrix product operator and its stacked square

**Source.** Chen, Liu, Wen 2011 (arXiv:1106.4752), Section "Matrix Product Unitary Operators and
its relation to 3 cocycle", `References/1106.4752/source/dDSPTmodel.tex` lines 377–385: the
boundary symmetry of the CZX model is the bond-two matrix product unitary with
`T^{0,1} = |0⟩⟨+|`, `T^{1,0} = |1⟩⟨-|`, where `|±⟩ = |0⟩ ± |1⟩`.
Review: arXiv:2011.12127, Appendix A, "The CZX MPU", `Papers/2011.12127/TN-Review-main.tex`
lines 2582–2595: the same tensor, its letters `A^{01}`, `A^{10}`, injectivity, and the stacked
bond-four tensor `B^{00}`, `B^{11}`; the gate order `⊗ CZ ⊗ ⊗ X` is displayed at line 1472.

**Formalized here.** The bond-two tensor, over the integers and the complexes, with
`M^{ij} = δ_{i,1 ⊕ j} T_j`, `T_0 = [[1,0],[1,0]]` and `T_1 = [[0,1],[0,-1]]`; its normality
(the source's injectivity); and the stacked product `B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond
dimension four as an explicit integer tensor. The first physical index is the output row, so
the source letter `A^{ij}` is the transpose of `M^{ji}` here; this is a convention, not a gap.

On a periodic chain of `L > 0` qubits, let `D_L |t⟩ = (-1)^{∑_j t_j t_{j+1}} |t⟩`, with
indices modulo `L`. The tensor generates `U_L = X^{⊗ L} D_L`, the order of the review's
Appendix A (controlled-`Z` gates followed by Pauli `X`). The cyclic convention includes the
self-loop `D_1 = Z` and counts the two-site edge twice, giving `D_2 = I`. Unitarity and
`U_L² = (-1)^L I` at every positive length are proved in `CZXUnitary`. Chen–Liu–Wen (line 385)
and the review's line 1472 write the reverse order `D_L X^{⊗ L}`, which differs from this
operator by `(-1)^L`. The decorated, two-qubit-blocked convention of arXiv:2502.20257, in
`TNLean.MPS.Examples.CZX.Gauging.CZXTensor`, is a different tensor whose square is the identity.

## Main definitions

* `CZXCompression.czxIntTensor`, `CZXCompression.czxTensor`: the bond-two tensor over the
  integers and over the complexes, on the pair alphabet `Fin 2 × Fin 2`.
* `CZXCompression.identityTensor`: the bond-one identity tensor `δ`.
* `CZXCompression.negIdentityIntMPS`: the integer matrices of `-δ`.
* `CZXCompression.czxSquareInt`, `CZXCompression.czxSquare`: the stacked product tensor
  `B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond dimension four.

## Main results

* `CZXCompression.czxMPS_isNormal`: the bond-two tensor is normal, its length-two words
  spanning the full two-by-two matrix algebra.
* `CZXCompression.czxSquare_eq`: the stacked product tensor is the coercion of an explicit
  integer tensor.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752) -- X. Chen, Z.-X. Liu, X.-G. Wen,
  *2D symmetry protected topological orders and their protected gapless edge excitations*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- the decorated CZX convention

## Provenance

The integer presentation of the tensor and of its stacked square was first recorded in
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`, Example D
(`ex:p5ft-czx`, lines 996–1037); that note is a verification record, not the source.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace CZXCompression

open MPSTensor

/-! ### The bond-two tensor of the note -/

/-- The integer tensor `M^{ij} = δ_{i,1 ⊕ j} T_j` of the CZX symmetry on the pair alphabet
(construction note, `ex:p5ft-czx`). -/
def czxIntTensor : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 1) => !![0, 1; 0, -1]
  | (1, 0) => !![1, 0; 1, 0]
  | _ => 0

/-- The CZX tensor of the note as a matrix product operator tensor. -/
def czxTensor : MPOTensor 2 2 := fun ij => complexOfInt (czxIntTensor ij)

/-- The integer tensor of the identity operator, of bond dimension one. -/
def identityIntTensor : Fin 2 × Fin 2 → Matrix (Fin 1) (Fin 1) ℤ :=
  fun ij => if ij.1 = ij.2 then 1 else 0

/-- The identity operator as a matrix product operator tensor of bond dimension one. -/
def identityTensor : MPOTensor 2 1 := fun ij => complexOfInt (identityIntTensor ij)

/-- The integer matrices of the identity tensor carried with the weight `-1`. -/
def negIdentityIntMPS (a : Fin 2 × Fin 2) : Matrix (Fin 1) (Fin 1) ℤ := -identityIntTensor a

theorem negIdentityMPS_eq (a : Fin 2 × Fin 2) :
    ((-1 : ℂ) • identityTensor) a = complexOfInt (negIdentityIntMPS a) := by
  rw [negIdentityIntMPS, complexOfInt_neg]
  simp [identityTensor]

/-! ### Normality of the bond-two tensor -/

/-- **The bond-two tensor of the note is normal.** Its length-two words span the full
two-by-two matrix algebra (construction note, `ex:p5ft-czx`): twice each matrix unit is the sum
or the difference of `M^{10} M^{10}` and `M^{01} M^{10}` (first column) or of `M^{10} M^{01}` and
`M^{01} M^{01}` (second column). -/
theorem czxMPS_isNormal : Kraus.IsNormal czxTensor :=
  isNormal_of_complexOfRing_smul_single (Int.castRingHom ℂ) czxIntTensor (fun _ => rfl)
    (by norm_num : 0 < 2) (fun _ j k => ![![(1, 0), (0, 1)] k, ![(1, 0), (0, 1)] j])
    (fun i j => ![1, (-1) ^ (i + j : ℕ)])
    (c := 2) (by norm_num) (by decide)

/-! ### The stacked product tensor of Example D -/

/-- The integer matrices of the stacked product tensor
`B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond dimension four (construction note, `ex:p5ft-czx`). -/
def czxSquareInt : Fin 2 × Fin 2 → Matrix (Fin 4) (Fin 4) ℤ
  | (0, 0) => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | (1, 1) => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]
  | _ => 0

/-- The stacked product tensor of Example D. -/
def czxSquare : MPOTensor 2 4 := MPOTensor.mulTensor czxTensor czxTensor

theorem czxSquare_eq (a : Fin 2 × Fin 2) : czxSquare a = complexOfInt (czxSquareInt a) := by
  have h : czxSquare a = complexOfInt (mulIntTensor czxIntTensor czxIntTensor a) :=
    mulTensor_complexOfRing _ czxIntTensor czxIntTensor a
  have hint : ∀ b, mulIntTensor czxIntTensor czxIntTensor b = czxSquareInt b := by
    decide
  rw [h, hint]

end CZXCompression
