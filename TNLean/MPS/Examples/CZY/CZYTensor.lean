/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.CZX.CZXTensor
import TNLean.MPS.MPDO.OperatorCyclicSum

/-!
# CZY: the anomalous `ℤ₂` operator of the Levin–Gu edge and its stacked square

**Source.** Liu, Molnár, Sun, Verstraete, Kato, Lootens, *Trading Mathematical for Physical
Simplicity: Bialgebraic Structures in Matrix Product Operator Symmetries*, arXiv:2509.03600,
`References/2509.03600/main.tex` lines 198–223: the symmetry `U_CZY = ∏ CZ_{i,i+1} ∏ Z_i X_i`
of the Levin–Gu edge Hamiltonian is the matrix product operator whose only nonzero components
are `A_1^{01} = [[1,1],[0,0]]` and `A_1^{10} = [[0,0],[-1,1]]`, the first physical index being
the output (ket) and the second the input (bra); the product of two copies is the bond-four
tensor `Ã_0^{00} = A_1^{01} ⊗ A_1^{10}`, `Ã_0^{11} = A_1^{10} ⊗ A_1^{01}`, all other
components zero.

**Formalized here.** The tensor over the integers and the complexes, in the source's index
convention (which is also the convention of `MPOTensor`); its periodic operator entrywise;
and the stacked tensor as an explicit integer tensor over the pair alphabet
`(0,0), (0,1), (1,0), (1,1)`.

On a periodic chain of `N > 0` qubits the tensor generates
`U_N |t⟩ = (-1)^{#\{n : s_n = 1, s_{n+1} = 0\}} |s⟩` with `s = 1 - t` the spin flip of `t`,
indices modulo `N`. This is the sign of the source's gate product `∏ CZ ∏ Z X` with the
cyclic convention `CZ_{1,1} = Z` at `N = 1`; the gate product itself is not formalized here.

## Main definitions

* `CZYCompression.czyIntTensor`, `CZYCompression.czyTensor`: the bond-two tensor `A_1`.
* `CZYCompression.czySquareInt`, `CZYCompression.czySquare`: the stacked bond-four tensor
  `Ã_0` in the pair-alphabet view.

## Main results

* `CZYCompression.mpo_czyTensor_apply`: the periodic operator of `A_1` entrywise.
* `CZYCompression.czySquare_eq`: the stacked tensor is the coercion of an explicit integer
  tensor, in agreement with the source's `Ã_0`.

## References

- [arXiv:2509.03600](https://arxiv.org/abs/2509.03600) -- Y. Liu, A. Molnár, X.-Q. Sun,
  F. Verstraete, K. Kato, L. Lootens, *Trading Mathematical for Physical Simplicity:
  Bialgebraic Structures in Matrix Product Operator Symmetries*
-/

noncomputable section

open scoped BigOperators Matrix

namespace CZYCompression

open MPSTensor

/-! ### The bond-two tensor -/

/-- The integer tensor `A_1` of the CZY symmetry: `A_1^{01} = [[1,1],[0,0]]`,
`A_1^{10} = [[0,0],[-1,1]]`, and zero otherwise (arXiv:2509.03600, main.tex lines 203–218). -/
def czyIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 1 => !![1, 1; 0, 0]
  | 1, 0 => !![0, 0; -1, 1]
  | _, _ => 0

/-- The CZY tensor `A_1` as a matrix product operator tensor (arXiv:2509.03600, main.tex
lines 203–218). -/
def czyTensor : MPOTensor 2 2 := fun i j => complexOfInt (czyIntTensor i j)

/-- The bond-two coordinates of `A_1`: the output `i` is the flip of the input `j`, the
incoming bond is forced to be `i`, and the outgoing bond `r` contributes `(-1)^{i (1 - r)}`. -/
theorem czyTensor_apply (i j l r : Fin 2) :
    czyTensor i j l r =
      if i = j.rev ∧ l = i then (-1 : ℂ) ^ (i.val * r.rev.val) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [czyTensor, czyIntTensor, complexOfInt, Fin.rev]

/-- **The periodic CZY operator entrywise** (arXiv:2509.03600, main.tex lines 199–218). The
entry at `(s, t)` vanishes unless `s` is the spin flip of `t`, and then it is `-1` raised to
the number of sites `n` with `s_n = 1` and `s_{n+1} = 0`, indices modulo `N`. -/
theorem mpo_czyTensor_apply {N : ℕ} [NeZero N] (s t : Fin N → Fin 2) :
    MPOTensor.mpo czyTensor N s t =
      if s = (fun n => (t n).rev) then
        ∏ n : Fin N, (-1 : ℂ) ^ ((s n).val * (s (n + 1)).rev.val) else 0 :=
  MPOTensor.mpo_apply_of_forced_left_bond (β := fun i _ => i) czyTensor_apply s t

/-! ### The stacked tensor -/

/-- The integer matrices of the stacked tensor `Ã_0^{ik} = ∑_j A_1^{ij} ⊗ A_1^{jk}` of bond
dimension four, in the pair-alphabet order `(0,0), (0,1), (1,0), (1,1)`: the letter `(0,0)` is
`A_1^{01} ⊗ A_1^{10}`, the letter `(1,1)` is `A_1^{10} ⊗ A_1^{01}`, and the mixed letters vanish
(arXiv:2509.03600, main.tex lines 219–223). -/
def czySquareInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 0, 0; -1, 1, -1, 1; 0, 0, 0, 0; 0, 0, 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 0, 0, 0; 0, 0, 0, 0; -1, -1, 1, 1; 0, 0, 0, 0]

/-- The stacked tensor `Ã_0` in the pair-alphabet view (arXiv:2509.03600, main.tex
lines 219–223). -/
def czySquare : MPSTensor 4 4 := (MPOTensor.mulTensor czyTensor czyTensor).toMPSTensor

theorem czySquare_eq (a : Fin 4) : czySquare a = complexOfInt (czySquareInt a) := by
  have h : czySquare a = complexOfInt (mulIntTensor czyIntTensor czyIntTensor
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfRing _ czyIntTensor czyIntTensor _ _
  have hint : ∀ b : Fin 4, mulIntTensor czyIntTensor czyIntTensor
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) = czySquareInt b := by
    decide
  rw [h, hint]

end CZYCompression
