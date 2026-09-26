/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Instance
import TNLean.MPS.MPDO.DiagonalDressing
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Anomalous `ℤ₂ × ℤ₂` symmetry: an exact representation by normal tensors

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection "Periodic
boundary condition case", `Papers/2203.12563/REsubmission.tex` lines 2200--2224: for a finite
group `G` and a three-cocycle `ω`, the operators `U_g` of the construction form a periodic
matrix product operator representation of `G`, `U_g U_h = U_{gh}`. The type-II three-cocycle
of `ℤ₂ × ℤ₂` is `ω_II(a b^i, a^j b, a^k b) = −1` with all other values `+1` (line 1848), which
in the coordinates `a = (1,0)`, `b = (0,1)` is `(−1)^{a₁ b₂ c₂}`. Neither source prints the
two-qubit tensors used here.

**Formalized here.** The two-qubit tensors `M_g = symTensor g` of
`AnomalousCondensationZ2Z2` give periodic operators `U_g^{sym} = U_g^{ω} (∏_i Z_i^{(2)})^{g₁}`
(`Z2Z2Condensation.mpo_symTensor_eq_groupCocycle`), which multiply only up to the signs
`λ(g,h)^N` of `mpo_symTensor_mul`. Dressing each tensor on its input leg by the same on-site
operator `(Z^{(2)})^{g₁}`, the Pauli `Z` on the second qubit when `g₁ = 1`, removes the
dressing, since `(Z^{(2)})² = 1`. The dressed tensor `M'_g` multiplies the letter of `M_g` with
input label `i` by the sign `(−1)^{g₁ i₂}`. It has the bond dimension of `M_g`, its periodic
operators are exactly the operators `U_g^{ω}` of the construction for `ω = (−1)^{a₁ b₂ c₂}`,
and these multiply exactly as `ℤ₂ × ℤ₂` on every nonempty ring. Rescaling letters by signs
does not change the spans of words, so the dressed doubled-index tensors are normal. The four
dressed tensors are therefore an exact normal representation of `ℤ₂ × ℤ₂`, to which the
anomaly three-cochain of arXiv:2502.20257 applies. Normality is proved for the dressed tensors
themselves, of bond dimensions one and two, not for the bond-four tensor of the construction.

## Main definitions

* `Z2Z2Condensation.secondZSign`: the diagonal of the on-site dressing `(Z^{(2)})^{g₁}`.
* `Z2Z2Condensation.kleinTensor`: the dressed tensor `M'_g`.
* `Z2Z2Condensation.kleinFamily`: the family `g ↦ M'_g` indexed by `ℤ₂ × ℤ₂`.

## Main results

* `Z2Z2Condensation.mpo_kleinTensor`: the periodic operators of `M'_g` are those of the
  construction for `(−1)^{a₁ b₂ c₂}`.
* `Z2Z2Condensation.kleinTensor_isNormal`: the dressed doubled-index tensors are normal.
* `Z2Z2Condensation.kleinFamily_isNormalRepresentation`: the dressed tensors are an exact
  representation of `ℤ₂ × ℤ₂` by normal tensors.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- Franco Rubio, Bochniak, Cirac,
  *Symmetry defects and gauging for quantum states with matrix product unitary symmetries*

## Provenance
The tensors `symTensor g` are representatives constructed in this development of the mixed
type-II class, recorded with their exact checks in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1--3; these are verification
records, not the source.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Z2Z2Condensation

open MPOTensor MPOTensor.GroupCocycle TNLean.Algebra.ScalarThreeCochain

/-- The diagonal of the on-site dressing `(Z^{(2)})^{g₁}` on one two-qubit site: the sign
`(−1)^{g₁ a₂}` at the site label `a`, whose second qubit is `a₂ = a.val % 2`. -/
def secondZSign (g : Multiplicative (ZMod 2 × ZMod 2)) (a : Fin 4) : ℂ :=
  (-1) ^ ((Multiplicative.toAdd g).1.val * (a.val % 2))

/-- The dressing sign is a power of `−1`, hence nonzero. -/
theorem secondZSign_ne_zero (g : Multiplicative (ZMod 2 × ZMod 2)) (a : Fin 4) :
    secondZSign g a ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/-- The Kronecker power of the on-site dressing is the chain dressing `secondZDressing`. -/
theorem diagonal_prod_secondZSign (g : Multiplicative (ZMod 2 × ZMod 2)) (N : ℕ) :
    (Matrix.diagonal fun t : Fin N → Fin 4 ↦ ∏ k, secondZSign g (t k)) = secondZDressing g N := by
  rw [secondZDressing]
  congr 1
  funext t
  simp only [secondZSign, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

/-- The chain dressing `(∏_i Z_i^{(2)})^{g₁}` squares to the identity. -/
theorem secondZDressing_mul_self (g : Multiplicative (ZMod 2 × ZMod 2)) (N : ℕ) :
    secondZDressing g N * secondZDressing g N = 1 := by
  rw [secondZDressing, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext t
  rw [← mul_pow]
  norm_num

/-- **The dressed two-qubit tensor** `M'_g`: the letter of `symTensor g` with input label `i`
multiplied by the sign `(−1)^{g₁ i₂}`, that is, `M_g` followed by the on-site dressing
`(Z^{(2)})^{g₁}` on its input leg. -/
def kleinTensor (g : Multiplicative (ZMod 2 × ZMod 2)) : MPOTensor 4 (bondDim (kleinEquiv g)) :=
  (symTensor (kleinEquiv g)).mulDiagonal (secondZSign g)

/-- **The dressed tensors realize the construction for `(−1)^{a₁ b₂ c₂}`**: on every nonempty
periodic chain, the periodic operator of `M'_g` is the operator `U_g^{ω}` of the construction.

Source: arXiv:2203.12563, lines 2204--2222 (the operators `U_g` of the construction), for the
type-II cocycle `ω(a,b,c) = (−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂` (line 1848). -/
theorem mpo_kleinTensor (g : Multiplicative (ZMod 2 × ZMod 2)) {N : ℕ} [NeZero N] :
    mpo (kleinTensor g) N = mpo (tensor kleinEquiv kleinCocycle g) N := by
  rw [kleinTensor, mpo_mulDiagonal, diagonal_prod_secondZSign, mpo_symTensor_eq_groupCocycle,
    Matrix.mul_assoc, secondZDressing_mul_self, Matrix.mul_one]

/-- **The dressed doubled-index tensors are normal**: dressing rescales every letter of the
normal tensor `symMPS g` by a sign, which leaves the spans of words unchanged. -/
theorem kleinTensor_isNormal (g : Multiplicative (ZMod 2 × ZMod 2)) :
    Kraus.IsNormal (kleinTensor g).toMPSTensor := by
  rw [kleinTensor, isNormal_toMPSTensor_mulDiagonal_iff _ (secondZSign_ne_zero g),
    ← symMPS_eq_toMPSTensor]
  exact symMPS_isNormal _

/-- The family `g ↦ M'_g` of dressed two-qubit tensors indexed by `ℤ₂ × ℤ₂`, with bond
dimension one for `e, y` and two for `x, xy`. -/
def kleinFamily : GroupFamily (Multiplicative (ZMod 2 × ZMod 2)) 4 where
  bondDim g := bondDim (kleinEquiv g)
  bondDim_pos g := by
    generalize kleinEquiv g = a
    fin_cases a <;> decide
  tensor := kleinTensor

/-- **The dressed tensors are an exact representation of `ℤ₂ × ℤ₂` by normal tensors**: every
doubled-index tensor is normal, and `U'_g U'_h = U'_{gh}` on every nonempty periodic chain.

Source: arXiv:2203.12563, lines 2200--2224 (the construction represents `G` exactly), for the
cocycle of line 1848; the representation law is that of arXiv:2502.20257, lines 1403--1407. -/
theorem kleinFamily_isNormalRepresentation : kleinFamily.IsNormalRepresentation where
  isNormal := kleinTensor_isNormal
  operator_mul g h N hN := by
    have : NeZero N := ⟨hN.ne'⟩
    change mpo (kleinTensor g) N * mpo (kleinTensor h) N = mpo (kleinTensor (g * h)) N
    rw [mpo_kleinTensor, mpo_kleinTensor, mpo_kleinTensor]
    exact klein_operator_laws.2.2.1 g h N hN

end Z2Z2Condensation
