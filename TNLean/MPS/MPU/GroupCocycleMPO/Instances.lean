/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicExamples
import TNLean.Algebra.ScalarThreeCocycleCyclicTwoExamples
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXUnitary
import TNLean.MPS.MPU.GroupCocycleMPO

/-!
# Group matrix product operators from a three-cocycle: cyclic and Klein instances

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection "Periodic
boundary condition case", `Papers/2203.12563/REsubmission.tex` line 2224: for the nontrivial
three-cocycle of `ℤ₂` the periodic operator is `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`; line 2070:
`W_g = CZ (1 ⊗ Z)` and `L_g = X`. Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.C,
`Papers/2405.00439/MPU-DW.tex` line 2040: the three-cocycles
`ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with `[b + c] = b + c mod n`
(their cocycle facts are in `TNLean.Algebra.ScalarThreeCocycleCyclicExamples`).

**Formalized here.** The periodic operators of the construction in `GroupCocycleMPO` for
three groups: for `ℤ₂` with the cocycle `ω(g,g,g) = −1`, the operator of the generator
equals `∏ CZ_{i,i+1} Z_i ∏ X_i` as a matrix, and the gate is `W_g = CZ (1 ⊗ Z)`; for `ℤ_n`
with `ω_j`, for every `n` and `j`, the construction satisfies the operator laws of a matrix
product unitary representation, with an explicit kernel; for `ℤ₂ × ℤ₂` with
`ω(a,b,c) = (−1)^{a₁ b₂ c₂}` the same holds. The last cocycle is a standard representative,
not taken from the sources on disk, so the `ℤ₂ × ℤ₂` statements are project results; so are
the unitarity and adjoint laws, which the sources do not state for the periodic operators.

Residues are represented by their values in `{0, …, n − 1}`, the source's convention.
The groups are written multiplicatively as `Multiplicative (ZMod n)`. The kernels of the
periodic operators are derived from the contraction `mpo_tensor_apply`; the sources do not
print them.

## Main definitions

* `MPOTensor.GroupCocycle.czxDecorated`: the operator `∏ CZ_{i,i+1} Z_i ∏ X_i`.

## Main results

* `MPOTensor.GroupCocycle.wGate_cyclicTwo`: `W_g = CZ (1 ⊗ Z)` for the generator of `ℤ₂`.
* `MPOTensor.GroupCocycle.mpo_tensor_cyclicTwo`: `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`.
* `MPOTensor.GroupCocycle.mpo_tensor_cyclic_apply`, `MPOTensor.GroupCocycle.cyclic_operator_laws`:
  the kernel and the operator laws for `ℤ_n` and `ω_j`.
* `MPOTensor.GroupCocycle.mpo_tensor_klein_apply`, `MPOTensor.GroupCocycle.klein_operator_laws`:
  the `ℤ₂ × ℤ₂` instance.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.GroupCocycle

open TNLean.Algebra TNLean.Algebra.ScalarThreeCochain

/-! ### The group `ℤ₂` -/

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

/-- Bridge: the identification of `ℤ₂` with the qubit basis `Fin 2`, arXiv:2203.12563,
line 2070 (`L_g = X`). -/
def bitEquiv : Multiplicative (ZMod 2) ≃ Fin 2 := Multiplicative.toAdd

/-- The gate value of the generator on the bit pair `(k,l)` is the sign of `CZ (1 ⊗ Z)`,
`(−1)^{kl + l}`. -/
private theorem cyclicTwo_site (k l : Fin 2) :
    (cyclicTwoCocycle 1 s₂ (bitEquiv.symm l) ((bitEquiv.symm l)⁻¹ * bitEquiv.symm k) : ℂ) =
      (-1) ^ (k.val * l.val) * (-1) ^ l.val := by
  unfold cyclicTwoCocycle
  fin_cases k <;> fin_cases l <;> split_ifs with h <;>
    first | (exfalso; revert h; decide) | simp

/-- **`W_g = CZ (1 ⊗ Z)`** for the generator of `ℤ₂` and the cocycle `ω(g,g,g) = −1`.

Source: arXiv:2203.12563, line 2070. -/
theorem wGate_cyclicTwo :
    wGate (cyclicTwoCocycle 1) s₂ =
      Matrix.diagonal fun kl : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ↦
        (-1 : ℂ) ^ ((bitEquiv kl.1).val * (bitEquiv kl.2).val) * (-1) ^ (bitEquiv kl.2).val := by
  rw [wGate]
  congr 1
  funext kl
  simpa using cyclicTwo_site (bitEquiv kl.1) (bitEquiv kl.2)

/-- The operator `∏ CZ_{i,i+1} Z_i ∏ X_i` on a periodic chain of `N` qubits: all spins are
flipped by `CZXCompression.spinFlip`, then each controlled-`Z` and each `Z` contributes its
sign on the flipped configuration `s`. Its entry at `(s, t)` is
`(−1)^{∑ s_i s_{i+1} + ∑ s_i}` when `s` is the flip of `t`, and zero otherwise. The operator
`CZXCompression.mpo_czxTensor` of the undecorated CZX tensor has no factors `Z_i` and takes its
sign `(−1)^{∑ t_i t_{i+1}}` on the input configuration; since `s_i = 1 − t_i`,
`∑ s_i s_{i+1} ≡ N + ∑ t_i t_{i+1} (mod 2)`, so dropping the `Z_i` here gives that operator
only up to the sign `(−1)^N`.

Source: arXiv:2203.12563, line 2224. -/
def czxDecorated (N : ℕ) [NeZero N] : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (CZXCompression.spinFlip N) fun t ↦
    (-1 : ℂ) ^ (CZXCompression.czExponent (CZXCompression.spinFlip N t) +
      ∑ i, (CZXCompression.spinFlip N t i).val)

/-- On the flipped pair, the gate sign `(−1)^{kl + l}` of the input bits equals the sign
`(−1)^{(rev k)(rev l) + rev k}` of the flipped bits. -/
private theorem site_rev (k l : Fin 2) :
    (-1 : ℂ) ^ (k.val * l.val) * (-1) ^ l.val =
      (-1) ^ (k.rev.val * l.rev.val) * (-1) ^ k.rev.val := by
  fin_cases k <;> fin_cases l <;> simp [Fin.rev]

/-- **For the nontrivial three-cocycle of `ℤ₂`, `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`** on every
nonempty periodic chain.

Source: arXiv:2203.12563, line 2224. -/
theorem mpo_tensor_cyclicTwo (N : ℕ) [NeZero N] :
    mpo (tensor bitEquiv (cyclicTwoCocycle 1) s₂) N = czxDecorated N := by
  ext s t
  have hshift : shift bitEquiv s₂ N t = CZXCompression.spinFlip N t := by
    funext i
    rw [shift_apply, CZXCompression.spinFlip_apply]
    generalize t i = a
    revert a
    decide
  rw [mpo_tensor_apply, czxDecorated, Matrix.monomial_apply, hshift]
  split_ifs with hs
  · simp only [CZXCompression.czExponent, CZXCompression.spinFlip_apply, cyclicTwo_site,
      site_rev, Finset.prod_mul_distrib, pow_add, Finset.prod_pow_eq_pow_sum]
  · rfl

/-- Bridge: the identification of `ℤ_{m+1}` with `Fin (m+1)` by residues in
`{0, …, m}`, the convention of arXiv:2405.00439, line 2040. -/
def residueEquiv (m : ℕ) : Multiplicative (ZMod (m + 1)) ≃ Fin (m + 1) := Multiplicative.toAdd

/-- **The periodic operator of `ω_j` on `ℤ_{m+1}`**: the entry at `(s, t)` vanishes unless
`s_i = g + t_i` at every site, and then equals `∏_i ζ^{j g ⌊(t_{i+1} + [t_i − t_{i+1}])/n⌋}`
with `n = m + 1` and `ζ = exp(2πi/n)`.

Source: arXiv:2203.12563, lines 2204–2222; arXiv:2405.00439, line 2040. The kernel is
derived from `mpo_tensor_apply`; the sources do not print it. -/
theorem mpo_tensor_cyclic_apply (m j : ℕ) (g : Multiplicative (ZMod (m + 1)))
    {N : ℕ} [NeZero N] (s t : Fin N → Fin (m + 1)) :
    mpo (tensor (residueEquiv m) (cyclicCocycle (m + 1) j) g) N s t =
      if s = fun i ↦ residueEquiv m g + t i then
        ∏ i, rootOfUnity (m + 1) ^ (j * (residueEquiv m g).val *
          (((t (i + 1)).val + (t i - t (i + 1)).val) / (m + 1)))
      else 0 := by
  rw [mpo_tensor_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [cyclicCocycle_val, toAdd_mul, toAdd_inv, neg_add_eq_sub]
  rfl

/-- The four operator laws for `ℤ_n` with the cocycle `ω_j`, for every `n = m + 1` and `j`.

Source: arXiv:2203.12563, lines 2204–2205 (`U_g U_h = U_{gh}`, `U_e = 1`), with `ω_j` from
arXiv:2405.00439, line 2040. Project result: unitarity and `U_g† = U_{g⁻¹}` (see
`MPOTensor.GroupCocycle.family_operator_laws`). -/
theorem cyclic_operator_laws (m j : ℕ) :
    (∀ g, IsMPUPos ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g)) ∧
      (∀ N, 0 < N → mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g) N *
            mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor h) N =
          mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor (g * h)) N) ∧
      (∀ g N, 0 < N → (mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g) N)ᴴ =
          mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g⁻¹) N) :=
  family_operator_laws (residueEquiv m) (cyclicCocycle_isCocycle (m + 1) j)
    (cyclicCocycle_isNormalized (m + 1) j) (cyclicCocycle_norm (m + 1) j)


/-- Project result: the identification of `ℤ₂ × ℤ₂` with `Fin 4`. -/
def kleinEquiv : Multiplicative (ZMod 2 × ZMod 2) ≃ Fin 4 :=
  Multiplicative.toAdd.trans (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)

/-- Project result: **the periodic operator of `(−1)^{a₁ b₂ c₂}`**: writing `x_i ∈ ℤ₂ × ℤ₂` for the
configuration `t`, the entry at `(s, t)` vanishes unless `s` is the shift of `t` by `g`, and
then equals `(−1)^{∑_i g₁ x_{i+1,2} (x_{i,2} − x_{i+1,2})}`. The construction is that of
arXiv:2203.12563, lines 2204–2222; the cocycle is not printed in the sources, and the kernel
is derived from `mpo_tensor_apply`. -/
theorem mpo_tensor_klein_apply (g : Multiplicative (ZMod 2 × ZMod 2)) {N : ℕ} [NeZero N]
    (s t : Fin N → Fin 4) :
    mpo (tensor kleinEquiv kleinCocycle g) N s t =
      if s = shift kleinEquiv g N t then
        ∏ i, (-1 : ℂ) ^ ((Multiplicative.toAdd g).1 *
          (Multiplicative.toAdd (kleinEquiv.symm (t (i + 1)))).2 *
            ((Multiplicative.toAdd (kleinEquiv.symm (t i))).2 -
              (Multiplicative.toAdd (kleinEquiv.symm (t (i + 1)))).2)).val
      else 0 := by
  rw [mpo_tensor_apply]
  congr 1
  simp only [kleinCocycle, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, toAdd_mul,
    toAdd_inv, neg_add_eq_sub, Prod.snd_sub]

/-- Project result: the four operator laws for the `ℤ₂ × ℤ₂` instance. -/
theorem klein_operator_laws :
    (∀ g, IsMPUPos ((family kleinEquiv kleinCocycle).tensor g)) ∧
      (∀ N, 0 < N → mpo ((family kleinEquiv kleinCocycle).tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo ((family kleinEquiv kleinCocycle).tensor g) N *
            mpo ((family kleinEquiv kleinCocycle).tensor h) N =
          mpo ((family kleinEquiv kleinCocycle).tensor (g * h)) N) ∧
      (∀ g N, 0 < N → (mpo ((family kleinEquiv kleinCocycle).tensor g) N)ᴴ =
          mpo ((family kleinEquiv kleinCocycle).tensor g⁻¹) N) :=
  family_operator_laws kleinEquiv kleinCocycle_isCocycle kleinCocycle_isNormalized
    kleinCocycle_norm

end MPOTensor.GroupCocycle
