/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPU.GroupCocycleMPO.Instances

/-!
# The `ℤ₂` group-cocycle operator as a symmetry of spin-chain Hamiltonians

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection
"MPO algebras representing `ℤ₂`", `Papers/2203.12563/REsubmission.tex` line 1843: for the
nontrivial three-cocycle of `ℤ₂`, the Hamiltonian `H = ∑_i CZ_{i,i+2} X_{i+1} − μ Z_i Z_{i+1}`
of Roose et al. "is invariant under `U = ∏ CZ_{i,i+1} Z_i ∏ X_i`"; line 2224 identifies `U` with
the periodic operator of the group-cocycle construction.
Review: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 1393: the local
Hamiltonian commuting with the MPO of the nontrivial three-cocycle of `ℤ₂` "is precisely the
cluster state Hamiltonian with critical magnetic field"; line 1472 writes this MPO, the virtual
symmetry of the CZX state, as `O_Z = ∏ CZ_{i,i+1} ∏ X_i`, without the factors `Z_i`.

**Formalized here.** On a periodic chain of `N ≥ 2` qubits:

* `U = ∏ CZ_{i,i+1} Z_i ∏ X_i` (`MPOTensor.GroupCocycle.czxDecorated`, the periodic operator of
  the construction by `MPOTensor.GroupCocycle.mpo_tensor_cyclicTwo`) commutes with the
  Hamiltonian of line 1843 for every `μ`.
* For the cluster–Ising Hamiltonian `H(λ) = −∑_j Z_{j−1} X_j Z_{j+1} − λ ∑_j X_j`, the review's
  operator `O_Z = ∏ CZ_{i,i+1} ∏ X_i` (the periodic operator `CZXCompression.mpo_czxTensor` of
  the undecorated CZX tensor) exchanges the two terms, `O_Z X_j O_Z† = Z_{j−1} X_j Z_{j+1}`, so
  `O_Z H(λ) O_Z† = λ H(λ⁻¹)` and `O_Z` commutes with the critical Hamiltonian `H(1)`.
* The decorated operator `U` exchanges them with a sign, `U X_j U† = −Z_{j−1} X_j Z_{j+1}`, so
  `U H(λ) U† = −λ H(λ⁻¹)`: `U` commutes with `H(−1)` and sends `H(1)` to `−H(1)`. The factors
  `Z_i` of `U` flip the sign of the transverse field at the symmetric point.

All operators are monomial matrices on the configurations `Fin N → Fin 2`, and every identity
reduces to one parity computation: flipping bit `j` changes `∑_i s_i s_{i+1}` by
`s_{j−1} + s_{j+1}` and `∑_i s_i` by one, modulo two
(`MPOTensor.GroupCocycle.czxDecorated_phase_flipAt`).

## Main definitions

* `MPOTensor.GroupCocycle.flipAt`: the flip of one bit of a configuration.
* `MPOTensor.GroupCocycle.pauliXAt`, `MPOTensor.GroupCocycle.clusterTerm`: the operators `X_j`
  and `Z_{j−1} X_j Z_{j+1}`.
* `MPOTensor.GroupCocycle.czXTerm`, `MPOTensor.GroupCocycle.zzTerm`: the operators
  `CZ_{i,i+2} X_{i+1}` and `Z_i Z_{i+1}`.
* `MPOTensor.GroupCocycle.clusterIsingHamiltonian`,
  `MPOTensor.GroupCocycle.rooseHamiltonian`: the two Hamiltonians.

## Main results

* `MPOTensor.GroupCocycle.czxDecorated_mul_pauliXAt`,
  `MPOTensor.GroupCocycle.czxDecorated_mul_clusterTerm`: the local conjugation relations.
* `MPOTensor.GroupCocycle.czxDecorated_mul_rooseHamiltonian`: `U` commutes with the Hamiltonian
  of arXiv:2203.12563, line 1843.
* `MPOTensor.GroupCocycle.mpo_czxTensor_conj_clusterIsingHamiltonian_one`: the review's CZX
  operator commutes with the critical cluster–Ising Hamiltonian `H(1)`.
* `MPOTensor.GroupCocycle.czxDecorated_conj_clusterIsingHamiltonian`: `U H(λ) U†` exchanges the
  two terms; `czxDecorated_conj_clusterIsingHamiltonian_neg_one` and
  `czxDecorated_conj_clusterIsingHamiltonian_one` are the points `λ = −1` and `λ = 1`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts, symmetries,
  theorems*
-/

open scoped BigOperators Matrix

namespace MPOTensor.GroupCocycle

open CZXCompression

variable {N : ℕ} [NeZero N]

/-! ### Single-site operators -/

/-- The flip of bit `j` of a configuration of `N` qubits. -/
def flipAt (j : Fin N) : Equiv.Perm (Fin N → Fin 2) :=
  Function.Involutive.toPerm (fun t ↦ Function.update t j (t j).rev) fun t ↦ by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update_of_ne h]

omit [NeZero N] in
theorem flipAt_apply (j : Fin N) (t : Fin N → Fin 2) (i : Fin N) :
    flipAt j t i = if i = j then (t i).rev else t i := by
  change Function.update t j (t j).rev i = _
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

omit [NeZero N] in
/-- Flipping one bit commutes with flipping all bits. -/
theorem spinFlip_mul_flipAt (j : Fin N) : spinFlip N * flipAt j = flipAt j * spinFlip N := by
  ext t i
  simp only [Equiv.Perm.mul_apply, spinFlip_apply, flipAt_apply]
  split_ifs <;> rfl

/-- The Pauli operator `X_j` on a periodic chain of `N` qubits. -/
noncomputable def pauliXAt (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (flipAt j) fun _ ↦ 1

/-- The three-site operator `Z_{j−1} X_j Z_{j+1}` of the cluster Hamiltonian: flip bit `j` and
multiply by the signs of the two neighbours. -/
noncomputable def clusterTerm (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (flipAt j) fun t ↦ (-1 : ℂ) ^ ((t (j - 1)).val + (t (j + 1)).val)

/-- The operator `CZ_{i,i+2} X_{i+1}` of arXiv:2203.12563, line 1843: flip bit `i + 1` and
multiply by the controlled-`Z` sign `(−1)^{t_i t_{i+2}}` of the two neighbours. -/
noncomputable def czXTerm (i : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (flipAt (i + 1)) fun t ↦ (-1 : ℂ) ^ ((t i).val * (t (i + 2)).val)

/-- The operator `Z_i Z_{i+1}`. -/
noncomputable def zzTerm (i : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial 1 fun t ↦ (-1 : ℂ) ^ ((t i).val + (t (i + 1)).val)

/-- The cluster–Ising Hamiltonian `H(λ) = −∑_j Z_{j−1} X_j Z_{j+1} − λ ∑_j X_j` on a periodic
chain of `N` qubits. -/
noncomputable def clusterIsingHamiltonian (N : ℕ) [NeZero N] (c : ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  -(∑ j, clusterTerm j) - c • ∑ j, pauliXAt j

/-- Source: arXiv:2203.12563, line 1843: the Hamiltonian
`H = ∑_i CZ_{i,i+2} X_{i+1} − μ Z_i Z_{i+1}` of Roose et al. on a periodic chain of `N`
qubits. -/
noncomputable def rooseHamiltonian (N : ℕ) [NeZero N] (μ : ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ∑ i, czXTerm i - μ • ∑ i, zzTerm i

/-! ### The parity computation -/

private theorem one_ne_zero_of_two_le (hN : 2 ≤ N) : (1 : Fin N) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h'
  exact one_ne_zero h'

private theorem sub_one_ne_self (hN : 2 ≤ N) (j : Fin N) : j - 1 ≠ j := fun h ↦
  one_ne_zero_of_two_le hN (sub_eq_self.mp h)

private theorem add_one_ne_self (hN : 2 ≤ N) (j : Fin N) : j + 1 ≠ j := fun h ↦
  one_ne_zero_of_two_le hN (add_eq_left.mp h)

/-- Flipping bit `j` multiplies the controlled-`Z` sign by the signs of the two neighbours. -/
private theorem neg_one_pow_czExponent_flipAt (hN : 2 ≤ N) (j : Fin N) (u : Fin N → Fin 2) :
    (-1 : ℂ) ^ czExponent (flipAt j u) =
      (-1 : ℂ) ^ czExponent u * ((-1) ^ (u (j - 1)).val * (-1) ^ (u (j + 1)).val) := by
  let r : Fin N → ℂ := fun n ↦
    if n = j - 1 then (-1) ^ (u (j - 1)).val else if n = j then (-1) ^ (u (j + 1)).val else 1
  have hr : ∏ n, r n = (-1) ^ (u (j - 1)).val * (-1) ^ (u (j + 1)).val := by
    rw [Finset.prod_eq_mul (j - 1) j (sub_one_ne_self hN j)]
    · simp [r, (sub_one_ne_self hN j).symm]
    · intro n _ hn
      simp [r, hn.1, hn.2]
    · simp
    · simp
  have hsite : ∀ n, (-1 : ℂ) ^ ((flipAt j u n).val * (flipAt j u (n + 1)).val) =
      (-1) ^ ((u n).val * (u (n + 1)).val) * r n := by
    intro n
    by_cases h1 : n = j - 1
    · subst h1
      have hne : j - 1 ≠ j := sub_one_ne_self hN j
      simp only [flipAt_apply, hne, sub_add_cancel, ite_true, ite_false, r]
      generalize u (j - 1) = a
      generalize u j = b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · by_cases h2 : n = j
      · subst h2
        simp only [flipAt_apply, add_one_ne_self hN n, ite_true, ite_false, h1, r]
        generalize u n = a
        generalize u (n + 1) = b
        fin_cases a <;> fin_cases b <;> simp [Fin.rev]
      · have h3 : n + 1 ≠ j := fun h ↦ h1 (by rw [← h, add_sub_cancel_right])
        simp [flipAt_apply, h1, h2, h3, r]
  rw [← hr, czExponent, czExponent, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun n _ ↦ hsite n

omit [NeZero N] in
/-- Flipping bit `j` changes the parity of the number of ones. -/
private theorem neg_one_pow_sum_flipAt (j : Fin N) (u : Fin N → Fin 2) :
    (-1 : ℂ) ^ ∑ i, (flipAt j u i).val = -(-1 : ℂ) ^ ∑ i, (u i).val := by
  have hsite : ∀ i, (-1 : ℂ) ^ (flipAt j u i).val =
      (if i = j then -1 else 1) * (-1) ^ (u i).val := by
    intro i
    by_cases h : i = j
    · simp only [flipAt_apply, h, ite_true]
      generalize u j = a
      fin_cases a <;> simp [Fin.rev]
    · simp [flipAt_apply, h]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_congr rfl fun i _ ↦ hsite i, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    ite_eq_left (Finset.mem_univ _), neg_one_mul]

/-- The phase of `U = ∏ CZ_{i,i+1} Z_i ∏ X_i` at the input `t`. -/
private theorem czxDecorated_eq :
    czxDecorated N = Matrix.monomial (spinFlip N) fun t ↦
      (-1 : ℂ) ^ (czExponent (spinFlip N t) + ∑ i, (spinFlip N t i).val) := rfl

/-- **The phase of `U` under a bit flip.** Flipping bit `j` of the input changes the phase of
`U = ∏ CZ_{i,i+1} Z_i ∏ X_i` by `−(−1)^{t_{j−1} + t_{j+1}}`. -/
theorem czxDecorated_phase_flipAt (hN : 2 ≤ N) (j : Fin N) (t : Fin N → Fin 2) :
    (-1 : ℂ) ^ (czExponent (spinFlip N (flipAt j t)) + ∑ i, (spinFlip N (flipAt j t) i).val) =
      -((-1) ^ ((t (j - 1)).val + (t (j + 1)).val) *
        (-1 : ℂ) ^ (czExponent (spinFlip N t) + ∑ i, (spinFlip N t i).val)) := by
  have hflip : spinFlip N (flipAt j t) = flipAt j (spinFlip N t) := by
    rw [← Equiv.Perm.mul_apply, spinFlip_mul_flipAt, Equiv.Perm.mul_apply]
  have hrev : ∀ a b : Fin 2, (-1 : ℂ) ^ a.rev.val * (-1) ^ b.rev.val =
      (-1) ^ (a.val + b.val) := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.rev]
  rw [hflip, pow_add, pow_add, neg_one_pow_czExponent_flipAt hN, neg_one_pow_sum_flipAt,
    spinFlip_apply, spinFlip_apply, hrev]
  ring

/-! ### The local conjugation relations -/

/-- **`U X_j = −Z_{j−1} X_j Z_{j+1} U`.** Project result. -/
theorem czxDecorated_mul_pauliXAt (hN : 2 ≤ N) (j : Fin N) :
    czxDecorated N * pauliXAt j = -(clusterTerm j * czxDecorated N) := by
  rw [czxDecorated_eq, pauliXAt, clusterTerm, Matrix.monomial_mul_monomial,
    Matrix.monomial_mul_monomial, spinFlip_mul_flipAt, Matrix.neg_monomial]
  congr 1
  funext s
  rw [Pi.neg_apply]
  rw [czxDecorated_phase_flipAt hN, mul_one]
  have hrev : ∀ a b : Fin 2, (-1 : ℂ) ^ (a.rev.val + b.rev.val) = (-1) ^ (a.val + b.val) := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.rev]
  rw [spinFlip_apply, spinFlip_apply, hrev]

/-- **`U Z_{j−1} X_j Z_{j+1} = −X_j U`.** Project result. -/
theorem czxDecorated_mul_clusterTerm (hN : 2 ≤ N) (j : Fin N) :
    czxDecorated N * clusterTerm j = -(pauliXAt j * czxDecorated N) := by
  rw [czxDecorated_eq, pauliXAt, clusterTerm, Matrix.monomial_mul_monomial,
    Matrix.monomial_mul_monomial, spinFlip_mul_flipAt, Matrix.neg_monomial]
  congr 1
  funext s
  rw [Pi.neg_apply]
  rw [czxDecorated_phase_flipAt hN, one_mul]
  have hsq : ∀ k : ℕ, (-1 : ℂ) ^ k * (-1) ^ k = 1 := fun k ↦ by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  linear_combination (-(-1 : ℂ) ^ (czExponent (spinFlip N s) + ∑ i, (spinFlip N s i).val)) *
    hsq ((s (j - 1)).val + (s (j + 1)).val)

/-- `U` commutes with `CZ_{i,i+2} X_{i+1}`. -/
theorem czxDecorated_mul_czXTerm (hN : 2 ≤ N) (i : Fin N) :
    czxDecorated N * czXTerm i = czXTerm i * czxDecorated N := by
  rw [czxDecorated_eq, czXTerm, Matrix.monomial_mul_monomial, Matrix.monomial_mul_monomial,
    spinFlip_mul_flipAt]
  congr 1
  funext s
  have h2 : i + 1 + 1 = i + 2 := by
    rw [add_assoc]; congr 1; ext; simp [Fin.val_add]
  rw [czxDecorated_phase_flipAt hN, add_sub_cancel_right, h2, spinFlip_apply, spinFlip_apply]
  have hbit : ∀ a b : Fin 2, -(-1 : ℂ) ^ (a.val + b.val) * (-1) ^ (a.val * b.val) =
      (-1) ^ (a.rev.val * b.rev.val) := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.rev]
  rw [← hbit]
  ring

/-- `U` commutes with `Z_i Z_{i+1}`. -/
theorem czxDecorated_mul_zzTerm (i : Fin N) :
    czxDecorated N * zzTerm i = zzTerm i * czxDecorated N := by
  rw [czxDecorated_eq, zzTerm, Matrix.monomial_mul_monomial, Matrix.monomial_mul_monomial,
    mul_one, one_mul]
  congr 1
  funext s
  have hbit : ∀ a b : Fin 2, (-1 : ℂ) ^ (a.rev.val + b.rev.val) = (-1) ^ (a.val + b.val) := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.rev]
  rw [Equiv.Perm.one_apply, spinFlip_apply, spinFlip_apply, hbit, mul_comm]

/-! ### The two Hamiltonians -/

/-- **The group-cocycle operator is a symmetry of the Hamiltonian of Roose et al.** Source:
arXiv:2203.12563, line 1843: `H = ∑_i CZ_{i,i+2} X_{i+1} − μ Z_i Z_{i+1}` "is invariant
under `U = ∏ CZ_{i,i+1} Z_i ∏ X_i`", here on every periodic chain of `N ≥ 2` qubits and for
every `μ`. -/
theorem czxDecorated_mul_rooseHamiltonian (hN : 2 ≤ N) (μ : ℂ) :
    czxDecorated N * rooseHamiltonian N μ = rooseHamiltonian N μ * czxDecorated N := by
  simp only [rooseHamiltonian, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.mul_sum, Finset.sum_mul, czxDecorated_mul_czXTerm hN, czxDecorated_mul_zzTerm]

/-- **Conjugation by `U` exchanges the two terms of the cluster–Ising Hamiltonian.** Project
result: `U H(λ) = (λ ∑_j Z_{j−1} X_j Z_{j+1} +
∑_j X_j) U` on every periodic chain of `N ≥ 2` qubits. -/
theorem czxDecorated_mul_clusterIsingHamiltonian (hN : 2 ≤ N) (c : ℂ) :
    czxDecorated N * clusterIsingHamiltonian N c =
      (c • ∑ j, clusterTerm j + ∑ j, pauliXAt j) * czxDecorated N := by
  simp only [clusterIsingHamiltonian, Matrix.mul_sub, Matrix.mul_neg, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    czxDecorated_mul_pauliXAt hN, czxDecorated_mul_clusterTerm hN, Finset.sum_neg_distrib,
    smul_neg, neg_neg, sub_neg_eq_add]
  abel

/-- `U` is unitary: `U U† = 1`. -/
private theorem czxDecorated_mul_conjTranspose :
    czxDecorated N * (czxDecorated N)ᴴ = 1 := by
  have h := Matrix.monomial_mem_unitaryGroup (spinFlip N) (fun t ↦
      (-1 : ℂ) ^ (czExponent (spinFlip N t) + ∑ i, (spinFlip N t i).val)) fun s ↦ by
    simp [star_pow, ← mul_pow]
  rw [← czxDecorated_eq, Matrix.mem_unitaryGroup_iff] at h
  exact h

/-- **`U H(λ) U† = λ ∑_j Z_{j−1} X_j Z_{j+1} + ∑_j X_j`.** Project result: the conjugated form
of `czxDecorated_mul_clusterIsingHamiltonian`. For `λ ≠ 0` the right side is `−λ H(λ⁻¹)`
(`czxDecorated_conj_clusterIsingHamiltonian_eq_smul`). -/
theorem czxDecorated_conj_clusterIsingHamiltonian (hN : 2 ≤ N) (c : ℂ) :
    czxDecorated N * clusterIsingHamiltonian N c * (czxDecorated N)ᴴ =
      c • ∑ j, clusterTerm j + ∑ j, pauliXAt j := by
  rw [czxDecorated_mul_clusterIsingHamiltonian hN, Matrix.mul_assoc,
    czxDecorated_mul_conjTranspose, Matrix.mul_one]

/-- **The exchange of couplings.** Project result: for `λ ≠ 0`, `U H(λ) U† = −λ H(λ⁻¹)`. -/
theorem czxDecorated_conj_clusterIsingHamiltonian_eq_smul (hN : 2 ≤ N) {c : ℂ} (hc : c ≠ 0) :
    czxDecorated N * clusterIsingHamiltonian N c * (czxDecorated N)ᴴ =
      -c • clusterIsingHamiltonian N c⁻¹ := by
  rw [czxDecorated_conj_clusterIsingHamiltonian hN, clusterIsingHamiltonian, smul_sub, smul_neg,
    smul_smul, neg_mul, mul_inv_cancel₀ hc, neg_smul, neg_smul, one_smul, sub_neg_eq_add,
    neg_neg]

/-- **The decorated operator fixes `H(−1)`.** Project result: `U` commutes with
`H(−1) = −∑_j Z_{j−1} X_j Z_{j+1} + ∑_j X_j` on every periodic chain of `N ≥ 2` qubits. -/
theorem czxDecorated_conj_clusterIsingHamiltonian_neg_one (hN : 2 ≤ N) :
    czxDecorated N * clusterIsingHamiltonian N (-1) * (czxDecorated N)ᴴ =
      clusterIsingHamiltonian N (-1) := by
  rw [czxDecorated_conj_clusterIsingHamiltonian hN, clusterIsingHamiltonian, neg_smul, one_smul,
    neg_smul, one_smul, sub_neg_eq_add]

/-- **The self-dual point is mapped to its negative.** Project result: `U H(1) U† = −H(1)`, so
in the sign convention `H(λ) = −∑_j Z_{j−1} X_j Z_{j+1} − λ ∑_j X_j` the operator `U` does not
fix `H(1)`. -/
theorem czxDecorated_conj_clusterIsingHamiltonian_one (hN : 2 ≤ N) :
    czxDecorated N * clusterIsingHamiltonian N 1 * (czxDecorated N)ᴴ =
      -clusterIsingHamiltonian N 1 := by
  rw [czxDecorated_conj_clusterIsingHamiltonian hN, clusterIsingHamiltonian, one_smul, one_smul,
    neg_sub, sub_neg_eq_add, add_comm]

/-! ### The undecorated CZX operator of the review -/

private theorem neg_one_pow_rev_add (a b : Fin 2) :
    (-1 : ℂ) ^ (a.rev.val + b.rev.val) = (-1) ^ a.val * (-1) ^ b.val := by
  fin_cases a <;> fin_cases b <;> simp [Fin.rev]

/-- **`O_Z X_j = Z_{j−1} X_j Z_{j+1} O_Z`** for the CZX operator `O_Z = ∏ CZ_{i,i+1} ∏ X_i` of
arXiv:2011.12127, line 1472. Project result. -/
theorem mpo_czxTensor_mul_pauliXAt (hN : 2 ≤ N) (j : Fin N) :
    MPOTensor.mpo czxTensor N * pauliXAt j = clusterTerm j * MPOTensor.mpo czxTensor N := by
  rw [mpo_czxTensor, pauliXAt, clusterTerm, Matrix.monomial_mul_monomial,
    Matrix.monomial_mul_monomial, spinFlip_mul_flipAt]
  congr 1
  funext s
  rw [neg_one_pow_czExponent_flipAt hN, mul_one, spinFlip_apply, spinFlip_apply,
    neg_one_pow_rev_add]
  ring

/-- **`O_Z Z_{j−1} X_j Z_{j+1} = X_j O_Z`.** Project result. -/
theorem mpo_czxTensor_mul_clusterTerm (hN : 2 ≤ N) (j : Fin N) :
    MPOTensor.mpo czxTensor N * clusterTerm j = pauliXAt j * MPOTensor.mpo czxTensor N := by
  rw [mpo_czxTensor, pauliXAt, clusterTerm, Matrix.monomial_mul_monomial,
    Matrix.monomial_mul_monomial, spinFlip_mul_flipAt]
  congr 1
  funext s
  rw [neg_one_pow_czExponent_flipAt hN, one_mul, pow_add]
  have hsq : ∀ k : ℕ, (-1 : ℂ) ^ k * (-1) ^ k = 1 := fun k ↦ by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  linear_combination (-1 : ℂ) ^ czExponent s * ((-1) ^ (s (j + 1)).val * (-1) ^ (s (j + 1)).val *
    hsq (s (j - 1)).val + hsq (s (j + 1)).val)

/-- **The review's CZX operator exchanges the two terms.** Project result:
`O_Z H(λ) O_Z† = −∑_j X_j − λ ∑_j Z_{j−1} X_j Z_{j+1}` on every periodic chain of `N ≥ 2`
qubits, which is `λ H(λ⁻¹)` for `λ ≠ 0`. -/
theorem mpo_czxTensor_conj_clusterIsingHamiltonian (hN : 2 ≤ N) (c : ℂ) :
    MPOTensor.mpo czxTensor N * clusterIsingHamiltonian N c * (MPOTensor.mpo czxTensor N)ᴴ =
      -(∑ j, pauliXAt j) - c • ∑ j, clusterTerm j := by
  have hU := Matrix.mem_unitaryGroup_iff.mp (mpo_czxTensor_mem_unitaryGroup (N := N))
  have hmul : MPOTensor.mpo czxTensor N * clusterIsingHamiltonian N c =
      (-(∑ j, pauliXAt j) - c • ∑ j, clusterTerm j) * MPOTensor.mpo czxTensor N := by
    simp only [clusterIsingHamiltonian, Matrix.mul_sub, Matrix.mul_neg, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
      mpo_czxTensor_mul_pauliXAt hN, mpo_czxTensor_mul_clusterTerm hN]
  rw [hmul, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hU, Matrix.mul_one]

/-- **The CZX symmetry of the critical cluster Hamiltonian.** Source: arXiv:2011.12127,
line 1393, with the operator `O_Z = ∏ CZ_{i,i+1} ∏ X_i` of line 1472: `O_Z` commutes with the
cluster Hamiltonian in the critical field, here `H(1) = −∑_j Z_{j−1} X_j Z_{j+1} − ∑_j X_j`, on
every periodic chain of `N ≥ 2` qubits. The review prints no formula for the Hamiltonian; the
sign convention of `H(λ)` is the one of the cluster–Ising model. -/
theorem mpo_czxTensor_conj_clusterIsingHamiltonian_one (hN : 2 ≤ N) :
    MPOTensor.mpo czxTensor N * clusterIsingHamiltonian N 1 * (MPOTensor.mpo czxTensor N)ᴴ =
      clusterIsingHamiltonian N 1 := by
  rw [mpo_czxTensor_conj_clusterIsingHamiltonian hN, clusterIsingHamiltonian, one_smul, one_smul,
    sub_eq_add_neg, sub_eq_add_neg, add_comm]

end MPOTensor.GroupCocycle
