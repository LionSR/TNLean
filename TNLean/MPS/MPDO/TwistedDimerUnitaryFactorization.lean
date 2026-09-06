/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimerMPDO

/-!
# Explicit unitary factorization of the twisted dimer

This is a project-derived identity for the closed operator family of `T`, not
an assertion from CPSV16. The motivating source is arXiv:1606.00608, lines
995--1010; the precise operator identity and its scope are recorded in
`docs/audits/2026-09-05_twisted_dimer_unitary_factorization.md`.
It does not assert on-site tensor equivalence, virtual gauge equivalence,
a general non-decoration theorem, or a whole-site circuit-depth bound.

A cell consists of the incoming bond `(R_previous, L_current)` and the current
flag. The controlled flag flip is a self-adjoint unitary on the entire cell,
including the orthogonal complement of the two Bell vectors. Its conjugation
fixes `sigma ⊗ I` and sends `sigma ⊗ Z` to `sigma' ⊗ Z`. Taking products over
cells gives the explicit factorization at every positive length. Length zero
is excluded: the empty factor expression is 2, whereas the MPO trace is 8.
-/

open scoped BigOperators Matrix Kronecker

noncomputable section

namespace MPOTensor.TwistedDimer

/-- Two qubits forming one bond, in right-then-left order. -/
abbrev Bond := Fin 2 × Fin 2

/-- One bond and its receiving flag. -/
abbrev Cell := Bond × Fin 2

/-- The normalized Bell projector, with sign label zero for plus and one for minus. -/
def bellProjector (ε : Fin 2) : Matrix Bond Bond ℂ :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then
    (1 / 2 : ℂ) * (tau ε a.2 : ℂ) * (tau ε b.2 : ℂ) else 0

/-- The bond state and its signed counterpart. -/
def bondState (k : Fin 2) : Matrix Bond Bond ℂ :=
  (x : ℂ) • bellProjector 0 + ((tau k 1 * y : ℝ) : ℂ) • bellProjector 1

/-- The state with Bell weights seven eighths and one eighth. -/
def sigma : Matrix Bond Bond ℂ := bondState 0

/-- The signed bond operator with Bell weights seven eighths and minus one eighth. -/
def sigma' : Matrix Bond Bond ℂ := bondState 1

/-- The identity and Pauli Z matrices, indexed by the horizontal block label. -/
def flagMatrix (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun f => (tau k f : ℂ)

/-- The Pauli X matrix flipping the flag. -/
def flagFlip : Matrix (Fin 2) (Fin 2) ℂ := fun f g => if f ≠ g then 1 else 0

/-- Flip the flag precisely in the minus Bell sector; act identically on its complement. -/
def localV : Matrix Cell Cell ℂ :=
  (1 - bellProjector 1) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    bellProjector 1 ⊗ₖ flagFlip

private lemma localV_laws : localVᴴ = localV ∧ localV * localV = 1 := by
  constructor <;> apply Matrix.ext <;> intro a b <;> revert a b <;>
    simp only [Prod.forall, Fin.forall_fin_two] <;>
    norm_num [localV,
      bellProjector, flagFlip, tau, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker_apply,
      Matrix.one_apply, Matrix.diagonal_apply]

/-- The local controlled flag flip is self-adjoint on the whole eight-dimensional cell. -/
theorem localV_conjTranspose : localVᴴ = localV := localV_laws.1

/-- The local controlled flag flip is an involution on the whole cell. -/
theorem localV_mul_self : localV * localV = 1 := localV_laws.2

private lemma localV_intertwine (k : Fin 2) :
    localV * (sigma ⊗ₖ flagMatrix k) = (bondState k ⊗ₖ flagMatrix k) * localV := by
  apply Matrix.ext
  intro a b
  simp only [localV, sigma, bondState, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.add_apply]
  revert a b
  fin_cases k <;> simp only [Prod.forall, Fin.forall_fin_two] <;>
    norm_num [bellProjector, flagFlip, flagMatrix, tau, x, y,
      Matrix.one_apply, Matrix.diagonal_apply]

/-- Both local conjugation identities, with the identity flag at label zero and Z at one. -/
theorem localV_conjugate (k : Fin 2) :
    localV * (sigma ⊗ₖ flagMatrix k) * localVᴴ = bondState k ⊗ₖ flagMatrix k := by
  rw [localV_intertwine, localV_conjTranspose, mul_assoc, localV_mul_self, mul_one]

/-- The Bell mixture has the same two-by-two entries as the displayed tensor,
with zero entries off the matched bond subspace. -/
lemma bondState_apply (k : Fin 2) (a b : Bond) :
    bondState k a b = if a.1 = a.2 ∧ b.1 = b.2 then (Cmat k a.2 b.2 : ℂ) else 0 := by
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  fin_cases k <;> fin_cases r <;> fin_cases l <;> fin_cases r' <;> fin_cases l' <;>
    norm_num [bondState, bellProjector, tau, Cmat, cDiag_eq, cOff_eq, x, y]

/-- Entrywise tensor power, indexed by configurations rather than nested products. -/
def powN {α : Type*} (A : Matrix α α ℂ) (N : ℕ) :
    Matrix (Fin N → α) (Fin N → α) ℂ := fun a b => ∏ m, A (a m) (b m)

private lemma powN_mul {α : Type*} [Fintype α] (A B : Matrix α α ℂ) (N : ℕ) :
    powN (A * B) N = powN A N * powN B N := by
  ext a b
  simp only [powN, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun m c => A (a m) c * B c (b m)

private lemma powN_conjTranspose {α : Type*} (A : Matrix α α ℂ) (N : ℕ) :
    powN Aᴴ N = (powN A N)ᴴ := by
  ext a b
  simp [powN, Matrix.conjTranspose_apply, star_prod]

private lemma powN_one {α : Type*} [DecidableEq α] (N : ℕ) :
    powN (1 : Matrix α α ℂ) N = 1 := by
  ext a b
  simp only [powN, Matrix.one_apply, Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

/-- Regroup sites into incoming bonds and their flags. This equivalence also exists
at length zero; only the operator identity requires positive length. -/
def incomingCellEquiv (N : ℕ) : (Fin N → Fin 8) ≃ (Fin N → Cell) where
  toFun s m := ((bitR (s ((finRotate N).symm m)), bitL (s m)), bitF (s m))
  invFun a m := physIdx (a m).1.2 (a (finRotate N m)).1.1 (a m).2
  left_inv s := by
    funext m
    simp only [Equiv.symm_apply_apply]
    exact physIdx_bits (s m)
  right_inv a := by
    funext m
    simp only [bitR_physIdx, bitL_physIdx, bitF_physIdx, Equiv.apply_symm_apply]

/-- Separate the bond configuration and the flag configuration of the incoming cells. -/
def bondFlagEquiv (N : ℕ) : (Fin N → Cell) ≃ (Fin N → Bond) × (Fin N → Fin 2) :=
  Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Bond) (fun _ ↦ Fin 2)

private lemma powN_kronecker (A : Matrix Bond Bond ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    powN (A ⊗ₖ B) N = (powN A N ⊗ₖ powN B N).submatrix
      (bondFlagEquiv N) (bondFlagEquiv N) := by
  ext a b
  exact Finset.prod_mul_distrib

/-- The even-parity flag state, with normalization two to the minus N. -/
def evenFlagState (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (1 / 2 : ℂ) ^ N • (powN (flagMatrix 0) N + powN (flagMatrix 1) N)

/-- Independent bond states and the even-parity flag state, in the original site coordinates. -/
def decoratedState (N : ℕ) : Matrix (Fin N → Fin 8) (Fin N → Fin 8) ℂ :=
  (powN sigma N ⊗ₖ evenFlagState N).submatrix
    ((incomingCellEquiv N).trans (bondFlagEquiv N))
    ((incomingCellEquiv N).trans (bondFlagEquiv N))

/-- The explicit product of controlled flag flips, in the original site coordinates. -/
def chainUnitary (N : ℕ) : Matrix (Fin N → Fin 8) (Fin N → Fin 8) ℂ :=
  (powN localV N).submatrix (incomingCellEquiv N) (incomingCellEquiv N)

/-- Matrix entries of the unitary are products of the specified local gate entries. -/
lemma chainUnitary_apply (N : ℕ) (s t : Fin N → Fin 8) :
    chainUnitary N s t = ∏ m,
      localV ((bitR (s ((finRotate N).symm m)), bitL (s m)), bitF (s m))
        ((bitR (t ((finRotate N).symm m)), bitL (t m)), bitF (t m)) := rfl

/-- The product gate is self-adjoint. -/
theorem chainUnitary_conjTranspose (N : ℕ) : (chainUnitary N)ᴴ = chainUnitary N := by
  simp only [chainUnitary, Matrix.conjTranspose_submatrix, ← powN_conjTranspose,
    localV_conjTranspose]

/-- The first whole-space unitary law. -/
theorem chainUnitary_mul_conjTranspose (N : ℕ) :
    chainUnitary N * (chainUnitary N)ᴴ = 1 := by
  rw [chainUnitary_conjTranspose]
  simp only [chainUnitary, Matrix.submatrix_mul_equiv, ← powN_mul, localV_mul_self,
    powN_one, Matrix.submatrix_one_equiv]

/-- The second whole-space unitary law. -/
theorem chainUnitary_conjTranspose_mul (N : ℕ) :
    (chainUnitary N)ᴴ * chainUnitary N = 1 := by
  simpa only [chainUnitary_conjTranspose] using chainUnitary_mul_conjTranspose N

private lemma incoming_matched_iff (N : ℕ) (s : Fin N → Fin 8) :
    (∀ m, bitR (s ((finRotate N).symm m)) = bitL (s m)) ↔
      IsCyclicBondMatched N s := by
  constructor
  · intro h m
    simpa only [Equiv.symm_apply_apply, IsBondMatchedPair] using h (finRotate N m)
  · intro h m
    simpa only [IsBondMatchedPair, Equiv.apply_symm_apply] using h ((finRotate N).symm m)

private lemma local_entry (k : Fin 2) (r r' : Fin 2) (i j : Fin 8) :
    (1 / 2 : ℂ) * (bondState k ⊗ₖ flagMatrix k)
      ((r, bitL i), bitF i) ((r', bitL j), bitF j) =
      if r = bitL i ∧ r' = bitL j then coef k i j else 0 := by
  simp only [Matrix.kronecker_apply, bondState_apply, flagMatrix, Matrix.diagonal_apply]
  by_cases hb : r = bitL i ∧ r' = bitL j
  · simp only [ite_eq_left hb]
    by_cases hf : bitF i = bitF j
    · simp only [hf, ite_true, coef]
      push_cast
      ring
    · simp [coef, hf]
  · simp [hb]

private lemma scaled_powN_entry (k : Fin 2) (N : ℕ) (s t : Fin N → Fin 8) :
    (1 / 2 : ℂ) ^ N * powN (bondState k ⊗ₖ flagMatrix k) N
        (incomingCellEquiv N s) (incomingCellEquiv N t) =
      chainIndicator N s t * ∏ m, coef k (s m) (t m) := by
  calc
    _ = ∏ m, (1 / 2 : ℂ) * (bondState k ⊗ₖ flagMatrix k)
        ((bitR (s ((finRotate N).symm m)), bitL (s m)), bitF (s m))
        ((bitR (t ((finRotate N).symm m)), bitL (t m)), bitF (t m)) := by
      simp [powN, incomingCellEquiv, Finset.prod_mul_distrib]
    _ = _ := by
      simp only [local_entry, Fintype.prod_ite_zero, forall_and,
        incoming_matched_iff, chainIndicator, Matrix.of_apply]
      split_ifs <;> simp

private lemma decoratedState_eq (N : ℕ) :
    decoratedState N =
      ((1 / 2 : ℂ) ^ N •
        (powN (sigma ⊗ₖ flagMatrix 0) N + powN (sigma ⊗ₖ flagMatrix 1) N)).submatrix
          (incomingCellEquiv N) (incomingCellEquiv N) := by
  rw [powN_kronecker, powN_kronecker]
  ext s t
  simp only [decoratedState, evenFlagState, Matrix.submatrix_apply, Matrix.kronecker_apply,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, powN, Equiv.trans_apply,
    bondFlagEquiv, Equiv.arrowProdEquivProdArrow_apply]
  ring

private lemma conjugate_decoratedState (N : ℕ) :
    chainUnitary N * decoratedState N * (chainUnitary N)ᴴ =
      ((1 / 2 : ℂ) ^ N •
        (powN (bondState 0 ⊗ₖ flagMatrix 0) N +
          powN (bondState 1 ⊗ₖ flagMatrix 1) N)).submatrix
            (incomingCellEquiv N) (incomingCellEquiv N) := by
  rw [decoratedState_eq]
  simp only [chainUnitary, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← powN_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    mul_add, add_mul, ← powN_mul, localV_conjugate]

/-- The closed twisted-dimer operator is the explicit unitary conjugate of
independent bond states and the even-parity flag state, for every positive
length, including length one. This is an operator identity, not a strict
on-site or virtual-gauge equivalence of tensors. See
`docs/audits/2026-09-05_twisted_dimer_unitary_factorization.md`. -/
theorem mpo_eq_unitary_factorization {N : ℕ} (hN : 0 < N) :
    mpo T N = chainUnitary N * decoratedState N * (chainUnitary N)ᴴ := by
  rw [conjugate_decoratedState]
  ext s t
  rw [mpo_T_entry_formula hN, Fin.sum_univ_two]
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    mul_add, scaled_powN_entry]

end MPOTensor.TwistedDimer
