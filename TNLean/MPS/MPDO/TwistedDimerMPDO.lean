/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinCyclicInduction
import TNLean.MPS.MPDO.TwistedDimer
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of the $\mathbb Z_2$-twisted quantum dimer

**Scope: the closed operator family.**  This file proves that the
$\mathbb Z_2$-twisted quantum dimer `T` of `TNLean.MPS.MPDO.TwistedDimer` is a
matrix product density operator: the operator it generates on a ring of `N`
sites is positive semidefinite for every positive `N`.  The tensor is a project
example motivated by the length-dependence question after Theorem 4.14 of
arXiv:1606.00608 (lines 995--1010); it is not a tensor stated in that source.

## Main results

* `mpo_T_entry_formula` — the closed-chain entry formula: the matrix element of
  the closed operator at a pair of physical strings is the cyclic bond-matching
  indicator times the sum over the two horizontal block labels of the product
  of the one-site coefficients;
* `mpo_T_eq_smul_hadamard` — the resulting Schur-product factorization of the
  closed operator;
* `T_isMPDO` — the closed operator is positive semidefinite on every ring of
  positive length.

## The argument

Every letter of the tensor is a sum of two matrix units carrying the block
labels $k = 0, 1$.  A product of letters therefore keeps one common block label
and vanishes unless consecutive letters match on their bond bits; closing the
trace adds the wraparound match, so the closed operator entry is the cyclic
bond-matching indicator times $\sum_k\prod_n\text{coefficient}$.

The one-site coefficient is half of $C_k[l,l']\,(\tau_k)_{ff}\,\delta_{ff'}$,
which is the entry of the four-by-four matrix `gLoc k` at the pairs
(flag bit, left bit) read off the two physical indices.  So the coefficient
product over the ring is $2^{-N}$ times an entry of the $N$-fold Kronecker
power `gPow k N`, and the closed operator is $2^{-N}$ times the Hadamard
product of the rank-one bond-matching indicator with the pullback of
`gPow 0 N + gPow 1 N`.  The Schur product theorem reduces positivity to
positive semidefiniteness of that sum of Kronecker powers.

The sum of the two Kronecker powers is not a Kronecker power itself, so it is
handled together with the difference: peeling the last site off the ring gives
$$
  g_0^{\otimes(N+1)} \pm g_1^{\otimes(N+1)}
    = \tfrac12\Bigl[(g_0^{\otimes N} + g_1^{\otimes N})\otimes(g_0 \pm g_1)
      + (g_0^{\otimes N} - g_1^{\otimes N})\otimes(g_0 \mp g_1)\Bigr],
$$
and both local combinations $g_0 \pm g_1$ are positive semidefinite: each is
block diagonal in the flag bit, with the rank-one blocks
$\tfrac74\,\lvert{+}\rangle\langle{+}\rvert$ and
$\tfrac14\,\lvert{-}\rangle\langle{-}\rvert$ in the two flag sectors, the
sectors being exchanged between the sum and the difference.  The induction
therefore proves the two statements simultaneously.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4, equation `eq:III_MPDOform`, lines 623--630 (matrix product density
  operators) and lines 995--1010 (the length-dependence question motivating this
  project example)
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### The bond-matching conditions -/

/-- The **open bond-matching condition** on a physical string of positive
length: the right bit of each letter is the left bit of the next one along the
segment.  A product of letters of the twisted dimer vanishes unless its ket and
bra strings both satisfy it (`evalWord_T_ofFn`).

Project example; not from CPSV16. -/
def OpenOK {n : ℕ} (σ : Fin (n + 1) → Fin 8) : Prop :=
  ∀ i : Fin n, gate (σ i.castSucc) (σ i.succ)

/-- The open bond-matching condition is a finite conjunction of equalities of
bits, hence decidable. -/
instance decidableOpenOK {n : ℕ} (σ : Fin (n + 1) → Fin 8) : Decidable (OpenOK σ) :=
  inferInstanceAs (Decidable (∀ i : Fin n, gate (σ i.castSucc) (σ i.succ)))

/-- The **cyclic bond-matching condition** on a physical string: the right bit
of each letter is the left bit of the next one around the ring, with the
successor given by `finRotate`.  It is the open condition together with the
wraparound step (`chainOK_succ`).

Project example; not from CPSV16. -/
def ChainOK (N : ℕ) (σ : Fin N → Fin 8) : Prop :=
  ∀ n : Fin N, gate (σ n) (σ (finRotate N n))

/-- The cyclic bond-matching condition is a finite conjunction of equalities of
bits, hence decidable. -/
instance decidableChainOK (N : ℕ) (σ : Fin N → Fin 8) : Decidable (ChainOK N σ) :=
  inferInstanceAs (Decidable (∀ n : Fin N, gate (σ n) (σ (finRotate N n))))

/-- Peeling the first site off the open bond-matching condition: the condition
on a string of length at least two is the match across the first bond together
with the condition on the tail. -/
lemma openOK_succ {n : ℕ} (σ : Fin (n + 2) → Fin 8) :
    OpenOK σ ↔ gate (σ 0) (σ (Fin.succ 0)) ∧ OpenOK (fun i => σ i.succ) := by
  rw [OpenOK, OpenOK, Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.succ_castSucc]

/-- The cyclic bond-matching condition is the open condition on the segment
together with the wraparound match from the last letter back to the first. -/
lemma chainOK_succ {n : ℕ} (σ : Fin (n + 1) → Fin 8) :
    ChainOK (n + 1) σ ↔ OpenOK σ ∧ gate (σ (Fin.last n)) (σ 0) := by
  rw [ChainOK, Fin.forall_fin_succ', OpenOK]
  simp only [Fin.finRotate_succ_castSucc, finRotate_last]

/-! ### The open-chain product of letters -/

/-- Multiplying a letter of the twisted dimer into a sum of matrix units with
one summand per block label keeps the block label and is gated by the
bond-matching condition between the letter and the first index pair of the
sum.

Project example; not from CPSV16. -/
lemma T_mul_single_sum (i j : Fin 8) (l l' r r' : Fin 2) (c : Fin 2 → ℂ) :
    T i j * (∑ k : Fin 2, Matrix.single (physIdx l l' k) (physIdx r r' k) (c k)) =
      if bitR i = l ∧ bitR j = l' then
        ∑ k : Fin 2, Matrix.single (physIdx (bitL i) (bitL j) k) (physIdx r r' k)
          (coef k i j * c k)
      else 0 := by
  simp only [T, Fin.sum_univ_two, add_mul, mul_add, single_mul_single_ite, physIdx_inj]
  by_cases h1 : bitR i = l <;> by_cases h2 : bitR j = l' <;> simp [h1, h2]

/-- **Open-chain product formula.**  The ordered product of the letters of the
twisted dimer along a pair of physical strings vanishes unless both strings
satisfy the open bond-matching condition, in which case it is the sum over the
two horizontal block labels of a single matrix unit: its row index is read off
the left bits of the first letters, its column index off the right bits of the
last letters, and its coefficient is the product of the one-site coefficients.

Project example; not from CPSV16. -/
lemma evalWord_T_ofFn : ∀ (n : ℕ) (σ τ : Fin (n + 1) → Fin 8),
    evalWord T (List.ofFn σ) (List.ofFn τ) =
      if OpenOK σ ∧ OpenOK τ then
        ∑ k : Fin 2, Matrix.single (physIdx (bitL (σ 0)) (bitL (τ 0)) k)
          (physIdx (bitR (σ (Fin.last n))) (bitR (τ (Fin.last n))) k)
          (∏ i : Fin (n + 1), coef k (σ i) (τ i))
      else 0 := by
  intro n
  induction n with
  | zero =>
      intro σ τ
      have hopen : ∀ ρ : Fin 1 → Fin 8, OpenOK ρ := fun ρ i => i.elim0
      rw [ite_eq_left ⟨hopen σ, hopen τ⟩]
      simp only [List.ofFn_succ, List.ofFn_zero, evalWord_cons, evalWord_nil, mul_one,
        Fin.last_zero, Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty]
      rfl
  | succ n ih =>
      intro σ τ
      rw [List.ofFn_succ, List.ofFn_succ (f := τ), evalWord_cons,
        ih (fun i => σ i.succ) (fun i => τ i.succ)]
      by_cases hs : OpenOK (fun i => σ i.succ) ∧ OpenOK (fun i => τ i.succ)
      · rw [ite_eq_left hs, T_mul_single_sum]
        by_cases hg : bitR (σ 0) = bitL (σ (Fin.succ 0)) ∧ bitR (τ 0) = bitL (τ (Fin.succ 0))
        · rw [ite_eq_left hg,
            ite_eq_left ⟨(openOK_succ σ).2 ⟨hg.1, hs.1⟩, (openOK_succ τ).2 ⟨hg.2, hs.2⟩⟩]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [Fin.prod_univ_succ]
          rw [Fin.succ_last]
        · rw [ite_eq_right hg, ite_eq_right]
          rintro ⟨hcσ, hcτ⟩
          exact hg ⟨((openOK_succ σ).1 hcσ).1, ((openOK_succ τ).1 hcτ).1⟩
      · rw [ite_eq_right hs, mul_zero, ite_eq_right]
        rintro ⟨hcσ, hcτ⟩
        exact hs ⟨((openOK_succ σ).1 hcσ).2, ((openOK_succ τ).1 hcτ).2⟩

/-! ### The closed-chain entry formula -/

/-- The indicator matrix of the cyclic bond-matching condition: the entry at a
pair of physical strings is one when both strings satisfy the condition and
zero otherwise.  It is the outer product of the indicator vector of the
condition with itself, hence rank one and positive semidefinite
(`chainIndicator_posSemidef`).

Project example; not from CPSV16. -/
def chainIndicator (N : ℕ) : Matrix (Fin N → Fin 8) (Fin N → Fin 8) ℂ :=
  Matrix.of fun σ τ => if ChainOK N σ ∧ ChainOK N τ then (1 : ℂ) else 0

/-- The chain indicator is the outer product of the indicator vector of the
cyclic bond-matching condition with itself, hence positive semidefinite. -/
lemma chainIndicator_posSemidef (N : ℕ) : (chainIndicator N).PosSemidef := by
  let c : (Fin N → Fin 8) → ℂ := fun σ => if ChainOK N σ then (1 : ℂ) else 0
  have h_eq : chainIndicator N = Matrix.vecMulVec c (star c) := by
    ext σ τ
    dsimp [chainIndicator, c, Matrix.vecMulVec, Matrix.of_apply]
    by_cases hσ : ChainOK N σ <;> by_cases hτ : ChainOK N τ <;> simp [hσ, hτ]
  rw [h_eq]
  exact Matrix.posSemidef_vecMulVec_self_star c

/-- **Closed-chain entry formula.**  For a positive chain length, the matrix
element of the closed operator at a pair of physical strings is the cyclic
bond-matching indicator times the sum over the two horizontal block labels of
the product of the one-site coefficients along the ring.

Both horizontal blocks contribute with the same bond-matching gate, because the
block label is part of the bond index and is preserved by every letter product;
closing the trace adds the wraparound match to the open condition.

Project example; not from CPSV16. -/
theorem mpo_T_entry_formula {N : ℕ} (hN : 0 < N) (σ τ : Fin N → Fin 8) :
    mpo T N σ τ = chainIndicator N σ τ * ∑ k : Fin 2, ∏ n : Fin N, coef k (σ n) (τ n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_T_ofFn n σ τ]
  by_cases hopen : OpenOK σ ∧ OpenOK τ
  · rw [ite_eq_left hopen, Matrix.trace_sum]
    by_cases hw : gate (σ (Fin.last n)) (σ 0) ∧ gate (τ (Fin.last n)) (τ 0)
    · have hchain : ChainOK (n + 1) σ ∧ ChainOK (n + 1) τ :=
        ⟨(chainOK_succ σ).2 ⟨hopen.1, hw.1⟩, (chainOK_succ τ).2 ⟨hopen.2, hw.2⟩⟩
      rw [chainIndicator, Matrix.of_apply, ite_eq_left hchain, one_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show physIdx (bitR (σ (Fin.last n))) (bitR (τ (Fin.last n))) k =
          physIdx (bitL (σ 0)) (bitL (τ 0)) k from by rw [hw.1, hw.2]]
      exact Matrix.trace_single_eq_same _ _
    · have hchain : ¬ (ChainOK (n + 1) σ ∧ ChainOK (n + 1) τ) := fun h =>
        hw ⟨((chainOK_succ σ).1 h.1).2, ((chainOK_succ τ).1 h.2).2⟩
      rw [chainIndicator, Matrix.of_apply, ite_eq_right hchain, zero_mul]
      refine Finset.sum_eq_zero fun k _ => Matrix.trace_single_eq_of_ne _ _ _ ?_
      rw [Ne, physIdx_inj]
      rintro ⟨h1, h2, -⟩
      exact hw ⟨h1.symm, h2.symm⟩
  · have hchain : ¬ (ChainOK (n + 1) σ ∧ ChainOK (n + 1) τ) := fun h =>
      hopen ⟨((chainOK_succ σ).1 h.1).1, ((chainOK_succ τ).1 h.2).1⟩
    rw [ite_eq_right hopen, chainIndicator, Matrix.of_apply, ite_eq_right hchain, zero_mul,
      Matrix.trace_zero]

/-! ### The local four-by-four factors -/

/-- The local four-by-four factor of the horizontal block `k`, indexed by pairs
(flag bit, left bit): it is diagonal in the flag bit, with the block
$C_k\,(\tau_k)_{ff}$ in the flag sector $f$.  The one-site coefficient of the
tensor is half of its entry at the flag and left bits of the two physical
indices (`coef_eq_gLoc`).

Project example; not from CPSV16. -/
def gLoc (k : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun a b => if a.1 = b.1 then ((Cmat k a.2 b.2 * tau k a.1 : ℝ) : ℂ) else 0

/-- The `N`-fold Kronecker power of the local factor `gLoc k`, written
entrywise: the entry at a pair of strings of (flag bit, left bit) pairs is the
product of the local entries along the string.

Project example; not from CPSV16. -/
def gPow (k : Fin 2) (N : ℕ) :
    Matrix (Fin N → Fin 2 × Fin 2) (Fin N → Fin 2 × Fin 2) ℂ :=
  Matrix.of fun a b => ∏ i : Fin N, gLoc k (a i) (b i)

/-- Reading a physical string through its flag and left bits.  It pulls the
Kronecker powers back to the physical configuration space of the closed
operator.

Project example; not from CPSV16. -/
def flagLeft (N : ℕ) (σ : Fin N → Fin 8) : Fin N → Fin 2 × Fin 2 :=
  fun i => (bitF (σ i), bitL (σ i))

/-- The one-site coefficient of the tensor is half the entry of the local
factor at the flag and left bits of the two physical indices. -/
lemma coef_eq_gLoc (k : Fin 2) (i j : Fin 8) :
    coef k i j = (1 / 2 : ℂ) * gLoc k (bitF i, bitL i) (bitF j, bitL j) := by
  by_cases h : bitF i = bitF j
  · simp only [coef, gLoc, Matrix.of_apply, h]
    push_cast
    ring
  · simp [coef, gLoc, h]

/-- The sum of the two local factors is positive semidefinite: it is block
diagonal in the flag bit, equal to $\tfrac74$ times the projector onto the
uniform vector in the sector $f = 0$ and to $\tfrac14$ times the projector onto
the alternating vector in the sector $f = 1$. -/
lemma gLoc_add_posSemidef : (gLoc 0 + gLoc 1).PosSemidef := by
  set u : Fin 2 × Fin 2 → ℂ := fun a => if a.1 = 0 then 1 else 0 with hu
  set w : Fin 2 × Fin 2 → ℂ := fun a => if a.1 = 1 then (if a.2 = 0 then 1 else -1) else 0 with hw
  have h_eq : gLoc 0 + gLoc 1 =
      (7 / 8 : ℂ) • Matrix.vecMulVec u (star u) + (1 / 8 : ℂ) • Matrix.vecMulVec w (star w) := by
    ext a b
    obtain ⟨f, l⟩ := a
    obtain ⟨f', l'⟩ := b
    fin_cases f <;> fin_cases l <;> fin_cases f' <;> fin_cases l' <;>
      norm_num [gLoc, hu, hw, Cmat, cDiag_eq, cOff_eq, tau, Matrix.vecMulVec]
  rw [h_eq]
  exact ((Matrix.posSemidef_vecMulVec_self_star u).smul (by positivity)).add
    ((Matrix.posSemidef_vecMulVec_self_star w).smul (by positivity))

/-- The difference of the two local factors is positive semidefinite: it is the
sum of the two projectors of `gLoc_add_posSemidef` with the flag sectors
exchanged. -/
lemma gLoc_sub_posSemidef : (gLoc 0 - gLoc 1).PosSemidef := by
  set u : Fin 2 × Fin 2 → ℂ := fun a => if a.1 = 0 then (if a.2 = 0 then 1 else -1) else 0 with hu
  set w : Fin 2 × Fin 2 → ℂ := fun a => if a.1 = 1 then 1 else 0 with hw
  have h_eq : gLoc 0 - gLoc 1 =
      (1 / 8 : ℂ) • Matrix.vecMulVec u (star u) + (7 / 8 : ℂ) • Matrix.vecMulVec w (star w) := by
    ext a b
    obtain ⟨f, l⟩ := a
    obtain ⟨f', l'⟩ := b
    fin_cases f <;> fin_cases l <;> fin_cases f' <;> fin_cases l' <;>
      norm_num [gLoc, hu, hw, Cmat, cDiag_eq, cOff_eq, tau, Matrix.vecMulVec]
  rw [h_eq]
  exact ((Matrix.posSemidef_vecMulVec_self_star u).smul (by positivity)).add
    ((Matrix.posSemidef_vecMulVec_self_star w).smul (by positivity))

/-! ### Positivity of the Kronecker powers -/

/-- **The sum and the difference of the two Kronecker powers are positive
semidefinite.**  Neither combination is itself a Kronecker power, so the two
statements are proved together by induction on the chain length: peeling the
last site off the ring writes each combination at length `N + 1` as half the
sum of the Kronecker products of the two combinations at length `N` with the
two combinations of the local factors, all four of which are positive
semidefinite.

Project example; not from CPSV16. -/
lemma gPow_add_sub_posSemidef (N : ℕ) :
    (gPow 0 N + gPow 1 N).PosSemidef ∧ (gPow 0 N - gPow 1 N).PosSemidef := by
  induction N with
  | zero =>
      have h : ∀ k : Fin 2, gPow k 0 = 1 := by
        intro k
        ext a b
        have hab : a = b := Subsingleton.elim _ _
        subst hab
        simp [gPow]
      rw [h 0, h 1]
      exact ⟨Matrix.PosSemidef.one.add Matrix.PosSemidef.one,
        by simpa using Matrix.PosSemidef.zero⟩
  | succ N ih =>
      set e : (Fin (N + 1) → Fin 2 × Fin 2) ≃ (Fin N → Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
        Fin.succFunEquiv (Fin 2 × Fin 2) N
      have h_fst : ∀ f : Fin (N + 1) → Fin 2 × Fin 2, (e f).1 = f ∘ Fin.castSucc :=
        fun _ => funext fun _ => rfl
      have h_snd : ∀ f : Fin (N + 1) → Fin 2 × Fin 2, (e f).2 = f (Fin.last N) :=
        fun _ => rfl
      have hadd : gPow 0 (N + 1) + gPow 1 (N + 1) =
          ((1 / 2 : ℂ) •
            (Matrix.kroneckerMap (· * ·) (gPow 0 N + gPow 1 N) (gLoc 0 + gLoc 1) +
              Matrix.kroneckerMap (· * ·) (gPow 0 N - gPow 1 N)
                (gLoc 0 - gLoc 1))).submatrix e e := by
        ext a b
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply,
          Matrix.kroneckerMap_apply, gPow, Matrix.of_apply, Fin.prod_univ_castSucc, smul_eq_mul,
          h_fst, h_snd, Function.comp_apply]
        ring
      have hsub : gPow 0 (N + 1) - gPow 1 (N + 1) =
          ((1 / 2 : ℂ) •
            (Matrix.kroneckerMap (· * ·) (gPow 0 N + gPow 1 N) (gLoc 0 - gLoc 1) +
              Matrix.kroneckerMap (· * ·) (gPow 0 N - gPow 1 N)
                (gLoc 0 + gLoc 1))).submatrix e e := by
        ext a b
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply,
          Matrix.kroneckerMap_apply, gPow, Matrix.of_apply, Fin.prod_univ_castSucc, smul_eq_mul,
          h_fst, h_snd, Function.comp_apply]
        ring
      refine ⟨hadd ▸ ?_, hsub ▸ ?_⟩
      · exact (((ih.1.kronecker gLoc_add_posSemidef).add
          (ih.2.kronecker gLoc_sub_posSemidef)).smul (by positivity)).submatrix e
      · exact (((ih.1.kronecker gLoc_sub_posSemidef).add
          (ih.2.kronecker gLoc_add_posSemidef)).smul (by positivity)).submatrix e

/-! ### The twisted dimer is a density-operator tensor -/

/-- The product of the one-site coefficients of one horizontal block along the
ring is the corresponding entry of the Kronecker power of the local factor,
scaled by the site normalization $2^{-N}$. -/
lemma prod_coef_eq_gPow (k : Fin 2) {N : ℕ} (σ τ : Fin N → Fin 8) :
    (∏ n : Fin N, coef k (σ n) (τ n)) =
      (1 / 2 : ℂ) ^ N * gPow k N (flagLeft N σ) (flagLeft N τ) := by
  simp only [coef_eq_gLoc, gPow, flagLeft, Matrix.of_apply, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The closed operator as a Schur product.**  For a positive chain length,
the closed operator is $2^{-N}$ times the Hadamard product of the cyclic
bond-matching indicator with the pullback, along the flag and left bits, of the
sum of the two Kronecker powers.

Project example; not from CPSV16. -/
theorem mpo_T_eq_smul_hadamard {N : ℕ} (hN : 0 < N) :
    mpo T N = (1 / 2 : ℂ) ^ N •
      (chainIndicator N ⊙ (gPow 0 N + gPow 1 N).submatrix (flagLeft N) (flagLeft N)) := by
  ext σ τ
  rw [mpo_T_entry_formula hN, Fin.sum_univ_two, prod_coef_eq_gPow, prod_coef_eq_gPow]
  simp only [Matrix.smul_apply, Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

/-- **The twisted quantum dimer is a matrix product density operator.**  The
closed operator is positive semidefinite for every positive chain length: it is
a nonnegative multiple of the Hadamard product of the rank-one bond-matching
indicator with the pullback of the sum of the two Kronecker powers, and the
Schur product theorem turns positive semidefiniteness of the two factors into
positive semidefiniteness of the product.

Source: arXiv:1606.00608, Section 4, equation `eq:III_MPDOform`, lines
623--630, for the notion of a matrix product density operator; the tensor is a
project example motivated by lines 995--1010, not a tensor stated in
CPSV16. -/
theorem T_isMPDO : IsMPDO T := by
  intro N hN
  rw [mpo_T_eq_smul_hadamard hN]
  exact ((chainIndicator_posSemidef N).hadamard
    ((gPow_add_sub_posSemidef N).1.submatrix (flagLeft N))).smul (by positivity)

end MPOTensor.TwistedDimer
