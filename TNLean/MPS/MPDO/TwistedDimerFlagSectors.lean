/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.TwistedDimerMPDO

/-!
# The flag sectors of the $\mathbb Z_2$-twisted quantum dimer

**Scope: the two flag-sector tensors and their closed operators.**  The letters
of the $\mathbb Z_2$-twisted quantum dimer `T` of `TNLean.MPS.MPDO.TwistedDimer`
are diagonal in the flag qubit, so the vertically viewed tensor splits along the
flag value $f \in \{0, 1\}$ into two tensors $M_f$ with four-dimensional
physical space, the qubits $L, R$, and letters indexed by pairs of horizontal
bond indices.  This file defines the normalized sector tensors
$\widehat M_f = M_f / \mu$ with $\mu = 5/8$, shows that their letters are the
restrictions of the letters of `T` to the flag value $f$, and proves the closed
form of their closed operators $O_L(\widehat M_f)$ on a ring of $L$ sites.
The tensor is a project example motivated by the length-dependence question
after Theorem 4.14 of arXiv:1606.00608 (lines 995--1010); it is not a tensor
stated in that source.

It is not asserted here that the sector tensors form the canonical
basis of normal tensors of `T`; the same-length product law of the sector
operators is proved in `TNLean.MPS.MPDO.TwistedDimerProductLaw`.

## Main definitions

* `flagWeight` — the one-site weight $C_k[p,p']\,(\tau_k)_{ff} / (2\mu)$ of the
  bond index $(p, p', k)$ in the sector $f$;
* `unitTensor` — the bond-four tensors whose letter at a pair of indices is a
  single matrix unit, the common shape of the horizontal blocks of `T` and of
  the flag sectors;
* `flagMPO` — the normalized sector tensor $\widehat M_f$, read as a tensor with
  eight-valued physical indices and bond dimension four;
* `flagOperatorFamily` — the family $L \mapsto O_L(\widehat M_f)$ of closed
  sector operators, in the form used by the same-length product predicate.

## Main results

* `flagMPO_apply_eq_T` — the letter of $\widehat M_f$ is $\mu^{-1}$ times the
  restriction of the vertical letter of `T` to the flag value $f$;
* `mpo_unitTensor_apply` — the closed-chain entry formula for a matrix-unit
  tensor: the cyclic bond-matching indicator times the product of the
  coefficients;
* `mpo_flagMPO_apply` — the closed operator $O_L(\widehat M_f)$ has entry
  $\prod_n C_{k_n}[p_n, p'_n]\,(\tau_{k_n})_{ff} / (2\mu)$ at a pair of
  cyclically bond-matched words with equal block labels, and vanishes
  otherwise.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii), lines 972--985 (the closed operators $O_L(M_\alpha)$ and
  their same-length algebra) and lines 995--1010 (the length-dependence
  question motivating this project example)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### Sector weights -/

/-- The vertical normalization $\mu = 5/8$ of the flag sectors: the square root
of the vertical spectral radius $\mu^2 = (x^2 + y^2)/2 = 25/64$ of each
sector at the rational point $x = 7/8$, $y = 1/8$.

Project example; not from CPSV16. -/
def mu : ℝ := 5 / 8

/-- The one-site weight of the bond index $a = (p, p', k)$ in the flag sector
$f$: the entry $C_k[p,p']$ times the flag sign $(\tau_k)_{ff}$, divided by
$2\mu$.

Project example; not from CPSV16. -/
def flagWeight (f : Fin 2) (a : Fin 8) : ℂ :=
  ((Cmat (bitF a) (bitL a) (bitR a) * tau (bitF a) f / (2 * mu) : ℝ) : ℂ)

lemma flagWeight_physIdx (f p p' k : Fin 2) :
    flagWeight f (physIdx p p' k) = ((Cmat k p p' * tau k f / (2 * mu) : ℝ) : ℂ) := by
  simp [flagWeight]

/-- The coefficient of the letter of the sector $f$ at the bond pair `(a, b)`:
the one-site weight of `a` when the two block labels agree, and zero
otherwise. -/
def flagCoef (f : Fin 2) (a b : Fin 8) : ℂ :=
  if bitF a = bitF b then flagWeight f a else 0

/-! ### Matrix-unit tensors with bond dimension four -/

/-- The tensor with eight-valued physical indices and bond dimension four whose
letter at the pair `(i, j)` is the matrix unit at the left bits over the right
bits, with coefficient `c i j`.  The horizontal blocks of the twisted dimer and
its flag sectors are all of this shape.

Project example; not from CPSV16. -/
def unitTensor (c : Fin 8 → Fin 8 → ℂ) : MPOTensor 8 4 := fun i j =>
  Matrix.single (finProdFinEquiv (bitL i, bitL j)) (finProdFinEquiv (bitR i, bitR j)) (c i j)

/-- The horizontal block `k` of the twisted dimer is the matrix-unit tensor of
its one-site coefficients. -/
lemma block_eq_unitTensor (k : Fin 2) : block k = unitTensor (coef k) := rfl

/-- The normalized flag sector $\widehat M_f = M_f / \mu$: the letter at the
bond pair $((p, p', k), (q, q', k'))$ is
$[k = k']\,\tfrac{1}{2\mu}\,C_k[p,p']\,(\tau_k)_{ff}\,E_{pp'} \otimes E_{qq'}$
on the two qubits $L, R$.  The letters are read as a tensor with eight-valued
physical indices (the horizontal bond indices of `T`) and bond dimension four
(the physical space of the sector).

Project example; not from CPSV16. -/
def flagMPO (f : Fin 2) : MPOTensor 8 4 := unitTensor (flagCoef f)

/-- **The sector letters restrict the letters of the tensor.**  The entry of
the letter of $\widehat M_f$ at the bond pair `(a, b)` between the qubit
configurations $(l, r)$ and $(l', r')$ is $\mu^{-1}$ times the bond-matrix
entry of `T` at the physical letters $((l, r, f), (l', r', f))$ carrying the
common flag value $f$. -/
theorem flagMPO_apply_eq_T (f : Fin 2) (a b : Fin 8) (l r l' r' : Fin 2) :
    flagMPO f a b (finProdFinEquiv (l, r)) (finProdFinEquiv (l', r')) =
      ((mu : ℝ) : ℂ)⁻¹ * T (physIdx l r f) (physIdx l' r' f) a b := by
  obtain ⟨p, p', k, rfl⟩ : ∃ p p' k, a = physIdx p p' k := ⟨_, _, _, (physIdx_bits a).symm⟩
  obtain ⟨q, q', k', rfl⟩ : ∃ q q' k', b = physIdx q q' k' := ⟨_, _, _, (physIdx_bits b).symm⟩
  rw [T_apply_blocks]
  simp only [flagMPO, unitTensor, flagCoef, block, bitL_physIdx, bitR_physIdx, bitF_physIdx,
    Matrix.single_apply, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, coef_physIdx,
    flagWeight_physIdx, ite_true]
  by_cases hk : k = k'
  · subst hk
    by_cases h : l = p ∧ l' = p'
    · obtain ⟨rfl, rfl⟩ := h
      by_cases h' : r = q ∧ r' = q'
      · obtain ⟨rfl, rfl⟩ := h'
        simp only [and_self, ite_true]
        push_cast
        have hmu : (mu : ℂ) ≠ 0 := by norm_num [mu]
        field_simp
      · have h'' : ¬ (q = r ∧ q' = r') := fun hh => h' ⟨hh.1.symm, hh.2.symm⟩
        simp [h', h'']
    · have h' : ¬ (p = l ∧ q = r) ∨ ¬ (p' = l' ∧ q' = r') := by tauto
      rcases h' with h' | h' <;> simp [h', h]
  · simp [hk]

/-! ### Closed operators of matrix-unit tensors -/

/-- A matrix unit with row index a pair of right bits and column index an
arbitrary pair, multiplied on the left by a letter of a matrix-unit tensor,
is again a matrix unit or zero according to the bond-matching condition. -/
lemma unitTensor_mul_single (c : Fin 8 → Fin 8 → ℂ) (i j : Fin 8) (l l' r r' : Fin 2)
    (u : ℂ) :
    unitTensor c i j * Matrix.single (finProdFinEquiv (l, l')) (finProdFinEquiv (r, r')) u =
      if bitR i = l ∧ bitR j = l' then
        Matrix.single (finProdFinEquiv (bitL i, bitL j)) (finProdFinEquiv (r, r')) (c i j * u)
      else 0 := by
  unfold unitTensor
  by_cases h : bitR i = l ∧ bitR j = l'
  · obtain ⟨h1, h2⟩ := h
    rw [ite_eq_left ⟨h1, h2⟩, h1, h2, Matrix.single_mul_single_same]
  · rw [ite_eq_right h, Matrix.single_mul_single_of_ne]
    intro heq
    exact h (by simpa [Prod.mk.injEq] using finProdFinEquiv.injective heq)

/-- **Open-chain product formula for matrix-unit tensors.**  The ordered
product of the letters along a pair of words vanishes unless both words
satisfy the open bond-matching condition, in which case it is the single matrix
unit whose row is read off the left bits of the first letters, whose column is
read off the right bits of the last letters, and whose coefficient is the
product of the coefficients.

Project example; not from CPSV16. -/
lemma evalWord_unitTensor_ofFn (c : Fin 8 → Fin 8 → ℂ) :
    ∀ (n : ℕ) (σ τ : Fin (n + 1) → Fin 8),
      evalWord (unitTensor c) (List.ofFn σ) (List.ofFn τ) =
        if IsOpenBondMatched σ ∧ IsOpenBondMatched τ then
          Matrix.single (finProdFinEquiv (bitL (σ 0), bitL (τ 0)))
            (finProdFinEquiv (bitR (σ (Fin.last n)), bitR (τ (Fin.last n))))
            (∏ i : Fin (n + 1), c (σ i) (τ i))
        else 0 := by
  intro n
  induction n with
  | zero =>
      intro σ τ
      have hopen : ∀ ρ : Fin 1 → Fin 8, IsOpenBondMatched ρ := fun ρ i => i.elim0
      rw [ite_eq_left ⟨hopen σ, hopen τ⟩]
      simp only [List.ofFn_succ, List.ofFn_zero, evalWord_cons, evalWord_nil, mul_one,
        Fin.last_zero, Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      rfl
  | succ n ih =>
      intro σ τ
      rw [List.ofFn_succ, List.ofFn_succ (f := τ), evalWord_cons,
        ih (fun i => σ i.succ) (fun i => τ i.succ)]
      by_cases hs : IsOpenBondMatched (fun i => σ i.succ) ∧ IsOpenBondMatched (fun i => τ i.succ)
      · rw [ite_eq_left hs, unitTensor_mul_single]
        by_cases hg : bitR (σ 0) = bitL (σ (Fin.succ 0)) ∧ bitR (τ 0) = bitL (τ (Fin.succ 0))
        · rw [ite_eq_left hg, ite_eq_left ⟨
              (isOpenBondMatched_succ σ).2 ⟨hg.1, hs.1⟩,
              (isOpenBondMatched_succ τ).2 ⟨hg.2, hs.2⟩⟩]
          conv_rhs => rw [Fin.prod_univ_succ]
          rw [Fin.succ_last]
        · rw [ite_eq_right hg, ite_eq_right]
          rintro ⟨hcσ, hcτ⟩
          exact hg ⟨((isOpenBondMatched_succ σ).1 hcσ).1, ((isOpenBondMatched_succ τ).1 hcτ).1⟩
      · rw [ite_eq_right hs, mul_zero, ite_eq_right]
        rintro ⟨hcσ, hcτ⟩
        exact hs ⟨((isOpenBondMatched_succ σ).1 hcσ).2, ((isOpenBondMatched_succ τ).1 hcτ).2⟩

/-- **Closed-chain entry formula for matrix-unit tensors.**  For a positive
chain length, the matrix element of the closed operator at a pair of words is
the cyclic bond-matching indicator times the product of the coefficients along
the ring.

Project example; not from CPSV16. -/
theorem mpo_unitTensor_apply (c : Fin 8 → Fin 8 → ℂ) {N : ℕ} (hN : 0 < N)
    (σ τ : Fin N → Fin 8) :
    mpo (unitTensor c) N σ τ = chainIndicator N σ τ * ∏ n : Fin N, c (σ n) (τ n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_unitTensor_ofFn c n σ τ]
  by_cases hopen : IsOpenBondMatched σ ∧ IsOpenBondMatched τ
  · rw [ite_eq_left hopen]
    by_cases hw : gate (σ (Fin.last n)) (σ 0) ∧ gate (τ (Fin.last n)) (τ 0)
    · have hchain : IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) τ :=
        ⟨(isCyclicBondMatched_succ σ).2 ⟨hopen.1, hw.1⟩,
          (isCyclicBondMatched_succ τ).2 ⟨hopen.2, hw.2⟩⟩
      rw [chainIndicator, Matrix.of_apply, ite_eq_left hchain, one_mul]
      rw [show finProdFinEquiv (bitR (σ (Fin.last n)), bitR (τ (Fin.last n))) =
          finProdFinEquiv (bitL (σ 0), bitL (τ 0)) from by rw [hw.1, hw.2]]
      exact Matrix.trace_single_eq_same _ _
    · have hchain : ¬ (IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) τ) := fun h =>
        hw ⟨((isCyclicBondMatched_succ σ).1 h.1).2, ((isCyclicBondMatched_succ τ).1 h.2).2⟩
      rw [chainIndicator, Matrix.of_apply, ite_eq_right hchain, zero_mul]
      refine Matrix.trace_single_eq_of_ne _ _ _ ?_
      rw [Ne, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
      rintro ⟨h1, h2⟩
      exact hw ⟨h1.symm, h2.symm⟩
  · have hchain : ¬ (IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) τ) := fun h =>
      hopen ⟨((isCyclicBondMatched_succ σ).1 h.1).1, ((isCyclicBondMatched_succ τ).1 h.2).1⟩
    rw [ite_eq_right hopen, chainIndicator, Matrix.of_apply, ite_eq_right hchain, zero_mul,
      Matrix.trace_zero]

/-! ### The closed sector operators -/

/-- The product of the sector coefficients along a pair of words is the product
of the one-site weights of the first word when the block labels agree
sitewise, and zero otherwise. -/
lemma prod_flagCoef (f : Fin 2) {L : ℕ} (σ τ : Fin L → Fin 8) :
    (∏ n, flagCoef f (σ n) (τ n)) =
      if ∀ n, bitF (σ n) = bitF (τ n) then ∏ n, flagWeight f (σ n) else 0 := by
  by_cases h : ∀ n, bitF (σ n) = bitF (τ n)
  · rw [ite_eq_left h]
    exact Finset.prod_congr rfl fun n _ => by simp [flagCoef, h n]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨n, hn⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ n) (by simp [flagCoef, hn])

/-- **Closed form of the sector operators.**  For a positive length `L`, the
entry of $O_L(\widehat M_f)$ at a pair of words of horizontal bond indices is
the product of the one-site weights
$C_{k_n}[p_n, p'_n]\,(\tau_{k_n})_{ff} / (2\mu)$ of the first word when both
words are cyclically bond matched and carry the same block labels, and zero
otherwise.

Project example; not from CPSV16. -/
theorem mpo_flagMPO_apply (f : Fin 2) {L : ℕ} (hL : 0 < L) (σ τ : Fin L → Fin 8) :
    mpo (flagMPO f) L σ τ =
      if IsCyclicBondMatched L σ ∧ IsCyclicBondMatched L τ ∧ ∀ n, bitF (σ n) = bitF (τ n) then
        ∏ n, flagWeight f (σ n)
      else 0 := by
  rw [flagMPO, mpo_unitTensor_apply _ hL, prod_flagCoef, chainIndicator, Matrix.of_apply]
  by_cases h1 : IsCyclicBondMatched L σ ∧ IsCyclicBondMatched L τ <;>
    by_cases h2 : ∀ n, bitF (σ n) = bitF (τ n) <;> simp [h1, h2]

/-- The flag sector $\widehat M_f$ read as a tensor with a doubled physical
index, the form in which vertical basis-of-normal-tensors data are recorded. -/
def flagFamily (f : Fin 2) : MPSTensor (8 * 8) 4 := (flagMPO f).toMPSTensor

lemma verticalBNTMPO_flagFamily (f : Fin 2) : verticalBNTMPO (flagFamily f) = flagMPO f := by
  funext a b
  change flagMPO f (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = flagMPO f a b
  rw [Equiv.symm_apply_apply]

/-- **The sector operator family.**  The family $L \mapsto O_L(\widehat M_f)$
of closed operators of the two flag sectors, in the form used by the
same-length product predicate of arXiv:1606.00608, Theorem 4.14(ii),
lines 972--985.  It is not asserted here that the two sectors form the canonical
basis of normal tensors of the twisted dimer. -/
def flagOperatorFamily :
    BNTLabelOperatorFamily (Fin 2) (fun L => Matrix (Fin L → Fin 8) (Fin L → Fin 8) ℂ) :=
  verticalBNTOperatorFamily (D := 8) (dim := fun _ => 4) flagFamily

@[simp] lemma flagOperatorFamily_operator (L : ℕ) (f : Fin 2) :
    flagOperatorFamily.operator L f = mpo (flagMPO f) L := by
  simp [flagOperatorFamily, verticalBNTMPO_flagFamily]

end MPOTensor.TwistedDimer
