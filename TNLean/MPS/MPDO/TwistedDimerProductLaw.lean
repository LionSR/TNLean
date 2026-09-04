/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.MPS.MPDO.TwistedDimerCoefficients
import TNLean.MPS.MPDO.TwistedDimerFlagSectors

/-!
# The same-length product law of the twisted-dimer flag sectors

**Scope: the product law of the sector operators.**  This file proves that the
closed operators $O_L(\widehat M_f)$ of the two normalized flag sectors of the
$\mathbb Z_2$-twisted quantum dimer (`TNLean.MPS.MPDO.TwistedDimerFlagSectors`)
satisfy, for every positive length $L$ and all flag values $f, f'$,
$$
  O_L(\widehat M_f)\,O_L(\widehat M_{f'})
    = \alpha^L\,O_L(\widehat M_{f+f'}) + \beta^L\,O_L(\widehat M_{f+f'+1}),
  \qquad \alpha = \tfrac{7}{10},\ \beta = \tfrac{1}{10},
$$
which is the same-length product law of arXiv:1606.00608, Theorem 4.14(ii),
lines 972--985, with the two-label coefficient family of
`TNLean.MPS.MPDO.TwistedDimerCoefficients`.  The flag-sector operators of the
displayed tensor therefore satisfy the product law with the two-label
coefficients; it is not asserted here that the two sectors form the canonical
basis of normal tensors of the tensor.  The tensor is a project example
motivated by the length-dependence question after Theorem 4.14 (lines
995--1010); it is not a tensor stated in that source.

## The argument

The entry of $O_L(\widehat M_f)$ at a pair of cyclically bond-matched words
with common block labels $k_n$ is $\prod_n C_{k_n}[p_n, p_{n+1}]
(\tau_{k_n})_{ff} / (2\mu)$, where $p_n$ runs over the left bits of the first
word.  Multiplying two such operators sums over a middle word, which is
determined by its left bits $t_n$ once the block labels are fixed, and the
middle sum is the transfer-matrix trace
$$
  \sum_t \prod_n C_{k_n}[t_n, t_{n+1}]
    = \operatorname{tr}\bigl(C_{k_1} \cdots C_{k_L}\bigr)
    = x^L + (-1)^{\sum_n k_n} y^L,
$$
because $C_k = x P_+ + (-1)^k y P_-$ with orthogonal idempotents $P_\pm$.
The flag signs multiply as $(\tau_k)_{ff}(\tau_k)_{f'f'} = (\tau_k)_{gg}$ with
$g = f + f'$, and the sign $(-1)^{\sum_n k_n}$ of the second summand shifts the
flag label by one.  Since $x / (2\mu) = 7/10$ and $y / (2\mu) = 1/10$, the two
summands are $\alpha^L$ and $\beta^L$ times the entries of the two sector
operators at the labels $f + f'$ and $f + f' + 1$.

## Main results

* `sum_cyclic_Cmat` — the cyclic transfer sum of the bond matrices along a
  string of block labels is $x^L + (-1)^{\sum k_n} y^L$;
* `mpo_flagMPO_mul` — the same-length product law of the sector operators;
* `flagOperatorFamily_hasSameLengthProductForm` — the product law in the form
  of the abstract same-length product predicate, with the two-label
  coefficient family.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii), lines 972--985 (the same-length product law) and lines
  995--1010 (the length-dependence question motivating this project example)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### Sign form of the bond matrices -/

/-- The flag sign $(\tau_k)_{11} = (-1)^k$ squares to one. -/
lemma tau_one_mul_self (k : Fin 2) : tau k 1 * tau k 1 = 1 := by
  fin_cases k <;> simp [tau]

/-- The flag signs are multiplicative in the flag value:
$(\tau_k)_{f+f', f+f'} = (\tau_k)_{ff}\,(\tau_k)_{f'f'}$. -/
lemma tau_add (k f f' : Fin 2) : tau k (f + f') = tau k f * tau k f' := by
  fin_cases k <;> fin_cases f <;> fin_cases f' <;> simp [tau]

/-- The bond matrix entry as a sign expansion:
$C_k[p,q] = \tfrac12\bigl(x + (-1)^{k + p + q} y\bigr)$, which is the entry of
$x P_+ + (-1)^k y P_-$. -/
lemma Cmat_eq_signs (k p q : Fin 2) :
    Cmat k p q = (x + tau k 1 * tau p 1 * tau q 1 * y) / 2 := by
  fin_cases k <;> fin_cases p <;> fin_cases q <;> norm_num [Cmat, cDiag, cOff, tau, x, y]

/-- The bond matrix $C_k$ as a complex two-by-two matrix. -/
def Cc (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun p q => ((Cmat k p q : ℝ) : ℂ)

/-- The entries of an ordered product of bond matrices: the product
$C_{k_1} \cdots C_{k_L}$ is $x^L P_+ + (-1)^{\sum k_n} y^L P_-$. -/
lemma ofFn_Cc_prod_apply :
    ∀ (L : ℕ) (k : Fin L → Fin 2) (p q : Fin 2),
      (List.ofFn fun n => Cc (k n)).prod p q =
        ((x : ℂ) ^ L +
          ((tau p 1 : ℝ) : ℂ) * ((tau q 1 : ℝ) : ℂ) * (∏ n, ((tau (k n) 1 : ℝ) : ℂ)) *
            (y : ℂ) ^ L) / 2
  | 0, k, p, q => by
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty,
        pow_zero, mul_one]
      fin_cases p <;> fin_cases q <;> norm_num [tau, Matrix.one_apply]
  | L + 1, k, p, q => by
      simp only [List.ofFn_succ, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two]
      rw [ofFn_Cc_prod_apply L, ofFn_Cc_prod_apply L, Fin.prod_univ_succ]
      simp only [Cc, Matrix.of_apply, Cmat_eq_signs]
      have h0 : tau 0 1 = 1 := by simp [tau]
      have h1 : tau 1 1 = -1 := by simp [tau]
      rw [h0, h1]
      push_cast
      ring

/-- The trace of an ordered product of bond matrices is
$x^L + (-1)^{\sum k_n} y^L$. -/
lemma trace_ofFn_Cc_prod (L : ℕ) (k : Fin L → Fin 2) :
    (List.ofFn fun n => Cc (k n)).prod.trace =
      (x : ℂ) ^ L + (∏ n, ((tau (k n) 1 : ℝ) : ℂ)) * (y : ℂ) ^ L := by
  rw [Matrix.trace, Fin.sum_univ_two]
  simp only [Matrix.diag_apply, ofFn_Cc_prod_apply]
  norm_num [tau]

/-- **The cyclic transfer sum.**  Summing the product of the bond-matrix
entries $C_{k_n}[t_n, t_{n+1}]$ around a ring of positive length over all
bit strings $t$ gives $x^L + (-1)^{\sum k_n} y^L$.

Project example; not from CPSV16. -/
theorem sum_cyclic_Cmat (L : ℕ) (k : Fin (L + 1) → Fin 2) :
    (∑ t : Fin (L + 1) → Fin 2,
        ∏ n, ((Cmat (k n) (t n) (t (finRotate (L + 1) n)) : ℝ) : ℂ)) =
      (x : ℂ) ^ (L + 1) + (∏ n, ((tau (k n) 1 : ℝ) : ℂ)) * (y : ℂ) ^ (L + 1) := by
  rw [← trace_ofFn_Cc_prod, Matrix.trace_ofFn_prod_eq_sum_cyclic]
  rfl

/-! ### The middle sum over a flag sector -/

/-- The product of the one-site weights along the word of bond indices
$(t_n, t_{n+1}, k_n)$ factors as $(2\mu)^{-L}$ times the flag signs times the
cyclic product of bond-matrix entries. -/
lemma prod_flagWeight_physIdx (f : Fin 2) {L : ℕ} (k t : Fin L → Fin 2) :
    (∏ n, flagWeight f (physIdx (t n) (t (finRotate L n)) (k n))) =
      (1 / (2 * (mu : ℂ))) ^ L * (∏ n, ((tau (k n) f : ℝ) : ℂ)) *
        ∏ n, ((Cmat (k n) (t n) (t (finRotate L n)) : ℝ) : ℂ) := by
  calc (∏ n, flagWeight f (physIdx (t n) (t (finRotate L n)) (k n)))
      = ∏ n, ((1 / (2 * (mu : ℂ))) * ((tau (k n) f : ℝ) : ℂ) *
          ((Cmat (k n) (t n) (t (finRotate L n)) : ℝ) : ℂ)) := by
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [flagWeight_physIdx]
        push_cast
        ring
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- **The middle sum over a flag sector.**  Summing the product of the one-site
weights over the cyclically bond-matched words with a prescribed string of
block labels is summing over the bit strings $t$ of their left bits, because
such a word is $(t_n, t_{n+1}, k_n)$.

Project example; not from CPSV16. -/
lemma sum_sector (f : Fin 2) (L : ℕ) (k : Fin L → Fin 2) :
    (∑ ρ : Fin L → Fin 8,
        if IsCyclicBondMatched L ρ ∧ ∀ n, k n = bitF (ρ n) then ∏ n, flagWeight f (ρ n) else 0) =
      ∑ t : Fin L → Fin 2, ∏ n, flagWeight f (physIdx (t n) (t (finRotate L n)) (k n)) := by
  set φ : (Fin L → Fin 2) → (Fin L → Fin 8) :=
    fun t n => physIdx (t n) (t (finRotate L n)) (k n) with hφ
  have hinj : Function.Injective φ := by
    intro t t' h
    funext n
    have := congrArg (fun ρ => bitL (ρ n)) h
    simpa [hφ] using this
  have hcond : ∀ t, IsCyclicBondMatched L (φ t) ∧ ∀ n, k n = bitF (φ t n) := by
    intro t
    exact ⟨fun n => by simp [hφ, IsBondMatchedPair], fun n => by simp [hφ]⟩
  symm
  calc (∑ t : Fin L → Fin 2, ∏ n, flagWeight f (φ t n))
      = ∑ t : Fin L → Fin 2,
          (if IsCyclicBondMatched L (φ t) ∧ ∀ n, k n = bitF (φ t n) then
            ∏ n, flagWeight f (φ t n) else 0) :=
        Finset.sum_congr rfl fun t _ => by rw [ite_eq_left (hcond t)]
    _ = ∑ ρ ∈ Finset.univ.image φ,
          (if IsCyclicBondMatched L ρ ∧ ∀ n, k n = bitF (ρ n) then
            ∏ n, flagWeight f (ρ n) else 0) :=
        by rw [Finset.sum_image fun t _ t' _ h => hinj h]
    _ = _ := by
        refine Finset.sum_subset (Finset.subset_univ _) fun ρ _ hρ => ?_
        rw [ite_eq_right]
        intro hc
        apply hρ
        rw [Finset.mem_image]
        refine ⟨fun n => bitL (ρ n), Finset.mem_univ _, funext fun n => ?_⟩
        change physIdx (bitL (ρ n)) (bitL (ρ (finRotate L n))) (k n) = ρ n
        rw [← hc.1 n, hc.2 n]
        exact physIdx_bits _

/-! ### The product law -/

/-- The one-site weight of the sector $f + f'$ is the weight of the sector $f$
times the flag sign of $f'$. -/
lemma flagWeight_add (f f' : Fin 2) (a : Fin 8) :
    flagWeight (f + f') a = flagWeight f a * ((tau (bitF a) f' : ℝ) : ℂ) := by
  simp only [flagWeight, tau_add]
  push_cast
  ring

/-- The weight $x / (2\mu) = 7/10$ is the first two-label fusion weight. -/
lemma alpha_eq_x_div : (1 / (2 * (mu : ℂ))) * (x : ℂ) = (alpha : ℂ) := by
  norm_num [mu, x, alpha]

/-- The weight $y / (2\mu) = 1/10$ is the second two-label fusion weight. -/
lemma beta_eq_y_div : (1 / (2 * (mu : ℂ))) * (y : ℂ) = (beta : ℂ) := by
  norm_num [mu, y, beta]

/-- **The same-length product law of the flag sectors.**  For every positive
length `L` and all flag values `f`, `f'`,
$$
  O_L(\widehat M_f)\,O_L(\widehat M_{f'})
    = \alpha^L\,O_L(\widehat M_{f+f'}) + \beta^L\,O_L(\widehat M_{f+f'+1}),
$$
with $\alpha = 7/10$ and $\beta = 1/10$.  This is the same-length product law
of arXiv:1606.00608, Theorem 4.14(ii), lines 972--985, for the flag-sector
operators of the displayed tensor; it is not asserted that the sectors form the
canonical basis of normal tensors of the tensor.

Project example; not from CPSV16. -/
theorem mpo_flagMPO_mul {L : ℕ} (hL : 0 < L) (f f' : Fin 2) :
    mpo (flagMPO f) L * mpo (flagMPO f') L =
      (alpha : ℂ) ^ L • mpo (flagMPO (f + f')) L +
        (beta : ℂ) ^ L • mpo (flagMPO (f + f' + 1)) L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  ext σ τ
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, mpo_flagMPO_apply _ hL,
    smul_eq_mul]
  by_cases h : IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) τ ∧
      ∀ m, bitF (σ m) = bitF (τ m)
  · rw [ite_eq_left h, ite_eq_left h]
    have hsum : (∑ ρ : Fin (n + 1) → Fin 8,
        (if IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) ρ ∧
            ∀ m, bitF (σ m) = bitF (ρ m) then ∏ m, flagWeight f (σ m) else 0) *
        (if IsCyclicBondMatched (n + 1) ρ ∧ IsCyclicBondMatched (n + 1) τ ∧
            ∀ m, bitF (ρ m) = bitF (τ m) then ∏ m, flagWeight f' (ρ m) else 0)) =
        (∏ m, flagWeight f (σ m)) *
          ∑ ρ : Fin (n + 1) → Fin 8,
            (if IsCyclicBondMatched (n + 1) ρ ∧ ∀ m, bitF (σ m) = bitF (ρ m) then
              ∏ m, flagWeight f' (ρ m) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      by_cases hρ : IsCyclicBondMatched (n + 1) ρ ∧ ∀ m, bitF (σ m) = bitF (ρ m)
      · rw [ite_eq_left ⟨h.1, hρ.1, hρ.2⟩,
          ite_eq_left ⟨hρ.1, h.2.1, fun m => (hρ.2 m).symm.trans (h.2.2 m)⟩, ite_eq_left hρ]
      · rw [ite_eq_right (fun hh => hρ ⟨hh.2.1, hh.2.2⟩), zero_mul, ite_eq_right hρ, mul_zero]
    rw [hsum, sum_sector f' (n + 1) (fun m => bitF (σ m))]
    simp only [prod_flagWeight_physIdx]
    rw [← Finset.mul_sum, sum_cyclic_Cmat]
    simp only [flagWeight_add, Finset.prod_mul_distrib]
    rw [← alpha_eq_x_div, ← beta_eq_y_div, mul_pow, mul_pow]
    ring
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero, add_zero]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    by_cases h1 : IsCyclicBondMatched (n + 1) σ ∧ IsCyclicBondMatched (n + 1) ρ ∧
        ∀ m, bitF (σ m) = bitF (ρ m)
    · rw [ite_eq_left h1,
        ite_eq_right (fun h2 => h ⟨h1.1, h2.2.1, fun m => (h1.2.2 m).trans (h2.2.2 m)⟩), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- **The two-label coefficients are attached to the flag sectors.**  The
sector operator family $L \mapsto O_L(\widehat M_f)$ satisfies the same-length
product predicate of arXiv:1606.00608, Theorem 4.14(ii), lines 972--985, with
the two-label coefficient family $c^{(L)}_{f f' g} = \alpha^L$ on the channel
$g = f + f'$ and $\beta^L$ on the channel $g = f + f' + 1$.  Together with
`twoLabelCoeffs_rescaling_stable_not_lengthIndependent`, the flag-sector
operators of the displayed tensor carry a length-dependent coefficient family
that no positive rescaling of the two labels makes length independent.  It is
not asserted that the two sectors form the canonical basis of normal tensors of
the tensor.

Project example; not from CPSV16. -/
theorem flagOperatorFamily_hasSameLengthProductForm :
    flagOperatorFamily.HasSameLengthProductForm twoLabelCoeffs := by
  intro L hL f f'
  simp only [flagOperatorFamily_operator, twoLabelCoeffs_coeff, Fin.sum_univ_two]
  rw [mpo_flagMPO_mul hL]
  fin_cases f <;> fin_cases f' <;> simp [IsSameChannel, add_comm]

end MPOTensor.TwistedDimer
