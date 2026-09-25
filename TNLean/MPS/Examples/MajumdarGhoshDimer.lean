/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MajumdarGhosh
import TNLean.MPS.ParentHamiltonian.GroundSpace
import QICLean.Algebra.TraceReindex

/-!
# Majumdar-Ghosh: dimer coverings and the review's tensor

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127),
Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2405: the ground
state of \(H=\sum \mathbf S_i\cdot\mathbf S_{i+1}+\tfrac12\sum\mathbf S_i\cdot\mathbf S_{i+2}\)
is the superposition of the singlet coverings \((1,2),(3,4),\dots\) and
\((2,3),(4,5),\dots,(N,1)\), and "can be written as an MPS with
\(A=[\,|0\rangle[(02|+(20|]+|1\rangle[(12|+(21|]\,]\otimes Y\)", with \(Y\) the
singlet matrix of lines 2380–2383.
Review: arXiv:2011.12127, Appendix A, "The Majumdar-Ghosh model".

**Formalized here.**
* The periodic vector of the bond-dimension-three tensor
  `majumdarGhoshTensor` is, on every even ring, the sum of the two
  nearest-neighbour singlet coverings, each singlet normalized; on odd rings it
  vanishes.
* The review's tensor, read literally with \((ab|\) the bra of the pair of
  virtual indices and \(\otimes Y\) a Kronecker factor, has bond dimension six.
  Its periodic vector on a ring of \(N=2m\) sites is \(2(-1)^m\) times the sum
  of the two coverings by the symmetric pair state \(|00\rangle+|11\rangle\),
  and is not a multiple of the Majumdar-Ghosh vector.
* Read instead as the three-level bond matrices followed by the bond state
  \(Y\oplus1\) (the singlet on the two spin levels, the empty level carried
  through), the same formula gives exactly the sum of the two coverings by
  unnormalized singlets.

**Local fix (Majumdar-Ghosh tensor):** the literal Kronecker reading of the
review's formula does not produce the Majumdar-Ghosh state; the three-level bond
with the singlet attached to its two spin levels does. Documented in
`docs/paper-gaps/rmp_majumdar_ghosh_tensor_gap.tex`.

## Main definitions
* `MPSTensor.pairProduct` : the product of a pair function over consecutive
  disjoint pairs of a word
* `MPSTensor.pairCoveringEven`, `MPSTensor.pairCoveringOdd` : the two
  nearest-neighbour pair coverings of a periodic chain
* `MPSTensor.majumdarGhoshSingletY` : the review's singlet matrix \(Y\)
* `MPSTensor.majumdarGhoshReviewTensor` : the review's tensor, bond dimension six
* `MPSTensor.majumdarGhoshBondSingletTensor` : the three-level bond matrices
  followed by the bond state \(Y\oplus1\)

## Main results
* `MPSTensor.majumdarGhosh_mpv_eq_pairCovering` : the periodic vector of the
  bond-dimension-three tensor is the sum of the two singlet coverings
* `MPSTensor.majumdarGhoshReview_mpv_eq` : the periodic vector of the review's
  literal tensor
* `MPSTensor.majumdarGhoshReview_mpv_ne_smul` : it is not a multiple of the
  Majumdar-Ghosh vector
* `MPSTensor.majumdarGhoshBondSinglet_mpv_eq_pairCovering` : the singlet-bond
  reading gives the sum of the two unnormalized singlet coverings

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators Kronecker
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### Pair products and pair coverings -/

/-- The product of `f` over the consecutive disjoint pairs of a word:
`pairProduct f [a₁, b₁, a₂, b₂, …] = f a₁ b₁ * f a₂ b₂ * ⋯`, and `0` on words of
odd length. -/
def pairProduct {α : Type*} (f : α → α → ℂ) : List α → ℂ
  | [] => 1
  | [_] => 0
  | a :: b :: t => f a b * pairProduct f t

@[simp] lemma pairProduct_nil {α : Type*} (f : α → α → ℂ) : pairProduct f [] = 1 := rfl

@[simp] lemma pairProduct_singleton {α : Type*} (f : α → α → ℂ) (a : α) :
    pairProduct f [a] = 0 := rfl

@[simp] lemma pairProduct_cons_cons {α : Type*} (f : α → α → ℂ) (a b : α) (t : List α) :
    pairProduct f (a :: b :: t) = f a b * pairProduct f t := rfl

/-- On a word of length `2 m` the pair product is the product over the `m`
consecutive pairs. -/
theorem pairProduct_eq_prod {α : Type*} (f : α → α → ℂ) :
    ∀ (m : ℕ) (l : List α) (hl : l.length = 2 * m),
      pairProduct f l =
        ∏ k : Fin m, f (l[2 * k.1]'(by omega)) (l[2 * k.1 + 1]'(by omega))
  | 0, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | m + 1, [], h => by simp at h
  | m + 1, [_], h => by simp at h; omega
  | m + 1, a :: b :: t, h => by
      have ht : t.length = 2 * m := by simp at h; omega
      rw [pairProduct_cons_cons, pairProduct_eq_prod f m t ht, Fin.prod_univ_succ]
      congr 1

/-- A word of odd length has pair product zero. -/
theorem pairProduct_eq_zero_of_odd {α : Type*} (f : α → α → ℂ) :
    ∀ l : List α, Odd l.length → pairProduct f l = 0
  | [], h => by simp at h
  | [_], _ => rfl
  | _ :: _ :: t, h => by
      rw [pairProduct_cons_cons, pairProduct_eq_zero_of_odd f t (by
        simpa [Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_add_one] using h), mul_zero]

/-- The pair covering \((1,2)(3,4)\cdots(N-1,N)\) of a periodic chain of `N`
sites with pair amplitude `f`, written with sites `0, …, N-1`: the coefficient of
the basis vector `σ` is \(\prod_k f(\sigma_{2k},\sigma_{2k+1})\). It is a
covering of the chain when `N` is even. -/
def pairCoveringEven {d : ℕ} (f : Fin d → Fin d → ℂ) {N : ℕ} :
    NSiteSpace d N := fun σ =>
  ∏ k : Fin (N / 2),
    f (σ ⟨2 * k.1, by have := k.isLt; omega⟩) (σ ⟨2 * k.1 + 1, by have := k.isLt; omega⟩)

/-- The pair covering \((2,3)(4,5)\cdots(N,1)\) of a periodic chain of `N`
sites with pair amplitude `f`, written with sites `0, …, N-1`: the coefficient of
`σ` is \(\prod_k f(\sigma_{2k+1},\sigma_{(2k+2)\bmod N})\). -/
def pairCoveringOdd {d : ℕ} (f : Fin d → Fin d → ℂ) {N : ℕ} :
    NSiteSpace d N := fun σ =>
  ∏ k : Fin (N / 2),
    f (σ ⟨(2 * k.1 + 1) % N, Nat.mod_lt _ (by have := k.isLt; omega)⟩)
      (σ ⟨(2 * k.1 + 2) % N, Nat.mod_lt _ (by have := k.isLt; omega)⟩)

/-- The pair product of a configuration is its even pair covering. -/
theorem pairProduct_ofFn_eq_pairCoveringEven {d : ℕ} (f : Fin d → Fin d → ℂ)
    {N : ℕ} (hN : Even N) (σ : Fin N → Fin d) :
    pairProduct f (List.ofFn σ) = pairCoveringEven f σ := by
  obtain ⟨n, hn⟩ := hN
  rw [pairProduct_eq_prod f (N / 2) _ (by simp; omega)]
  simp [pairCoveringEven]

/-- The pair product of a configuration rotated by one site is its odd pair
covering. -/
theorem pairProduct_rotate_ofFn_eq_pairCoveringOdd {d : ℕ} (f : Fin d → Fin d → ℂ)
    {N : ℕ} (hN : Even N) (σ : Fin N → Fin d) :
    pairProduct f ((List.ofFn σ).rotate 1) = pairCoveringOdd f σ := by
  obtain ⟨n, hn⟩ := hN
  rw [pairProduct_eq_prod f (N / 2) _ (by simp; omega)]
  simp only [pairCoveringOdd, List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]

/-! ### Tensors with a hub bond level

A tensor has a *hub* level `z` when no letter connects two non-hub levels and no
letter maps the hub to itself. Its closed words then alternate between the hub
and the other levels, so its coefficients are sums of two pair products. -/

section Hub

variable {d D : ℕ}

private lemma mul_mul_apply_hub (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0)
    (a b : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) :
    (K a * K b * M) z z = (K a * K b) z z * M z z := by
  rw [Matrix.mul_apply, Finset.sum_eq_single z]
  · intro y _ hy
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro x _
    by_cases hx : x = z
    · subst hx; rw [hhub, zero_mul]
    · rw [hoff b x y hx hy, mul_zero]
  · simp

/-- The hub-to-hub entry of a word evaluation is the pair product of the two-letter
hub amplitudes. -/
theorem evalWord_apply_hub_eq_pairProduct (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0) :
    ∀ w : List (Fin d),
      Kraus.evalWord K w z z = pairProduct (fun a b => (K a * K b) z z) w
  | [] => by simp
  | [a] => by simp [hhub]
  | a :: b :: t => by
      rw [pairProduct_cons_cons, ← evalWord_apply_hub_eq_pairProduct K z hoff hhub t,
        Kraus.evalWord_cons, Kraus.evalWord_cons, ← Matrix.mul_assoc,
        mul_mul_apply_hub K z hoff hhub]

private lemma trace_mul_eq_hub (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0)
    (a : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (K a * M) = (K a * M) z z + (M * K a) z z := by
  have h1 : Matrix.trace (K a * M) =
      (K a * M) z z + ∑ x ∈ univ.erase z, (K a * M) x x := by
    exact (Finset.add_sum_erase _ (fun x => (K a * M) x x) (mem_univ z)).symm
  have h2 : (M * K a) z z = ∑ x ∈ univ.erase z, (K a * M) x x := by
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (mem_univ z), hhub, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx : x ≠ z := Finset.ne_of_mem_erase hx
    rw [Matrix.mul_apply, Finset.sum_eq_single z]
    · ring
    · intro y _ hy; rw [hoff a x y hx hy, zero_mul]
    · simp
  rw [h1, h2]

/-- The periodic coefficient of a nonempty word for a tensor with a hub level is
the sum of the pair products of the word and of its rotation by one letter. -/
theorem coeff_cons_eq_pairProduct_add (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0)
    (a : Fin d) (w : List (Fin d)) :
    coeff K (a :: w) =
      pairProduct (fun a b => (K a * K b) z z) (a :: w) +
        pairProduct (fun a b => (K a * K b) z z) (w ++ [a]) := by
  rw [coeff_eq, Kraus.evalWord_cons, trace_mul_eq_hub K z hoff hhub,
    ← evalWord_apply_hub_eq_pairProduct K z hoff hhub,
    ← evalWord_apply_hub_eq_pairProduct K z hoff hhub, Kraus.evalWord_cons,
    Kraus.evalWord_append]
  simp

/-- On an even periodic chain the periodic vector of a tensor with a hub level is
the sum of the two pair coverings with the two-letter hub amplitudes. -/
theorem mpv_eq_pairCovering_of_hub (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0)
    {N : ℕ} (hN : Even N) (hNpos : 0 < N) (σ : Fin N → Fin d) :
    mpv K σ =
      pairCoveringEven (fun a b => (K a * K b) z z) σ +
        pairCoveringOdd (fun a b => (K a * K b) z z) σ := by
  rw [← pairProduct_ofFn_eq_pairCoveringEven _ hN,
    ← pairProduct_rotate_ofFn_eq_pairCoveringOdd _ hN, mpv_eq]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [List.ofFn_succ, coeff_cons_eq_pairProduct_add K z hoff hhub]
  simp

/-- On an odd periodic chain the periodic vector of a tensor with a hub level
vanishes. -/
theorem mpv_eq_zero_of_hub_of_odd (K : MPSTensor d D) (z : Fin D)
    (hoff : ∀ a x y, x ≠ z → y ≠ z → K a x y = 0) (hhub : ∀ a, K a z z = 0)
    {N : ℕ} (hN : Odd N) (σ : Fin N → Fin d) :
    mpv K σ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by obtain ⟨k, hk⟩ := hN; omega⟩
  rw [mpv_eq, List.ofFn_succ, coeff_cons_eq_pairProduct_add K z hoff hhub,
    pairProduct_eq_zero_of_odd _ _ (by simpa using hN),
    pairProduct_eq_zero_of_odd _ _ (by simpa using hN), add_zero]

end Hub

/-! ### The singlet matrix -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2380–2383. The singlet matrix \(Y=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\);
its entry \(Y_{ab}\) is the coefficient of \(|ab\rangle\) in the singlet
\(|10\rangle-|01\rangle\). -/
def majumdarGhoshSingletY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

lemma majumdarGhoshSingletY_sq : majumdarGhoshSingletY ^ 2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [majumdarGhoshSingletY, sq]

/-- Even powers of the singlet matrix. -/
lemma majumdarGhoshSingletY_pow_two_mul (m : ℕ) :
    majumdarGhoshSingletY ^ (2 * m) = (-1 : ℂ) ^ m • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pow_mul, majumdarGhoshSingletY_sq,
    show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1 by simp, smul_pow, one_pow]

/-- The normalized singlet amplitude \(Y_{ab}/\sqrt2\): the coefficient of
\(|ab\rangle\) in \((|10\rangle-|01\rangle)/\sqrt2\). -/
def majumdarGhoshSinglet (a b : Fin 2) : ℂ :=
  Complex.invSqrtTwo * majumdarGhoshSingletY a b

/-! ### The bond-dimension-three tensor -/

/-- Project result: the two-letter hub amplitude of `majumdarGhoshTensor` is the
normalized singlet, \((A^aA^b)_{00}=Y_{ab}/\sqrt2\). -/
lemma majumdarGhoshTensor_mul_apply_zero_zero (a b : Fin 2) :
    (majumdarGhoshTensor a * majumdarGhoshTensor b) 0 0 = majumdarGhoshSinglet a b := by
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshTensor, majumdarGhoshSinglet, majumdarGhoshSingletY, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- No matrix of `majumdarGhoshTensor` connects two of the levels `1, 2`. -/
lemma majumdarGhoshTensor_apply_eq_zero_of_ne_zero (a : Fin 2) (x y : Fin 3) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    majumdarGhoshTensor a x y = 0 := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;> simp_all [majumdarGhoshTensor]

/-- No matrix of `majumdarGhoshTensor` maps the level `0` to itself. -/
lemma majumdarGhoshTensor_apply_zero_zero (a : Fin 2) : majumdarGhoshTensor a 0 0 = 0 := by
  fin_cases a <;> simp [majumdarGhoshTensor]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2399–2401 (the ground state is the superposition of the singlet coverings
\((1,2),(3,4),\dots\) and \((2,3),(4,5),\dots,(N,1)\)), for the
bond-dimension-three representative. On a periodic chain of even length
\(N>0\), the periodic vector of `majumdarGhoshTensor` is the sum of the two
nearest-neighbour coverings by the normalized singlet
\((|10\rangle-|01\rangle)/\sqrt2\). -/
theorem majumdarGhosh_mpv_eq_pairCovering {N : ℕ} (hN : Even N) (hNpos : 0 < N)
    (σ : Fin N → Fin 2) :
    mpv majumdarGhoshTensor σ =
      pairCoveringEven majumdarGhoshSinglet σ + pairCoveringOdd majumdarGhoshSinglet σ := by
  rw [mpv_eq_pairCovering_of_hub majumdarGhoshTensor 0 majumdarGhoshTensor_apply_eq_zero_of_ne_zero
    majumdarGhoshTensor_apply_zero_zero hN hNpos]
  simp only [majumdarGhoshTensor_mul_apply_zero_zero]

/-- Project result: the periodic vector of `majumdarGhoshTensor` vanishes on odd
rings. -/
theorem majumdarGhosh_mpv_eq_zero_of_odd {N : ℕ} (hN : Odd N) (σ : Fin N → Fin 2) :
    mpv majumdarGhoshTensor σ = 0 :=
  mpv_eq_zero_of_hub_of_odd majumdarGhoshTensor 0 majumdarGhoshTensor_apply_eq_zero_of_ne_zero
    majumdarGhoshTensor_apply_zero_zero hN σ

/-! ### The review's tensor, read literally -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2401–2403. The three-level bond matrices of the review's formula,
\(B^0=(02|+(20|\) and \(B^1=(12|+(21|\), with \((ab|\) the bra of the pair of
virtual indices, that is, the matrix unit with row `a` and column `b`. -/
def majumdarGhoshReviewBond : MPSTensor 2 3 := fun i =>
  match i with
  | 0 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 1 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2401–2403. The review's Majumdar-Ghosh tensor
\(A=[\,|0\rangle[(02|+(20|]+|1\rangle[(12|+(21|]\,]\otimes Y\), read literally:
\(A^i=B^i\otimes Y\) on the six-dimensional bond \(\mathbb C^3\otimes\mathbb C^2\),
identified with `Fin 6` by `finProdFinEquiv`. -/
def majumdarGhoshReviewTensor : MPSTensor 2 6 := fun i =>
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (majumdarGhoshReviewBond i ⊗ₖ majumdarGhoshSingletY)

private lemma majumdarGhoshReviewTensor_evalWord :
    ∀ w : List (Fin 2),
      Kraus.evalWord majumdarGhoshReviewTensor w =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Kraus.evalWord majumdarGhoshReviewBond w ⊗ₖ (majumdarGhoshSingletY ^ w.length))
  | [] => by simp
  | i :: w => by
      rw [Kraus.evalWord_cons, majumdarGhoshReviewTensor_evalWord w, majumdarGhoshReviewTensor,
        Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Kraus.evalWord_cons,
        List.length_cons, pow_succ']

/-- Bridge: each coefficient of the review's literal tensor factors as the
coefficient of the three-level bond matrices times the trace of a power of
\(Y\). -/
theorem majumdarGhoshReview_coeff (w : List (Fin 2)) :
    coeff majumdarGhoshReviewTensor w =
      coeff majumdarGhoshReviewBond w * Matrix.trace (majumdarGhoshSingletY ^ w.length) := by
  rw [coeff_eq, majumdarGhoshReviewTensor_evalWord, Matrix.trace_reindex,
    Matrix.trace_kronecker, coeff_eq]

private lemma majumdarGhoshReviewBond_hoff (a : Fin 2) (x y : Fin 3) (hx : x ≠ 2) (hy : y ≠ 2) :
    majumdarGhoshReviewBond a x y = 0 := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;> simp_all [majumdarGhoshReviewBond]

private lemma majumdarGhoshReviewBond_hhub (a : Fin 2) : majumdarGhoshReviewBond a 2 2 = 0 := by
  fin_cases a <;> simp [majumdarGhoshReviewBond]

/-- The two-letter hub amplitude of the three-level bond matrices is the
Kronecker delta: the pair state is \(|00\rangle+|11\rangle\), not the singlet. -/
lemma majumdarGhoshReviewBond_mul_apply_two_two (a b : Fin 2) :
    (majumdarGhoshReviewBond a * majumdarGhoshReviewBond b) 2 2 = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshReviewBond, Matrix.mul_apply, Fin.sum_univ_three]

/-- Project result, refuting the literal reading of the review: on a periodic
chain of \(N=2m>0\) sites the review's tensor (defined from
arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2401–2403) has
periodic vector \(2(-1)^m\) times the sum of the two nearest-neighbour coverings
by the pair state \(|00\rangle+|11\rangle\), not the singlet superposition the
review claims. -/
theorem majumdarGhoshReview_mpv_eq {m : ℕ} (hm : 0 < m) (σ : Fin (2 * m) → Fin 2) :
    mpv majumdarGhoshReviewTensor σ =
      2 * (-1 : ℂ) ^ m *
        (pairCoveringEven (fun a b => if a = b then 1 else 0) σ +
          pairCoveringOdd (fun a b => if a = b then 1 else 0) σ) := by
  have hbond := mpv_eq_pairCovering_of_hub majumdarGhoshReviewBond 2
    majumdarGhoshReviewBond_hoff majumdarGhoshReviewBond_hhub (N := 2 * m)
    (even_two_mul m) (by omega) σ
  simp only [majumdarGhoshReviewBond_mul_apply_two_two] at hbond
  rw [mpv_eq, majumdarGhoshReview_coeff, ← mpv_eq, hbond, List.length_ofFn,
    majumdarGhoshSingletY_pow_two_mul, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- Project result: the review's literal tensor does not represent the
Majumdar-Ghosh state. On every even ring its periodic vector is not a scalar
multiple of the periodic vector of `majumdarGhoshTensor`: on the configuration
with all spins `0` the former is \(\pm4\) and the latter vanishes. -/
theorem majumdarGhoshReview_mpv_ne_smul {m : ℕ} (hm : 0 < m) (c : ℂ) :
    (mpv majumdarGhoshReviewTensor : NSiteSpace 2 (2 * m)) ≠
      c • (mpv majumdarGhoshTensor : NSiteSpace 2 (2 * m)) := by
  intro h
  have h0 := congrFun h (fun _ => 0)
  have hk : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hk
  rw [Pi.smul_apply, smul_eq_mul,
    majumdarGhosh_mpv_eq_pairCovering (even_two_mul _) (by omega),
    majumdarGhoshReview_mpv_eq hm] at h0
  have hdiv : 2 * (k + 1) / 2 = k + 1 := by omega
  simp [pairCoveringEven, pairCoveringOdd, majumdarGhoshSinglet, majumdarGhoshSingletY,
    hdiv] at h0

/-! ### The singlet-bond reading -/

/-- Project result: the three-level bond matrices of the review followed by the
bond state \(Y\oplus1\), which places the singlet on the two spin levels `0, 1`
and carries the empty level `2` through: \(C^i=B^i(Y\oplus1)\). -/
def majumdarGhoshBondSingletTensor : MPSTensor 2 3 := fun i =>
  majumdarGhoshReviewBond i * !![0, -1, 0; 1, 0, 0; 0, 0, 1]

private lemma majumdarGhoshBondSinglet_hoff (a : Fin 2) (x y : Fin 3) (hx : x ≠ 2) (hy : y ≠ 2) :
    majumdarGhoshBondSingletTensor a x y = 0 := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;>
    simp_all [majumdarGhoshBondSingletTensor, majumdarGhoshReviewBond, Matrix.mul_apply,
      Fin.sum_univ_three]

private lemma majumdarGhoshBondSinglet_hhub (a : Fin 2) :
    majumdarGhoshBondSingletTensor a 2 2 = 0 := by
  fin_cases a <;>
    simp [majumdarGhoshBondSingletTensor, majumdarGhoshReviewBond, Matrix.mul_apply,
      Fin.sum_univ_three]

private lemma majumdarGhoshBondSinglet_mul_apply_two_two (a b : Fin 2) :
    (majumdarGhoshBondSingletTensor a * majumdarGhoshBondSingletTensor b) 2 2 =
      majumdarGhoshSingletY a b := by
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshBondSingletTensor, majumdarGhoshReviewBond, majumdarGhoshSingletY,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- Project result: on a periodic chain of even length \(N>0\), the singlet-bond
reading of the review's formula has periodic vector equal to the sum of the two
nearest-neighbour coverings by the unnormalized singlet \(|10\rangle-|01\rangle\),
the superposition of arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2399–2401. -/
theorem majumdarGhoshBondSinglet_mpv_eq_pairCovering {N : ℕ} (hN : Even N) (hNpos : 0 < N)
    (σ : Fin N → Fin 2) :
    mpv majumdarGhoshBondSingletTensor σ =
      pairCoveringEven (fun a b => majumdarGhoshSingletY a b) σ +
        pairCoveringOdd (fun a b => majumdarGhoshSingletY a b) σ := by
  rw [mpv_eq_pairCovering_of_hub majumdarGhoshBondSingletTensor 2 majumdarGhoshBondSinglet_hoff
    majumdarGhoshBondSinglet_hhub hN hNpos]
  simp only [majumdarGhoshBondSinglet_mul_apply_two_two]

/-- Bridge: on an even ring of \(N>0\) sites, the periodic vector of the
singlet-bond reading is \(\sqrt2^{\,N/2}\) times that of `majumdarGhoshTensor`. -/
theorem majumdarGhoshBondSinglet_mpv_eq_smul {N : ℕ} (hN : Even N) (hNpos : 0 < N)
    (σ : Fin N → Fin 2) :
    mpv majumdarGhoshBondSingletTensor σ =
      (↑(Real.sqrt 2) : ℂ) ^ (N / 2) * mpv majumdarGhoshTensor σ := by
  rw [majumdarGhoshBondSinglet_mpv_eq_pairCovering hN hNpos,
    majumdarGhosh_mpv_eq_pairCovering hN hNpos]
  simp only [pairCoveringEven, pairCoveringOdd, majumdarGhoshSinglet, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_pow, Complex.sqrtTwo_mul_invSqrtTwo, one_pow,
    one_mul, one_mul]

end MPSTensor

end
