/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciAnomaly

/-!
# Fibonacci: the nonnegative integer representations of rank at most two

**Source.** Garre-Rubio, Lootens and Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1991–1993: for a matrix product operator representing
the Fibonacci fusion category `{1, τ; τ × τ = 1 + τ}`, "the only solution for an invariant MPS
subspace is characterized by two blocks `{x_1, x_τ}`" with `τ · x_1 = x_τ` and
`τ · x_τ = x_1 + x_τ`. The multiplicities of the blocks form a nonnegative integer
representation of the fusion ring (lines 564–565).

**Formalized here.** The nonnegative integer representations of the Fibonacci ring on which the
unit acts as the identity, on one or two blocks: there is none on one block, and on two blocks
the representation is the regular one, `M_a = N_a` after labelling the blocks by `1` and `τ`.
Together with the integrality theorem `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily`, a
symmetric family of at most two normal blocks with the unit acting trivially has exactly two
blocks, transforming as in line 1993.

**Scope restriction (at most two blocks):** the source's uniqueness claim covers invariant
subspaces with any number of blocks; only one and two blocks are classified here. Documented in
`docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`.

## Main results

* `FibonacciCompression.fibNim_entries_of_sq`: the `2 × 2` nonnegative integer solutions of
  `m² = 1 + m`.
* `FibonacciCompression.not_isNIMRep_fibNim_of_card_eq_one`: no representation on one block.
* `FibonacciCompression.exists_equiv_of_isNIMRep_fibNim_of_card_eq_two`: on two blocks, the
  regular representation up to relabelling.
* `FibonacciCompression.exists_equiv_of_isMPOSymmetricFamily_fibBlock`: a symmetric family of
  at most two normal blocks with the unit acting trivially has two blocks transforming as the
  regular representation.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open MPSTensor MPOTensor

namespace FibonacciCompression

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The representation identity at `a = b = τ` with the unit acting trivially:
`δ_{xy} + M_{τ,x}^y = ∑_z M_{τ,x}^z M_{τ,z}^y`, since `τ × τ = 1 + τ`. -/
theorem IsNIMRep.fibNim_tau_sq {M : Fin 2 → κ → κ → ℕ} (hM : IsNIMRep fibNim M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (x y : κ) :
    (if x = y then 1 else 0) + M 1 x y = ∑ z, M 1 x z * M 1 z y := by
  have h := hM 1 1 x y
  simpa [fibNim, fibFusionMatrix, Fin.sum_univ_two, hunit] using h

/-- **The `2 × 2` nonnegative integer solutions of `m² = 1 + m`.** If natural numbers
`a, b, c, d` satisfy the entrywise equations of `[[a, b], [c, d]]² = 1 + [[a, b], [c, d]]`, then
the matrix is `[[0, 1], [1, 1]]` or `[[1, 1], [1, 0]]`. -/
theorem fibNim_entries_of_sq {a b c d : ℕ} (h11 : 1 + a = a * a + b * c)
    (h12 : b = a * b + b * d) (h21 : c = c * a + d * c) (h22 : 1 + d = c * b + d * d) :
    (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by
  have ha : a ≤ 1 := by nlinarith
  have haa : a * a = a := by interval_cases a <;> rfl
  have hbc : b * c = 1 := by linarith
  obtain rfl := Nat.eq_one_of_mul_eq_one_right hbc
  obtain rfl := Nat.eq_one_of_mul_eq_one_left hbc
  omega

/-- **No representation on one block** (arXiv:2203.12563, line 1993): a nonnegative integer
representation of the Fibonacci ring on one block with the unit acting trivially would give
`m² = 1 + m` in `ℕ`. -/
theorem not_isNIMRep_fibNim_of_card_eq_one (hκ : Fintype.card κ = 1)
    {M : Fin 2 → κ → κ → ℕ} (hM : IsNIMRep fibNim M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) : False := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hκ
  have h := IsNIMRep.fibNim_tau_sq hM hunit x x
  rw [Fintype.sum_eq_single x fun z hz => absurd (hx z) hz] at h
  simp only [↓reduceIte] at h
  exact Nat.mul_self_ne_add_one (M 1 x x) (by omega)

/-- **On two blocks the representation is the regular one** (arXiv:2203.12563, line 1993): a
nonnegative integer representation of the Fibonacci ring on two blocks with the unit acting
trivially is `M_a = N_a` after labelling the blocks by `1` and `τ`, that is `τ · x_1 = x_τ` and
`τ · x_τ = x_1 + x_τ`. -/
theorem exists_equiv_of_isNIMRep_fibNim_of_card_eq_two (hκ : Fintype.card κ = 2)
    {M : Fin 2 → κ → κ → ℕ} (hM : IsNIMRep fibNim M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) :
    ∃ σ : κ ≃ Fin 2, ∀ a x y, M a x y = fibNim a (σ x) (σ y) := by
  set τ₀ := (Fintype.equivFinOfCardEq hκ).symm
  have hsq : ∀ i j : Fin 2, (if i = j then 1 else 0) + M 1 (τ₀ i) (τ₀ j) =
      ∑ k : Fin 2, M 1 (τ₀ i) (τ₀ k) * M 1 (τ₀ k) (τ₀ j) := by
    intro i j
    have h := IsNIMRep.fibNim_tau_sq hM hunit (τ₀ i) (τ₀ j)
    rw [← Equiv.sum_comp τ₀] at h
    simpa [τ₀.injective.eq_iff] using h
  have h11 := hsq 0 0
  have h12 := hsq 0 1
  have h21 := hsq 1 0
  have h22 := hsq 1 1
  simp only [Fin.sum_univ_two, Fin.isValue, ite_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, ite_false, zero_add] at h11 h12 h21 h22
  -- the entries of `M_τ` in the labelling `τ₀`
  have hent : ∀ σ : Equiv.Perm (Fin 2),
      (∀ i j, M 1 (τ₀ i) (τ₀ j) = fibFusionMatrix (σ i) (σ j)) →
      ∃ σ' : κ ≃ Fin 2, ∀ a x y, M a x y = fibNim a (σ' x) (σ' y) := by
    intro σ hσ
    refine ⟨τ₀.symm.trans σ, fun a x y => ?_⟩
    obtain ⟨i, rfl⟩ := τ₀.surjective x
    obtain ⟨j, rfl⟩ := τ₀.surjective y
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    fin_cases a
    · simp [fibNim, hunit, Matrix.one_apply, τ₀.injective.eq_iff, σ.injective.eq_iff]
    · exact hσ i j
  rcases fibNim_entries_of_sq h11 h12 h21 h22 with
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · refine hent 1 fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [fibFusionMatrix, ha, hb, hc, hd]
  · refine hent (Equiv.swap 0 1) fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [fibFusionMatrix, ha, hb, hc, hd]

/-- **A symmetric family of at most two normal blocks is the regular representation**
(arXiv:2203.12563, lines 1991–1993, for at most two blocks). Let `(A_x)` be normal tensors of
positive bond dimension whose periodic vectors are linearly independent at one positive length,
symmetric under the Fibonacci algebra with the unit acting trivially. If there are at most two
blocks, there are exactly two, and after labelling them by `1` and `τ` the multiplicities are
`M_a = N_a`: `τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ`. -/
theorem exists_equiv_of_isMPOSymmetricFamily_fibBlock [Nonempty κ] {D : κ → ℕ}
    {A : ∀ x, MPSTensor 2 (D x)} {M : Fin 2 → κ → κ → ℂ}
    (hsym : IsMPOSymmetricFamily fibBlock A M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin 2 => mpv (A x) σ)
    (hκ : Fintype.card κ ≤ 2) :
    Fintype.card κ = 2 ∧ ∃ σ : κ ≃ Fin 2, ∀ a x y, M a x y = fibNim a (σ x) (σ y) := by
  obtain ⟨M', hMM', hM'⟩ :=
    exists_isNIMRep_of_isMPOSymmetricFamily isMPOFusionAlgebra_fibBlock hsym hA hD hL₀ hli
  have hunit' : ∀ x y, M' 0 x y = if x = y then 1 else 0 := by
    intro x y
    have h := hunit x y
    rw [hMM'] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hpos : 0 < Fintype.card κ := Fintype.card_pos
  have h2 : Fintype.card κ = 2 := by
    rcases Nat.lt_or_ge (Fintype.card κ) 2 with h | h
    · exact (not_isNIMRep_fibNim_of_card_eq_one (by omega) hM' hunit').elim
    · omega
  obtain ⟨σ, hσ⟩ := exists_equiv_of_isNIMRep_fibNim_of_card_eq_two h2 hM' hunit'
  exact ⟨h2, σ, fun a x y => by rw [hMM', hσ]⟩

end FibonacciCompression
