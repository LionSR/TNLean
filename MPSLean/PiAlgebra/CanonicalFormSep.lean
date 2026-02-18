/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.PiAlgebra.BlockSeparation
import MPSLean.PiAlgebra.BlockSeparationProof
import MPSLean.PiAlgebra.FundamentalTheoremComplete
import MPSLean.Spectral.SpectralGap
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Canonical form predicate -/

structure IsCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  block_injective : ∀ k, IsInjective (A k)
  ds_gauge : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
  mu_ne_zero : ∀ k, μ k ≠ 0

namespace IsCanonicalForm

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

theorem mu_injective (hCF : IsCanonicalForm μ A) : Function.Injective μ := by
  intro j k hjk
  have h : ‖μ j‖ = ‖μ k‖ := by rw [hjk]
  exact hCF.mu_strict_anti.injective h

theorem mu_norm_injective (hCF : IsCanonicalForm μ A) :
    Function.Injective (fun k : Fin r => ‖μ k‖) :=
  hCF.mu_strict_anti.injective

end IsCanonicalForm

/-! ### Auxiliary algebraic lemmas -/

section AlgebraicLemmas

lemma scalar_mul_sub_smul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    Matrix.scalar n (c * z) - c • M = c • (Matrix.scalar n z - M) := by
  ext i j
  simp [Matrix.scalar, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, smul_eq_mul]
  split <;> ring

lemma eval_charpoly_smul_mul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    (c • M).charpoly.eval (c * z) = c ^ Fintype.card n * M.charpoly.eval z := by
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, scalar_mul_sub_smul, Matrix.det_smul]

theorem charpoly_eq_of_smul_charpoly_eq {n : Type*} [DecidableEq n] [Fintype n]
    (c : ℂ) (hc : c ≠ 0) (T U : Matrix n n ℂ)
    (h : (c • T).charpoly = (c • U).charpoly) :
    T.charpoly = U.charpoly := by
  have hcn : c ^ Fintype.card n ≠ 0 := pow_ne_zero _ hc
  apply Polynomial.funext
  intro z
  have h1 := eval_charpoly_smul_mul c z T
  have h2 := eval_charpoly_smul_mul c z U
  have h3 : (c • T).charpoly.eval (c * z) = (c • U).charpoly.eval (c * z) := by rw [h]
  rw [h1] at h3; rw [h2] at h3
  exact mul_left_cancel₀ hcn h3

theorem trace_eq_of_charpoly_eq
    {D : ℕ} [NeZero D]
    (T U : Matrix (Fin D) (Fin D) ℂ)
    (h : T.charpoly = U.charpoly) :
    Matrix.trace T = Matrix.trace U := by
  have : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (NeZero.pos D)
  have hT := Matrix.trace_eq_neg_charpoly_coeff T
  have hU := Matrix.trace_eq_neg_charpoly_coeff U
  rw [hT, hU, h]

end AlgebraicLemmas

/-! ### Block separation core lemma (sorry)

**Mathematical content**: Under canonical form hypotheses (injective blocks in DS gauge,
strict |μ| ordering), the summed identity ∑_k μ_k^N · Δ_k(σ) = 0 for all N and σ
implies per-block MPV equality.

**Proof sketch** (PGVWC 2007, Theorem 3; Cirac et al. 2021, Theorem IV.3):
The argument uses three key ingredients:
1. **Asymptotic dominance**: For repeated words of length ML, the coefficient (μ₀^M)^L
   dominates all other terms (peeling lemma), giving exponential decay of Δ₀.
2. **Transfer operator convergence**: Injectivity + DS gauge normalization implies that
   the transfer operator E_{A_k} has a spectral gap. The iterated transfer converges
   exponentially to the rank-1 projection onto the fixed point.
3. **Cross-block cancellation**: By using the identity for ALL words simultaneously
   (not just repeated words), the injective blocks' tensor algebras span the full
   matrix algebra, providing enough equations to uniquely determine Δ_k = 0.

The combination of these three ingredients shows that the leading block's MPV difference
must vanish, after which the block can be peeled off and the argument repeated
by induction on r. -/

lemma block_separation_core
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hA_ds : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) := by
  -- The proof proceeds by cases on r
  by_cases hr0 : r = 0
  · subst hr0; intro k; exact k.elim0
  · by_cases hr1 : r = 1
    · -- Single block case: from μ₀^N δ₀(σ) = 0 and μ₀ ≠ 0, get δ₀ = 0
      subst hr1; intro k
      have hk : k = 0 := Fin.ext (by omega)
      subst hk
      intro N σ
      have h_eq := h_summed N σ
      simp only [Fin.sum_univ_one] at h_eq
      -- h_eq : (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) = 0
      have hμ_pow : (μ 0) ^ N ≠ 0 := pow_ne_zero N (hμ_ne_zero 0)
      have hsub := (mul_eq_zero.mp h_eq).resolve_left hμ_pow
      -- hsub : mpv (A 0) σ - mpv (B 0) σ = 0
      simp only [mpv, coeff] at hsub ⊢
      exact sub_eq_zero.mp hsub
    · -- General case (r ≥ 2): requires the full block separation argument
      -- This is PGVWC 2007 Theorem 3 / Cirac et al. 2021 Theorem IV.3.
      -- The proof uses:
      -- 1. Peeling: dominant block coefficient extraction via the summed identity
      -- 2. Newton's identities: power sums determine the characteristic polynomial
      --    (Newton-Girard trace formula: charpolyRev coefficients satisfy a triangular
      --    recurrence determined by traces of powers)
      -- 3. Injectivity gives algebraic spanning for sufficient constraint equations
      -- A full formalization requires ~300-500 lines of algebraic infrastructure
      -- (Newton-Girard trace formulas, eigenvalue analysis, or formal power series ODE).
      sorry

/-! ### DS gauge implies trace bound

**Mathematical content**: Under the doubly stochastic (DS) gauge normalization
∑_i A_i† A_i = I, the iterated TP condition `word_conjTranspose_mul_sum` gives
∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I for words of any length.
Each term is PSD, so for any specific word w, (evalWord A w)† (evalWord A w) ≤ I
(in the Loewner order). This means each diagonal entry satisfies ‖M_ii‖ ≤ 1,
giving |tr(M)| ≤ ∑ ‖M_ii‖ ≤ D. For M = (evalWord A w)^L, we use the
identity (evalWord A w)^L = evalWord A (w ++ w ++ ... ++ w). -/

open scoped ComplexOrder

private lemma star_mul_self_re_eq' (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  have : star z = starRingEnd ℂ z := rfl; rw [this, Complex.conj_mul']; norm_cast

private lemma star_mul_self_re_nonneg' (z : ℂ) : 0 ≤ (star z * z).re := by
  rw [star_mul_self_re_eq']; exact sq_nonneg _

/-- If ∑_σ (f σ)† (f σ) = I, then each diagonal entry of each f σ₀ has norm ≤ 1.
This follows from the PSD ordering: each (f σ₀)† (f σ₀) ≤ I. -/
private lemma norm_diag_le_one_from_sum_eq_one
    {D' : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin D') (Fin D') ℂ)
    (hf : ∑ σ, (f σ)ᴴ * f σ = 1)
    (σ₀ : ι) (i : Fin D') :
    ‖f σ₀ i i‖ ≤ 1 := by
  classical
  -- 1 - M†M is PSD (sum of remaining PSD terms)
  have h_psd : (1 - (f σ₀)ᴴ * f σ₀).PosSemidef := by
    have hsub : 1 - (f σ₀)ᴴ * f σ₀ = ∑ σ ∈ Finset.univ.erase σ₀, (f σ)ᴴ * f σ := by
      rw [← hf, ← Finset.add_sum_erase _ _ (Finset.mem_univ σ₀), add_sub_cancel_left]
    rw [hsub]
    exact Matrix.posSemidef_sum _ (fun σ _ => Matrix.posSemidef_conjTranspose_mul_self (f σ))
  -- (M†M)_ii ≤ 1 via ComplexOrder
  have h_diag_nn : 0 ≤ (1 - (f σ₀)ᴴ * f σ₀) i i := h_psd.diag_nonneg
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h_diag_nn
  have h_le : ((f σ₀)ᴴ * f σ₀) i i ≤ 1 := sub_nonneg.mp h_diag_nn
  -- Extract real-part bound
  have h_re : (((f σ₀)ᴴ * f σ₀) i i).re ≤ 1 := by
    have := (Complex.le_def.mp h_le).1; simpa using this
  -- (M†M)_ii = ∑_j star(M_ji) * M_ji
  have h_expand : ((f σ₀)ᴴ * f σ₀) i i = ∑ j, star ((f σ₀) j i) * (f σ₀) j i := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- ‖M_ii‖² ≤ re(∑_j star(M_ji) * M_ji) = re((M†M)_ii) ≤ 1
  have h_sq : ‖f σ₀ i i‖ ^ 2 ≤ 1 := by
    have h1 : (star (f σ₀ i i) * f σ₀ i i).re ≤
        (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := by
      simp only [Complex.re_sum]
      have : ∀ j : Fin D', j ∈ Finset.univ →
          0 ≤ (fun k => (star (f σ₀ k i) * f σ₀ k i).re) j :=
        fun j _ => star_mul_self_re_nonneg' (f σ₀ j i)
      exact Finset.single_le_sum this (Finset.mem_univ i)
    calc ‖f σ₀ i i‖ ^ 2
        = (star (f σ₀ i i) * f σ₀ i i).re := (star_mul_self_re_eq' _).symm
      _ ≤ (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := h1
      _ = (((f σ₀)ᴴ * f σ₀) i i).re := by rw [h_expand]
      _ ≤ 1 := h_re
  rwa [← abs_of_nonneg (norm_nonneg _), ← sq_le_one_iff_abs_le_one]

/-- Under DS gauge, the trace of any power of any word evaluation is bounded by D.
Uses the iterated TP condition and PSD diagonal bounds. -/
lemma ds_gauge_evalWord_trace_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (w : List (Fin d)) (L : ℕ) :
    ‖Matrix.trace ((evalWord A w) ^ L)‖ ≤ (D : ℝ) := by
  -- (evalWord A w)^L = evalWord A ((replicate L w).flatten)
  set n := w.length * L
  rw [← evalWord_flatten_replicate A w L]
  set w' := (List.replicate L w).flatten
  have hlen : w'.length = n := by
    simp [w', n, List.length_flatten, List.map_replicate,
      List.sum_replicate, smul_eq_mul, mul_comm]
  -- Express w' as List.ofFn σ₀ for a specific σ₀
  set σ₀ : Fin n → Fin d := fun i => w'.get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ₀ = w' := by
    conv_rhs => rw [← List.ofFn_getElem w']
    apply List.ofFn_congr (by omega)
  rw [← hofFn]
  -- word_conjTranspose_mul_sum: ∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I
  have h_sum := word_conjTranspose_mul_sum (fun i => A i) hA_ds n
  -- Each diagonal entry of evalWord A (ofFn σ₀) has norm ≤ 1
  have h_diag : ∀ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ ≤ 1 :=
    norm_diag_le_one_from_sum_eq_one
      (fun σ => evalWord A (List.ofFn σ)) h_sum σ₀
  -- ‖tr(M)‖ ≤ ∑_i ‖M_ii‖ ≤ ∑_i 1 = D
  calc ‖Matrix.trace (evalWord A (List.ofFn σ₀))‖
      ≤ ∑ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin D, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h_diag i)
    _ = (D : ℝ) := by simp [Finset.sum_const, Finset.card_fin]

/-! ### Peeling lemma -/

section PeelingLemma

/-- **Peeling lemma**: Given a weighted sum ∑_k α_k^L · δ_k(L) = 0 where
the leading coefficient |α₀| strictly dominates the others (|α_k| ≤ |α₀|·ρ
for k ≠ 0 with ρ < 1), and all δ_k are uniformly bounded, then δ₀(L)
decays exponentially: |δ₀(L)| ≤ C · ρ^L.

This is the key technical tool for extracting per-block information from
the global identity. It works by isolating δ₀ from the sum and bounding
the remaining terms using the dominance gap. -/
theorem peeling_exponential_bound
    {r : ℕ} (hr : 0 < r)
    (α : Fin r → ℂ) (hα₀ : α ⟨0, hr⟩ ≠ 0)
    (δ : Fin r → ℕ → ℂ)
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hδ_bound : ∀ k L, ‖δ k L‖ ≤ B)
    (h_sum : ∀ L : ℕ, ∑ k : Fin r, (α k) ^ L * δ k L = 0)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (hρ_bound : ∀ k : Fin r, k ≠ ⟨0, hr⟩ → ‖α k‖ ≤ ‖α ⟨0, hr⟩‖ * ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      ‖δ ⟨0, hr⟩ L‖ ≤ C * ρ ^ L := by
  set idx₀ : Fin r := ⟨0, hr⟩
  refine ⟨↑(r - 1) * B, mul_nonneg (Nat.cast_nonneg' _) hB_nn, ?_⟩
  intro L
  have h_eq := h_sum L
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx₀)] at h_eq
  have h_neg : (α idx₀) ^ L * δ idx₀ L =
      -(∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L) :=
    eq_neg_of_add_eq_zero_left h_eq
  have h_norm_eq : ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ =
      ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := by
    rw [← norm_mul, h_neg, norm_neg]
  have h_term_le : ∀ k ∈ Finset.univ.erase idx₀,
      ‖(α k) ^ L * δ k L‖ ≤ (‖α idx₀‖ * ρ) ^ L * B := by
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [norm_mul, norm_pow]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg _) (hρ_bound k hk.1) L
    · exact hδ_bound k L
    · exact norm_nonneg _
    · exact pow_nonneg (mul_nonneg (norm_nonneg _) hρ_pos.le) L
  have h_erase_card : (Finset.univ.erase idx₀).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  have h_sum_le : ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖
        ≤ ∑ k ∈ Finset.univ.erase idx₀, ‖(α k) ^ L * δ k L‖ :=
          norm_sum_le (Finset.univ.erase idx₀) _
      _ ≤ ∑ _k ∈ Finset.univ.erase idx₀, ((‖α idx₀‖ * ρ) ^ L * B) :=
          Finset.sum_le_sum h_term_le
      _ = ↑(Finset.univ.erase idx₀).card * ((‖α idx₀‖ * ρ) ^ L * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by rw [h_erase_card]
  have hα₀_pow_pos : (0 : ℝ) < ‖α idx₀‖ ^ L :=
    pow_pos (norm_pos_iff.mpr hα₀) L
  have h_chain : ‖α idx₀‖ ^ L * ‖δ idx₀ L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖α idx₀‖ ^ L * ‖δ idx₀ L‖
        = ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ := by rw [norm_pow]
      _ = ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := h_norm_eq
      _ ≤ ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := h_sum_le
  rw [mul_pow] at h_chain
  have : ↑(r - 1) * (‖α idx₀‖ ^ L * ρ ^ L * B) =
      ‖α idx₀‖ ^ L * (↑(r - 1) * B * ρ ^ L) := by ring
  rw [this] at h_chain
  exact le_of_mul_le_mul_left h_chain hα₀_pow_pos

end PeelingLemma

/-! ### Block separation -/

section BlockSeparation

/-- The summed identity for a fixed word w and all powers L.
From SameMPV₂ of block-diagonal tensors, for any word w of length M:
  ∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0
where T_k = evalWord(A_k, w), U_k = evalWord(B_k, w). -/
theorem summed_identity_for_word
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0)
    (w : List (Fin d)) (L : ℕ) :
    ∑ k : Fin r, ((μ k) ^ w.length) ^ L *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L)) = 0 := by
  set M := w.length
  have hlen : ((List.replicate L w).flatten).length = M * L := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, mul_comm]
  set σ : Fin (M * L) → Fin d := fun i =>
    ((List.replicate L w).flatten).get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ = (List.replicate L w).flatten := by
    conv_rhs => rw [← List.ofFn_getElem ((List.replicate L w).flatten)]
    apply List.ofFn_congr (by omega)
  have hsummed := h_summed (M * L) σ
  simp only [mpv, coeff, hofFn, evalWord_flatten_replicate, mul_sub] at hsummed
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hsummed
  conv_lhs =>
    arg 2; ext k
    rw [show ((μ k) ^ M) ^ L = (μ k) ^ (M * L) from (pow_mul _ _ _).symm]
  rw [show (∑ k : Fin r, (μ k) ^ (M * L) *
    (Matrix.trace ((evalWord (A k) w) ^ L) -
     Matrix.trace ((evalWord (B k) w) ^ L))) =
    ∑ k : Fin r, (μ k) ^ (M * L) * Matrix.trace ((evalWord (A k) w) ^ L) -
    ∑ k : Fin r, (μ k) ^ (M * L) * Matrix.trace ((evalWord (B k) w) ^ L)
    from by rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring]
  exact sub_eq_zero.mpr hsummed

theorem sameMPV_of_charpoly_eq_all_words
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (h : ∀ w : List (Fin d), (evalWord A w).charpoly = (evalWord B w).charpoly) :
    SameMPV A B := by
  intro N σ
  simp only [mpv, coeff]
  exact trace_eq_of_charpoly_eq _ _ (h (List.ofFn σ))

/-- Block separation for all blocks: a direct consequence of the core lemma.
Under canonical form hypotheses, the summed identity implies per-block SameMPV.
Requires injectivity of all blocks (used in the core lemma for the spectral gap
argument). -/
theorem block_separation_all_words
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hA_ds : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N *
        (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) :=
  block_separation_core μ A B hμ_strict hμ_ne_zero hA_inj hA_ds hB_ds h_summed

end BlockSeparation

/-! ### Block separation under canonical form -/

section CanonicalFormSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

theorem per_block_sameMPV_of_canonical_form
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  by_cases hr : r ≤ 1
  · intro k N σ
    have := sameMPV₂_summed_blocks μ A B hSame₂ N σ
    interval_cases r
    · exact k.elim0
    · have hk : k = 0 := Fin.ext (by omega)
      subst hk
      simp only [Fin.sum_univ_one, smul_eq_mul] at this
      exact mul_left_cancel₀ (pow_ne_zero N (hA.mu_ne_zero 0)) this
  · push_neg at hr
    have h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
        ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0 := by
      intro N σ
      have heq := sameMPV₂_summed_blocks μ A B hSame₂ N σ
      simp only [smul_eq_mul] at heq
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
    exact block_separation_all_words μ A B hA.mu_strict_anti hA.mu_ne_zero
      hA.block_injective hA.ds_gauge hB_ds h_summed

theorem fundamentalTheorem_canonicalForm
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  have hSep := per_block_sameMPV_of_canonical_form μ A B hA hB_ds hSame₂
  exact ⟨fun k => fundamentalTheorem_singleBlock (hA.block_injective k) (hSep k),
         fundamentalTheorem_multiBlock_global μ A B hA.block_injective hSep⟩

theorem fundamentalTheorem_canonicalForm_explicit
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  have hSep := per_block_sameMPV_of_canonical_form μ A B hA hB_ds hSame₂
  exact fundamentalTheorem_multiBlock_explicit A B hA.block_injective hSep

end CanonicalFormSeparation

end MPSTensor
