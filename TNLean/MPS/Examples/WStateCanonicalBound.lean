/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.WStatePeriodic
import TNLean.MPS.ParentHamiltonian.PGVWC07CutRank
import QICLean.Channel.QuantumWielandt

/-!
# W state: the single-length bound from a canonical form with condition C1

**Source.** Pérez-García, Verstraete, Wolf, Cirac 2007 (arXiv:quant-ph/0608197), Appendix
"An open problem", subsection "W state", Corollary and proof,
`Papers/quant-ph_0608197/MPSarchive.tex` lines 2182–2225: if `W_N` is the periodic vector of
`D × D` matrices then, assuming Conjecture 2 (condition C1 by blocks with `L₀ = O(D²)`),
`D = Ω(N^{1/3})`. The proof cuts the chain into two pieces, each of at least
`3(b-1)(L₀+1)` sites, shows that the reduced state of one piece has rank at least
`∑_j D_j²`, uses that this rank is `2` for `W_N`, and excludes two blocks of size `1 × 1`;
hence `N/2 ≤ 3(b-1)(L₀+1)`.
Review: arXiv:2011.12127, Appendix A, "The W state", `Papers/2011.12127/TN-Review-main.tex`
line 2362, which cites this bound with the Wielandt index of Michałek and Shitov in the form
`D³ log D = Ω(N)`.

**Formalized here.** The inequality `N/2 ≤ 3(b-1)(L₀+1)` of the proof, for a periodic
tensor in the translation-invariant canonical form of PGVWC07 whose blocks satisfy condition
C1 at a common length `L₀`, and for every nonzero multiple of `W_N`; with the threshold
`max(L₀, 3(b-1)(L₀+1))` described below. When the first matrix `A^j_0` of every block is
invertible, the source's `L₀ = D²` (lines 2115–2118, through Wolf's Theorem 6.9(2)) turns this
into `N < 2 max(D²+1, 3(D-1)(D²+2))`, the source's `D = Ω(N^{1/3})` for such blocks. For
primitive blocks, Wolf's general quantum Wielandt bound gives the weaker
`N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`.
Along the way: the reduced state of `W_N` across any cut has rank at most `2`, and a sum of at
most two translation-invariant product states is not a multiple of `W_N` for `N ≥ 3`.

**Scope restriction (canonical form with condition C1 as hypothesis):** the source derives
condition C1 by blocks with `L₀ = O(D²)` for an arbitrary tensor from its Conjecture 2
(lines 2109–2111, 2187–2188), and the review replaces Conjecture 2 by the Wielandt bound of
Michałek and Shitov. The reduction of an arbitrary `D × D` tensor to a canonical form with
condition C1 is not formalized, and `L₀ = O(D²)` is formalized only when every `A^j_0` is
invertible (the source's proposition), not in general, nor is `O(D² log D)`. The canonical
form, condition C1, and pairwise distinctness of the blocks are hypotheses. Distinctness is
taken in the form used by the direct-sum lemma, no two blocks related by a gauge and a phase,
which is stricter than the source's pairwise different block states (lines 1329–1330).
Consequently neither the unconditional `D = Ω(N^{1/3})` nor `D³ log D = Ω(N)` is formalized.
Documented in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

**Local fix (single-block threshold):** for one block the printed inequality
`N/2 ≤ 3(b-1)(L₀+1)` reads `N ≤ 0`, which fails for `W_1 = |1⟩`, a product state; the proof
needs both pieces to have at least `L₀` sites to apply condition C1. The bound proved is
`N < 2 max(L₀, 3(b-1)(L₀+1))`. Documented in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main definitions

* `weightIndicator N m` — the indicator of the configurations of `N` sites with `m`
  excitations.

## Main results

* `wIndicator_append` — the W amplitude of a concatenation splits as
  `u₁(σ)u₀(τ) + u₀(σ)u₁(τ)`.
* `finrank_span_wIndicator_append_le_two` — the reduced state of `W_N` across any cut has
  rank at most `2`.
* `not_sum_pow_mul_pow_eq` — at most two geometric amplitudes do not give a multiple of
  `W_N` on the words `1^m 0^{N-m}`, `m = 1, 2, 3` (two product states need `N ≥ 3`).
* `PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator` — the bound
  `N < 2 max(L₀, 3(b-1)(L₀+1))`.
* `PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator_of_isUnit` — with `A^j_0`
  invertible in every block, `N < 2 max(D²+1, 3(D-1)(D²+2))`.
* `PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator_of_isPrimitive` — with primitive
  blocks and Wolf's general Wielandt bound, `N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`.

## References

- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix Product State Representations*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ### The W amplitude across a cut -/

/-- The indicator of the configurations of `N` sites with exactly `m` excitations; the W
amplitude is `weightIndicator N 1`. -/
def weightIndicator (N m : ℕ) : Cfg 2 N → ℂ :=
  fun σ => if (List.ofFn σ).count 1 = m then 1 else 0

/-- Source: arXiv:quant-ph/0608197, line 2208 (the decomposition behind "in the case of
`|W_N⟩` this rank is 2"). Cutting `N = R + R'` sites, the W amplitude of `σ τ` is
`u₁(σ)u₀(τ) + u₀(σ)u₁(τ)`, where `u_m` indicates `m` excitations. -/
theorem wIndicator_append {R R' : ℕ} (σ : Cfg 2 R) (τ : Cfg 2 R') :
    wIndicator (R + R') (Fin.append σ τ) =
      weightIndicator R 1 σ * weightIndicator R' 0 τ +
        weightIndicator R 0 σ * weightIndicator R' 1 τ := by
  simp only [wIndicator_apply, weightIndicator, List.ofFn_fin_append, List.count_append]
  rcases (List.ofFn σ).count 1 with _ | _ | a <;> rcases (List.ofFn τ).count 1 with _ | _ | b <;>
    simp
  omega

/-- Source: arXiv:quant-ph/0608197, line 2208 ("in the case of `|W_N⟩`, this rank is 2"). For
every configuration `τ` of the last `R'` sites, the amplitude `σ ↦ W(σ τ)` lies in the span of
the two indicators `u₁` and `u₀` on the first `R` sites; this span has dimension at most `2`. -/
theorem wIndicator_append_mem_span {R R' : ℕ} (τ : Cfg 2 R') :
    (fun σ : Cfg 2 R => wIndicator (R + R') (Fin.append σ τ)) ∈
      Submodule.span ℂ (Set.range ![weightIndicator R 1, weightIndicator R 0]) := by
  have : (fun σ : Cfg 2 R => wIndicator (R + R') (Fin.append σ τ)) =
      weightIndicator R' 0 τ • weightIndicator R 1 +
        weightIndicator R' 1 τ • weightIndicator R 0 := by
    funext σ
    rw [wIndicator_append]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The span of the two indicators `u₁`, `u₀` has dimension at most `2`. -/
theorem finrank_span_wIndicator_append_le_two (R : ℕ) :
    Module.finrank ℂ
      (Submodule.span ℂ (Set.range ![weightIndicator R 1, weightIndicator R 0])) ≤ 2 := by
  have := finrank_range_le_card (R := ℂ) ![weightIndicator R 1, weightIndicator R 0]
  rw [Fintype.card_fin] at this
  exact this

/-! ### At most two product states -/

/-- Project result, completing the step "It is trivial now to see that this is impossible"
of arXiv:quant-ph/0608197, lines 2208–2210. Let `x_k, y_k` (`k < r ≤ 2`) be complex numbers,
the weighted one-site amplitudes of at most two `1 × 1` blocks. The amplitude of the word
`1^m 0^{N-m}` is then `∑_k y_k^m x_k^{N-m}`; these amplitudes do not agree with `c W_N`,
`c ≠ 0`, for `m = 1, 2, 3`, as soon as `N ≥ 2`, and `N ≥ 3` when there are two blocks.

The restriction `N ≥ 3` for two blocks is necessary:
`W_2 = ((|0⟩+|1⟩)^{⊗2} - (|0⟩-|1⟩)^{⊗2})/2` is a sum of two translation-invariant
product states. -/
theorem not_sum_pow_mul_pow_eq {r : ℕ} (hr : r ≤ 2) {N : ℕ} (hN : 2 ≤ N)
    (hN₃ : r = 2 → 3 ≤ N) (x y : Fin r → ℂ) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ m, 1 ≤ m → m ≤ 3 → m ≤ N →
      ∑ k, y k ^ m * x k ^ (N - m) = if m = 1 then c else 0) : False := by
  interval_cases r
  · have h1 := h 1 le_rfl (by norm_num) (by omega)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ite_true] at h1
    exact hc h1.symm
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    have h1 := h 1 le_rfl (by norm_num) (by omega)
    have h2 := h 2 (by norm_num) (by norm_num) (by omega)
    simp only [Fin.sum_univ_one, ite_true, OfNat.ofNat_ne_one, ite_false,
      show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at h1 h2
    have hy : c * y 0 = 0 := by linear_combination (-y 0) * h1 + x 0 * h2
    rcases mul_eq_zero.mp hy with hc0 | hy0
    · exact hc hc0
    · rw [hy0] at h1; simp at h1; exact hc h1.symm
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by have := hN₃ rfl; omega⟩
    have h1 := h 1 le_rfl (by norm_num) (by omega)
    have h2 := h 2 (by norm_num) (by norm_num) (by omega)
    have h3 := h 3 (by norm_num) le_rfl (by omega)
    simp only [Fin.sum_univ_two, ite_true, OfNat.ofNat_ne_one, ite_false,
      show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega,
      show n + 3 - 3 = n by omega] at h1 h2 h3
    -- The two geometric sequences are annihilated by `(x₀ S - y₀)(x₁ S - y₁)`.
    have hyy : c * (y 0 * y 1) = 0 := by
      linear_combination -(y 0 * y 1) * h1 + (x 0 * y 1 + x 1 * y 0) * h2 - (x 0 * x 1) * h3
    rcases mul_eq_zero.mp hyy with hc0 | hyy
    · exact hc hc0
    rcases mul_eq_zero.mp hyy with hy | hy
    · rw [hy] at h1 h2
      have : c * y 1 = 0 := by linear_combination (-y 1) * h1 + x 1 * h2
      rcases mul_eq_zero.mp this with hc0 | hy1
      · exact hc hc0
      · rw [hy1] at h1; simp at h1; exact hc h1.symm
    · rw [hy] at h1 h2
      have : c * y 0 = 0 := by linear_combination (-y 0) * h1 + x 0 * h2
      rcases mul_eq_zero.mp this with hc0 | hy0
      · exact hc hc0
      · rw [hy0] at h1; simp at h1; exact hc h1.symm

/-! ### The bound -/

/-- On a one-dimensional index type, the trace of `M^p M'^q` is the product of the powers of
the single entries. -/
private theorem trace_pow_mul_pow_of_subsingleton {n : Type*} [Fintype n] [DecidableEq n]
    [Subsingleton n] (i : n) (M M' : Matrix n n ℂ) (p q : ℕ) :
    Matrix.trace (M ^ p * M' ^ q) = M i i ^ p * M' i i ^ q := by
  have hmul : ∀ P Q : Matrix n n ℂ, (P * Q) i i = P i i * Q i i := fun P Q => by
    rw [Matrix.mul_apply, Fintype.sum_subsingleton _ i]
  have hpow : ∀ (P : Matrix n n ℂ) (k : ℕ), (P ^ k) i i = P i i ^ k := fun P k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  rw [Matrix.trace, Fintype.sum_subsingleton _ i, Matrix.diag_apply, hmul, hpow, hpow]

/-- Source: arXiv:quant-ph/0608197, Corollary in the subsection "W state" and its proof,
`Papers/quant-ph_0608197/MPSarchive.tex` lines 2182–2222, in the conditional form the proof
establishes: "Therefore `N/2 ≤ 3(b-1)(L₀+1)`".

Let `A` be a periodic tensor in the translation-invariant canonical form of PGVWC07 with `b`
blocks, each satisfying condition C1 at a common length `L₀ > 0`, with no two blocks related
by a gauge and a phase. If the periodic vector of `A` on `N` sites is `c W_N` for some `c ≠ 0`, then
`N < 2 max(L₀, 3(b-1)(L₀+1))`.

The proof follows the source: cut the chain into pieces of at least
`max(L₀, 3(b-1)(L₀+1))` sites; by condition C1 and the direct-sum lemma the reduced state of
the first piece has rank at least `∑_j D_j²`; the W state has rank at most `2` across the cut,
so there are at most two blocks, all of size `1 × 1`; and at most two translation-invariant
product states do not give `c W_N`.

The scope restriction and the local fix stated in the module docstring apply: the canonical
form with condition C1 at `L₀` is a hypothesis, the distinctness hypothesis is stricter than
the source's pairwise different block states, and the threshold contains `L₀` for a single
block. -/
theorem PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator {D : ℕ} {A : MPSTensor 2 D}
    (h : PGVWC07CanonicalFormData A) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ k, Kraus.IsNBlkInjective (h.blocks k) L₀)
    (hDistinct : BlocksNotGaugePhaseEquiv (d := 2) h.blocks)
    {N : ℕ} {c : ℂ} (hc : c ≠ 0) (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max L₀ (3 * (h.r - 1) * (L₀ + 1)) := by
  classical
  by_contra hN
  push Not at hN
  set n₀ := max L₀ (3 * (h.r - 1) * (L₀ + 1)) with hn₀
  have hLn : L₀ ≤ n₀ := le_max_left _ _
  have hN2 : 2 ≤ N := by omega
  -- Word-level form of the hypothesis.
  have hWord : ∀ w : List (Fin 2), w.length = N →
      Matrix.trace (Kraus.evalWord A w) = c * if w.count 1 = 1 then 1 else 0 := by
    intro w hw
    subst hw
    simpa [List.ofFn_getElem] using hW (fun i => w[i])
  -- Cut rank: `∑_k D_k² ≤ 2`.
  have hsum : ∑ k, h.dim k ^ 2 ≤ 2 := by
    obtain ⟨R', rfl⟩ : ∃ R', N = n₀ + R' := ⟨N - n₀, by omega⟩
    have hR := h.wordTupleSpanTop_of_ge hL₀ hC1 hDistinct le_rfl
    have hR' := h.wordTupleSpanTop_of_ge hL₀ hC1 hDistinct (n := R') (by omega)
    refine le_trans (sum_sq_dim_le_finrank_of_forall_mem h.blocks
      (fun k => (h.weight k : ℂ) ^ (n₀ + R'))
      (fun k => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (h.weight_pos k).ne')) hR hR'
      (Submodule.span ℂ (Set.range ![weightIndicator n₀ 1, weightIndicator n₀ 0]))
      (fun τ => ?_)) (finrank_span_wIndicator_append_le_two n₀)
    have hfun : (fun σ : Cfg 2 n₀ => ∑ k, (h.weight k : ℂ) ^ (n₀ + R') *
        Matrix.trace (Kraus.evalWord (h.blocks k) (List.ofFn σ) *
          Kraus.evalWord (h.blocks k) (List.ofFn τ))) =
        c • fun σ : Cfg 2 n₀ => wIndicator (n₀ + R') (Fin.append σ τ) := by
      funext σ
      rw [Pi.smul_apply, smul_eq_mul, ← hW, h.mpv_eq_sum]
      simp [List.ofFn_fin_append, Kraus.evalWord_append]
    rw [hfun]
    exact Submodule.smul_mem _ _ (wIndicator_append_mem_span τ)
  -- Hence at most two blocks, each of size `1 × 1`.
  have hdim : ∀ k, h.dim k = 1 := fun k => by
    have h1 := h.dim_pos k
    have h2 : h.dim k ^ 2 ≤ 2 :=
      le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (h.dim j ^ 2))
        (Finset.mem_univ k)) hsum
    nlinarith
  have hr : h.r ≤ 2 := by
    simpa [hdim] using hsum
  have hN3 : h.r = 2 → 3 ≤ N := fun hr2 => by
    rw [hr2] at hn₀
    have : 6 ≤ n₀ := by rw [hn₀]; exact le_max_of_le_right (by omega)
    omega
  -- The amplitudes of the words `1^m 0^{N-m}`.
  let i : (k : Fin h.r) → Fin (h.dim k) := fun k => ⟨0, h.dim_pos k⟩
  refine not_sum_pow_mul_pow_eq hr hN2 hN3
    (fun k => (h.weight k : ℂ) * h.blocks k 0 (i k) (i k))
    (fun k => (h.weight k : ℂ) * h.blocks k 1 (i k) (i k)) hc (fun m _ _ hmN => ?_)
  have hlen : (List.replicate m (1 : Fin 2) ++ List.replicate (N - m) 0).length = N := by
    simp; omega
  have hcount : (List.replicate m (1 : Fin 2) ++ List.replicate (N - m) 0).count 1 = m := by
    simp [List.count_replicate]
  have key := hWord _ hlen
  rw [h.trace_evalWord_eq_sum, hlen, hcount] at key
  rw [show (if m = 1 then c else 0) = c * if m = 1 then 1 else 0 by split_ifs <;> simp, ← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : Subsingleton (Fin (h.dim k)) := Fin.subsingleton_iff_le_one.mpr (hdim k).le
  rw [Kraus.evalWord_append, Kraus.evalWord_replicate, Kraus.evalWord_replicate,
    trace_pow_mul_pow_of_subsingleton (i k), mul_pow, mul_pow]
  rw [show (h.weight k : ℂ) ^ N = (h.weight k : ℂ) ^ m * (h.weight k : ℂ) ^ (N - m) by
    rw [← pow_add, Nat.add_sub_cancel' hmN]]
  ring

/-- The block count and block sizes of a canonical form of bond dimension `D` are at most
`D`. -/
private theorem PGVWC07CanonicalFormData.r_le_and_dim_le {d D : ℕ} {A : MPSTensor d D}
    (h : PGVWC07CanonicalFormData A) : h.r ≤ D ∧ ∀ k, h.dim k ≤ D := by
  classical
  have hcard : ∑ k, h.dim k = D := by
    simpa [Fintype.card_sigma] using Fintype.card_congr h.index
  refine ⟨?_, fun k => ?_⟩
  · calc h.r = ∑ _k : Fin h.r, 1 := by simp
      _ ≤ ∑ k, h.dim k := Finset.sum_le_sum fun k _ => h.dim_pos k
      _ = D := hcard
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (h.dim j)) (Finset.mem_univ k)).trans
      hcard.le

/-- Project result: an explicit single-length bound in terms of the bond dimension, replacing
the source's Conjecture 2 (`L₀ = O(D²)`, arXiv:quant-ph/0608197, lines 2109–2111) by the
general quantum Wielandt bound `q ≤ (D_j² - k + 1) D_j²` (Wolf, Theorem 6.9; arXiv:0909.5347,
Theorem 1). Assume that `A` is a periodic tensor of bond dimension `D` in the canonical form of
PGVWC07 with pairwise distinct blocks (in the stricter sense of
`PGVWC07CanonicalFormData.wordTupleSpanTop_of_ge`), and that the dual channel
`X ↦ ∑_i A^{j†}_i X A^j_i` of every block is primitive, that is, has no peripheral eigenvalue
other than `1`. If the periodic vector of `A` on `N` sites is `c W_N`, `c ≠ 0`, then
`N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`, so `D ≥ Ω(N^{1/5})`. Irreducibility of the dual
channel, which the Wielandt bound also needs, follows from the canonical form
(`PGVWC07CanonicalFormData.isIrreducibleMap_mapLM_blocks_conjTranspose`).

This is weaker than the source's `D = Ω(N^{1/3})` and the review's `D³ log D = Ω(N)`, which
use `L₀ = O(D²)` and `L₀ = O(D² log D)`; primitivity of the blocks is a hypothesis (the source
removes peripheral eigenvalues by blocking, lines 2092–2096). -/
theorem PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator_of_isPrimitive {D : ℕ}
    {A : MPSTensor 2 D} (h : PGVWC07CanonicalFormData A)
    (hPrim : ∀ k, IsPrimitive (Kraus.mapLM fun i => (h.blocks k i)ᴴ))
    (hDistinct : BlocksNotGaugePhaseEquiv (d := 2) h.blocks)
    {N : ℕ} {c : ℂ} (hc : c ≠ 0) (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  classical
  obtain ⟨hrD, hdimD⟩ := h.r_le_and_dim_le
  have hC1 : ∀ k, Kraus.IsNBlkInjective (h.blocks k) ((D ^ 2 + 1) ^ 2) := by
    intro k
    have : NeZero (h.dim k) := ⟨(h.dim_pos k).ne'⟩
    have hTP : Kraus.IsTP fun i => (h.blocks k i)ᴴ := by
      simpa [Kraus.IsTP, Matrix.conjTranspose_conjTranspose] using h.unital k
    have hIrr := h.isIrreducibleMap_mapLM_blocks_conjTranspose k
    have hq := Kraus.wielandtIndex_le_general _ hTP hIrr (hPrim k)
    have hFrom := Kraus.hasFullWordSpanFrom_wielandtIndex _
      (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive _ hTP hIrr (hPrim k))
    refine Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose (hFrom _ ?_)
    refine hq.trans ?_
    have hd : h.dim k ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left (hdimD k) 2
    calc (h.dim k ^ 2 - Kraus.krausRank (fun i => (h.blocks k i)ᴴ) + 1) * h.dim k ^ 2
        ≤ (D ^ 2 + 1) * D ^ 2 := Nat.mul_le_mul (by omega) hd
      _ ≤ (D ^ 2 + 1) ^ 2 := by nlinarith
  refine (h.lt_of_mpv_eq_smul_wIndicator (by positivity) hC1 hDistinct hc hW).trans_le ?_
  gcongr

/-- Project result: the source's `D = Ω(N^{1/3})` when the first matrix of every block is
invertible. The source proves that condition C1 then holds at `L₀ = D²`
(arXiv:quant-ph/0608197, Proposition in Appendix "An open problem", lines 2115–2118); the
formal counterpart used here is Wolf, Theorem 6.9(2): for a trace-preserving family with
eventually full word span and an invertible element among its letters, the words of length
`D_j² - k + 1` span the full matrix algebra. Assume that `A` is a periodic tensor of bond
dimension `D` in the canonical form of PGVWC07 whose blocks satisfy condition C1 at some
positive length (lines 1314–1323), with pairwise distinct blocks (in the stricter sense of
`PGVWC07CanonicalFormData.wordTupleSpanTop_of_ge`), and with `A^j_0` invertible for every
block. If the periodic vector of `A` on `N` sites is `c W_N`, `c ≠ 0`, then
`N < 2 max(D²+1, 3(D-1)(D²+2))`, so `D = Ω(N^{1/3})`. -/
theorem PGVWC07CanonicalFormData.lt_of_mpv_eq_smul_wIndicator_of_isUnit {D : ℕ}
    {A : MPSTensor 2 D} (h : PGVWC07CanonicalFormData A)
    (hC1 : ∀ k, ∃ L, 0 < L ∧ Kraus.IsNBlkInjective (h.blocks k) L)
    (hA0 : ∀ k, IsUnit (h.blocks k 0))
    (hDistinct : BlocksNotGaugePhaseEquiv (d := 2) h.blocks)
    {N : ℕ} {c : ℂ} (hc : c ≠ 0) (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max (D ^ 2 + 1) (3 * (D - 1) * (D ^ 2 + 2)) := by
  classical
  obtain ⟨hrD, hdimD⟩ := h.r_le_and_dim_le
  have hC1' : ∀ k, Kraus.IsNBlkInjective (h.blocks k) (D ^ 2 + 1) := by
    intro k
    obtain ⟨L, hL, hinj⟩ := hC1 k
    have hTP : Kraus.IsTP fun i => (h.blocks k i)ᴴ := by
      simpa [Kraus.IsTP, Matrix.conjTranspose_conjTranspose] using h.unital k
    have hinj' : Kraus.IsNBlkInjective (fun i => (h.blocks k i)ᴴ) L :=
      Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose (K := fun i => (h.blocks k i)ᴴ)
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hinj)
    have hFull : Kraus.HasEventuallyFullWordSpan fun i => (h.blocks k i)ᴴ :=
      (Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP _ hTP).mpr ⟨L, hL, hinj'⟩
    have hq := Kraus.wordSpan_eq_top_of_mem_wordSpan_one_of_isUnit _ hFull
      (Kraus.apply_mem_wordSpan_one _ 0) (isUnit_star.mpr (hA0 k))
    refine Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose
      (Kraus.wordSpan_eq_top_of_ge_of_isTP _ hTP hq ?_)
    have hd : h.dim k ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left (hdimD k) 2
    omega
  refine (h.lt_of_mpv_eq_smul_wIndicator (by positivity) hC1' hDistinct hc hW).trans_le ?_
  have : 3 * (h.r - 1) * (D ^ 2 + 1 + 1) ≤ 3 * (D - 1) * (D ^ 2 + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) le_rfl
  exact Nat.mul_le_mul_left _ (max_le_max le_rfl this)

end MPSTensor
