/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.WStateCanonicalBound
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Periodic.PeriodBound
import TNLean.MPS.Periodic.ScaledNormalization
import TNLean.MPS.Periodic.StateVectorDecomposition

/-!
# W state: the single-length bound at prime length for an arbitrary tensor

**Source.** Pérez-García, Verstraete, Wolf, Cirac 2007 (arXiv:quant-ph/0608197), Appendix
"An open problem", `Papers/quant-ph_0608197/MPSarchive.tex` lines 2090–2097: condition C2 in
each block of the canonical form implies condition C1 for a sufficiently large `L₀`, and the
peripheral eigenvalues of modulus one other than `1` "can be avoided by grouping the spins
into blocks or simply considering `N` prime" (Theorem 5, lines 849–858). The canonical form
is a sum of weighted block states with pairwise different blocks (lines 1314–1330), and the
W-state corollary (lines 2182–2225) bounds `N` by `2 · 3(b-1)(L₀+1)`.
Review: arXiv:2011.12127, Appendix A, "The W state", `Papers/2011.12127/TN-Review-main.tex`
line 2362.

**Formalized here.** The source's reduction at prime length, for an arbitrary `D × D`
tensor: bring the tensor to the translation-invariant canonical form with unital blocks;
at a prime length `N > D²` every block with a peripheral eigenvalue other than `1` has a
period `1 < m ≤ D² < N`, which does not divide the prime `N`, hence contributes zero; the remaining blocks are
primitive and satisfy condition C1 at `L₀ = (D²+1)²` by Wolf's general quantum Wielandt
bound; grouping blocks whose states agree up to a phase power gives pairwise distinct blocks.
The single-length bound of the corollary then gives, for every prime `N` and every tensor
whose periodic vector on `N` sites is `c W_N`, `c ≠ 0`,
`N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`, that is, `D = Ω(N^{1/5})` along prime lengths.

**Scope restriction (prime length and the general Wielandt index):** the source's
`D ≽ O(N^{1/3})` assumes Conjecture 2 (`L₀ = O(D²)`, lines 2109–2111), and the review's
`D³ log D = Ω(N)` uses the index `O(D² log D)` of Michałek and Shitov; neither index is
formalized for general blocks, so the exponent here is `1/5`. The bound is proved for prime
`N` only, the source's second device; for composite `N` blocking by the periods is not
formalized. Documented in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main results

* `MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_prime` — for prime `N`, an arbitrary tensor
  with periodic vector `c W_N` satisfies `N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`.

## References

- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix Product State Representations*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- Project result: the W-state bound at prime length for an arbitrary tensor.

Source of the reduction: arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex`
lines 2090–2097 (condition C2 gives condition C1; peripheral eigenvalues are avoided by
taking `N` prime), lines 1314–1330 (the canonical form as a sum of weighted block states
with pairwise different blocks), and lines 2182–2225 (the corollary and its proof). The
general quantum Wielandt bound (Wolf, Theorem 6.9; arXiv:0909.5347, Theorem 1) replaces
Conjecture 2.

Let `A` be any tensor of bond dimension `D` with two physical levels and `N` a prime. If the
periodic vector of `A` on `N` sites is `c W_N` with `c ≠ 0`, then
`N < 2 max((D²+1)², 3(D-1)((D²+1)²+1))`.

The proof: for `N ≤ D²` the bound is immediate. Otherwise take the canonical form with unital
blocks `A^j` and weights `λ_j`. Each block is irreducible and, rescaled and gauged, periodic
with some period `m_j ≤ D_j² < N`. If `m_j ≠ 1` then `m_j` does not divide the prime `N` and
the block state vanishes at length `N` (Theorem 5, lines 849–858: "If p is no factor,
then ψ=0"). If `m_j = 1` the block is primitive and
satisfies condition C1 at `(D²+1)²`. Grouping the blocks whose states agree up to a phase
power gives representatives no two of which are related by a gauge and a phase, with
coefficients `γ_j`; dropping those with `γ_j = 0` or period other than `1` leaves at most `D`
blocks that satisfy the hypotheses of `lt_of_sum_mpv_eq_smul_wIndicator`.

This is weaker than the source's `D = Ω(N^{1/3})` and the review's `D³ log D = Ω(N)`, and
holds for prime `N` only; see the scope restriction in the module docstring. -/
theorem lt_of_mpv_eq_smul_wIndicator_of_prime {D : ℕ} (A : MPSTensor 2 D) {N : ℕ}
    (hN : N.Prime) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  classical
  -- Short chains.
  rcases le_or_gt N (D ^ 2) with hND | hND
  · have h1 : D ^ 2 < (D ^ 2 + 1) ^ 2 := by nlinarith
    have h2 := le_max_left ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))
    omega
  -- The canonical form with unital blocks.
  obtain ⟨r, dim, μ, Blk, hΛ, hScalar, -, hdim, hSame, hsumdim⟩ :=
    exists_pgvwc07_unital_dualDiag_from_arbitrary A
  have hNZ : ∀ k, NeZero (dim k) := fun k => ⟨(hdim k).ne'⟩
  have hdimD : ∀ k, dim k ≤ D := fun k =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (dim j)) (Finset.mem_univ k)).trans hsumdim
  have hrD : r ≤ D :=
    calc r = ∑ _k : Fin r, 1 := by simp
      _ ≤ ∑ k, dim k := Finset.sum_le_sum fun k _ => hdim k
      _ ≤ D := hsumdim
  have hunital : ∀ k, ∑ i, Blk k i * (Blk k i)ᴴ = 1 := fun k => (hΛ k).choose_spec.2.2.1
  have hDual : ∀ k, ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ, Λ.PosDef ∧
      Kraus.transferMap (d := 2) (D := dim k) (fun a => (Blk k a)ᴴ) Λ = Λ := fun k => by
    obtain ⟨Λ, hPD, -, -, hfix⟩ := hΛ k
    exact ⟨Λ, hPD, hfix⟩
  have hIrr : ∀ k, Kraus.IsIrreducibleFamily (Blk k) := fun k => by
    obtain ⟨Λ, hPD, hfix⟩ := hDual k
    exact isIrreducibleFamily_of_unital_of_dualFixedPoint _ (hunital k) hPD hfix (hScalar k)
  have hne : ∀ k, ∃ i, Blk k i ≠ 0 := fun k => by
    by_contra h
    push Not at h
    have h1 := hunital k
    simp only [h, Matrix.zero_mul, Finset.sum_const_zero] at h1
    have := hNZ k
    exact zero_ne_one h1
  -- The periodic representative of each block.
  choose Bp ζ m hζ hGauge hmpvB hPer using fun k =>
    have := hNZ k
    exists_leftCanonical_periodic_scale_of_irreducible (hIrr k) (hne k)
  have hmN : ∀ k, m k < N := fun k =>
    ((hPer k).period_le_sq.trans (Nat.pow_le_pow_left (hdimD k) 2)).trans_lt hND
  -- A block of period other than `1` has zero state at the prime length `N`.
  have hzero : ∀ k, m k ≠ 1 → ∀ σ : Cfg 2 N, mpv (Blk k) σ = 0 := fun k hk σ => by
    have hndvd : ¬ m k ∣ N := fun hdvd => by
      rcases hN.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact hk h
      · exact (hmN k).ne h
    have h0 := pgvwc07_stateVector_eq_zero_of_not_dvd (Bp k) (hPer k) hndvd σ
    rw [hmpvB k N σ] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (hζ k))
  -- A block of period `1` satisfies condition C1 at `(D²+1)²`.
  have hC1 : ∀ k, m k = 1 → Kraus.IsNBlkInjective (Blk k) ((D ^ 2 + 1) ^ 2) := fun k hk => by
    have := hNZ k
    have hP1 : IsPeriodic 1 (Bp k) := hk ▸ hPer k
    obtain ⟨hIrrB, hTP, hPrim⟩ := (IsPeriodic.one_iff_primitive _).mp hP1
    have hIrrMap := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrrB
    have hq := Kraus.wielandtIndex_le_general _ hTP hIrrMap hPrim
    have hFrom := Kraus.hasFullWordSpanFrom_wielandtIndex _
      (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive _ hTP hIrrMap hPrim)
    have hd : dim k ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left (hdimD k) 2
    have hB : Kraus.IsNBlkInjective (Bp k) ((D ^ 2 + 1) ^ 2) := by
      refine hFrom _ (hq.trans ?_)
      calc (dim k ^ 2 - Kraus.krausRank (Bp k) + 1) * dim k ^ 2
          ≤ (D ^ 2 + 1) * D ^ 2 := Nat.mul_le_mul (by omega) hd
        _ ≤ (D ^ 2 + 1) ^ 2 := by nlinarith
    exact (isNBlkInjective_smul_iff (hζ k) (Blk k) _).mp
      (isNBlkInjective_of_gaugeEquiv hB (hGauge k).symm)
  -- Group the blocks whose states agree up to a phase power.
  let cls := mpvPhaseClassData Blk
  have hphase : ∀ j q, ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ σ : Cfg 2 N,
      mpv (Blk (cls.enum j q)) σ = ξ ^ N * mpv (Blk (cls.repr j)) σ := fun j q => by
    obtain ⟨ξ, hξ, h⟩ := cls.enum_phase j q
    exact ⟨ξ, hξ, h N hN.pos⟩
  choose ξ _ hξ using hphase
  let γ : Fin cls.g → ℂ := fun j => ∑ q, μ (cls.enum j q) ^ N * ξ j q ^ N
  have hdecomp : ∀ σ : Cfg 2 N, mpv A σ = ∑ j, γ j * mpv (Blk (cls.repr j)) σ := fun σ => by
    rw [hSame N hN.pos σ, mpv_toTensorFromBlocks_eq_sum]
    simp only [smul_eq_mul]
    rw [← cls.regroup (fun k => μ k ^ N * mpv (Blk k) σ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [γ, hξ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hgr : cls.g ≤ r := by
    have h1 := cls.regroup (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    have h2 : ∑ j, cls.copies j = r := by exact_mod_cast h1
    calc cls.g = ∑ _j : Fin cls.g, 1 := by simp
      _ ≤ ∑ j, cls.copies j := Finset.sum_le_sum fun j _ => cls.copies_pos j
      _ = r := h2
  -- Keep the classes with nonzero coefficient and period `1`.
  let T : Finset (Fin cls.g) := Finset.univ.filter fun j => γ j ≠ 0 ∧ m (cls.repr j) = 1
  have hsumT : ∀ σ : Cfg 2 N,
      mpv A σ = ∑ j ∈ T, γ j * mpv (Blk (cls.repr j)) σ := fun σ => by
    rw [hdecomp, Finset.sum_filter_of_ne]
    intro j _ hj
    refine ⟨left_ne_zero_of_mul hj, ?_⟩
    by_contra hm
    exact right_ne_zero_of_mul hj (hzero _ hm σ)
  let e : Fin T.card ≃ T := T.equivFin.symm
  let ι : Fin T.card → Fin cls.g := fun i => (e i : Fin cls.g)
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιT : ∀ i, γ (ι i) ≠ 0 ∧ m (cls.repr (ι i)) = 1 := fun i =>
    (Finset.mem_filter.mp (e i).2).2
  have hW' : ∀ σ : Cfg 2 N,
      ∑ i, γ (ι i) * mpv (Blk (cls.repr (ι i))) σ = c * wIndicator N σ := fun σ => by
    rw [← hW, hsumT, ← Finset.sum_coe_sort T]
    exact e.sum_comp (fun x : T => γ x * mpv (Blk (cls.repr x)) σ)
  have hTD : T.card ≤ D :=
    (Finset.card_le_univ T).trans (by simpa using hgr.trans hrD)
  refine (lt_of_sum_mpv_eq_smul_wIndicator (fun i => Blk (cls.repr (ι i))) (fun i => hdim _)
    (fun i => hunital _) (fun i => hDual _) (fun i => hIrr _) (by positivity)
    (fun i => hC1 _ (hιT i).2) (cls.blocks_not_equiv.comp hι) (fun i => γ (ι i))
    (fun i => (hιT i).1) hc hW').trans_le ?_
  gcongr

end MPSTensor
