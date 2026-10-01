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
# W-state bounds at lengths without small divisors

The periodic decomposition in Pérez-García, Verstraete, Wolf, and Cirac
(arXiv:quant-ph/0608197, Theorem 5) makes a period-\(m\) block vanish at length \(N\)
whenever \(m\nmid N\). Nonzero cyclic sectors give \(m\le D\), so a length with no divisor
between \(2\) and \(D\) receives contributions only from primitive blocks. Applying the
canonical-block W-state argument and the general quantum Wielandt bound gives
\(N<2\max((D^2+1)^2,3(D-1)((D^2+1)^2+1))\).

This includes composite lengths whose prime factors exceed the bond dimension. The
prime-length theorem follows as a corollary, using the direct numerical bound when
\(N\le D\).

**Scope restriction (chain lengths and the general Wielandt index):** the cubic source
bound assumes Conjecture 2 of arXiv:quant-ph/0608197, and the review's bound
\(D^3\log D=\Omega(N)\) uses the Michałek–Shitov index. The general index used here yields
only a fifth-degree estimate, and lengths with a divisor between \(2\) and \(D\) require
an additional reduction. Documented in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main results

* `MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor` — the bound when no integer
  between two and the bond dimension divides the chain length.
* `MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_prime` — the prime-length consequence.

## References

* arXiv:quant-ph/0608197, Theorem 5, Appendix "An open problem", and the W-state corollary;
  `Papers/quant-ph_0608197/MPSarchive.tex`, lines 849–858, 2090–2097, and 2182–2225.
* arXiv:2011.12127, Appendix A, "The W state";
  `Papers/2011.12127/TN-Review-main.tex`, line 2362.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- Project result: the W-state bound when no integer between two and the bond dimension
divides the chain length.

The canonical reduction of arXiv:quant-ph/0608197, Appendix "An open problem", removes a
periodic block whenever its period does not divide the chain length (Theorem 5). The linear
period bound therefore suffices for this divisor hypothesis. The surviving primitive blocks
satisfy injectivity after \((D^2+1)^2\) sites by the general quantum Wielandt bound
(arXiv:0909.5347, Theorem 1). Grouping phase-equivalent blocks gives the hypotheses of the
canonical W-state bound. The remaining source restrictions are recorded in the module docstring. -/
theorem lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor {D : ℕ}
    (A : MPSTensor 2 D) {N : ℕ} (hN : 2 ≤ N)
    (hdiv : ∀ m : ℕ, 2 ≤ m → m ≤ D → ¬m ∣ N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_two hN
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
  have hmD : ∀ k, m k ≤ D := fun k ↦
    (hPer k).period_le_bondDim.trans (hdimD k)
  -- The divisor hypothesis makes every block of period greater than one vanish.
  have hzero : ∀ k, m k ≠ 1 → ∀ σ : Cfg 2 N, mpv (Blk k) σ = 0 := fun k hk σ => by
    have hndvd : ¬ m k ∣ N :=
      hdiv _ ((Nat.two_le_iff _).2 ⟨(hPer k).period_pos.ne', hk⟩) (hmD k)
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
    exact ⟨ξ, hξ, h N hNpos⟩
  choose ξ _ hξ using hphase
  let γ : Fin cls.g → ℂ := fun j => ∑ q, μ (cls.enum j q) ^ N * ξ j q ^ N
  have hdecomp : ∀ σ : Cfg 2 N, mpv A σ = ∑ j, γ j * mpv (Blk (cls.repr j)) σ := fun σ => by
    rw [hSame N hNpos σ, mpv_toTensorFromBlocks_eq_sum]
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

/-- At prime chain length, every translation-invariant periodic representation of a nonzero
multiple of the W state satisfies the fifth-degree bond-dimension bound.

This is the prime-length reduction of arXiv:quant-ph/0608197, Appendix "An open problem",
with the general quantum Wielandt estimate in place of its Conjecture 2. For \(N>D\),
primality implies the hypothesis of `lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor`;
for \(N\le D\), the numerical bound is immediate. -/
theorem lt_of_mpv_eq_smul_wIndicator_of_prime {D : ℕ} (A : MPSTensor 2 D) {N : ℕ}
    (hN : N.Prime) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  rcases le_or_gt N D with hND | hND
  · nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) D,
      le_max_left ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))]
  · exact lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor A hN.two_le
      (fun m hm2 hmD hdvd ↦ (hN.eq_one_or_self_of_dvd m hdvd).elim (by omega) (by omega)) hc hW

end MPSTensor
