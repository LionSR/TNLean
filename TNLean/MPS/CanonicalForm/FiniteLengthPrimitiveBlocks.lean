/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import QICLean.Channel.QuantumWielandt
import TNLean.MPS.Periodic.BlockDecomposition
import TNLean.MPS.Periodic.IrreducibleFormBlocking
import TNLean.MPS.Periodic.PeriodBound

/-!
# Primitive sectors at a prescribed finite length

At a positive length `N`, the periodic blocks that contribute have periods dividing `N`.
Every period is also at most the original bond dimension `D`, and hence divides `D!`.
Blocking by `gcd N D!` therefore removes the periods of all contributing blocks. The
prescribed step-orbit decomposition splits them into period-one sectors, retaining total
bond dimension at most `D`. The general quantum Wielandt estimate gives a common
injectivity length `(D² + 1)²` in the blocked alphabet.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849–880 and the blocking
device at lines 2090–2097; arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456.
The prescribed factorial-gcd choice and the simultaneous dimension estimate are project
consequences of these decompositions.

**Scope restriction (blocking cost and block separation):** the construction applies to
every positive `N`, including repeated small prime factors, but its blocking cost is at most
`D!`. It does not group phase-equivalent sectors or prove the review's polynomial W-state
bound. The logarithmic injectivity estimate remains separate; see
`docs/paper-gaps/rmp_w_state_ti_bound.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- At every positive chain length, an arbitrary tensor has a derived expansion into
primitive sectors after blocking by `gcd N D!`. The sectors have total bond dimension at
most `D`, have nonzero coefficients at the represented length, and are all injective after
`(D² + 1)²` blocked sites. Equality is only asserted at the original represented length,
not at all lengths after deleting the noncontributing periodic blocks.

Source: PGVWC07, Theorem 5 and lines 2090–2097; arXiv:1708.00029,
`lem:blocking-arbitrary`, with the general bound of arXiv:0909.5347, Theorem 1. -/
theorem exists_primitive_blocks_at_gcd_factorial {d D N : ℕ}
    (A : MPSTensor d D) (hN : 0 < N) :
    let p := N.gcd D.factorial
    0 < p ∧ p ∣ N ∧ p ≤ D.factorial ∧
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (B : (j : Fin r) → MPSTensor (blockPhysDim d p) (dim j)) (c : Fin r → ℂ),
      (∀ j, 0 < dim j) ∧ (∑ j, dim j) ≤ D ∧
      (∀ j, IsPeriodic 1 (B j)) ∧
      (∀ j, Kraus.IsNBlkInjective (B j) ((D ^ 2 + 1) ^ 2)) ∧
      (∀ j, c j ≠ 0) ∧
      ∀ σ : Cfg (blockPhysDim d p) (N / p),
        mpv (blockTensor A p) σ = ∑ j, c j * mpv (B j) σ := by
  classical
  let p := N.gcd D.factorial
  let M := N / p
  have hp : 0 < p := Nat.gcd_pos_of_pos_left _ hN
  have hpN : p ∣ N := Nat.gcd_dvd_left _ _
  have hMp : M * p = N := Nat.div_mul_cancel hpN
  have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hN hpN) hp
  refine ⟨hp, hpN, Nat.gcd_le_right N (Nat.factorial_pos D), ?_⟩
  obtain ⟨r, dim, μ, blocks, period, hper, hμ, hdim, hSame, hsum⟩ :=
    exists_periodic_blockDecomposition A
  have hdimD (k : Fin r) : dim k ≤ D :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (dim j)) (Finset.mem_univ k)).trans hsum
  have hperiodD (k : Fin r) : period k ≤ D :=
    (hper k).period_le_bondDim.trans (hdimD k)
  let S : Finset (Fin r) := Finset.univ.filter fun k => period k ∣ N
  let e : Fin S.card ≃ S := S.equivFin.symm
  let ι : Fin S.card → Fin r := fun k => (e k : Fin r)
  have hsurvives (k : Fin S.card) : period (ι k) ∣ N :=
    (Finset.mem_filter.mp (e k).2).2
  have hperiodp (k : Fin S.card) : period (ι k) ∣ p :=
    Nat.dvd_gcd (hsurvives k) (Nat.dvd_factorial (hper (ι k)).period_pos (hperiodD _))
  let n : Fin S.card → ℕ := fun k => (period (ι k)).gcd p
  obtain ⟨sd, B, hsd, htotal, hperRaw, hblock⟩ :=
    exists_periodic_family_blockDecomposition
      (fun k => blocks (ι k)) (fun k => period (ι k)) (fun k => hper (ι k)) hp
  have hperB (k : Fin S.card) (a : Fin (n k)) : IsPeriodic 1 (B k a) := by
    have hperiod : period (ι k) / (period (ι k)).gcd p = 1 := by
      rw [Nat.gcd_eq_left_iff_dvd.mpr (hperiodp k),
        Nat.div_self ((hper (ι k)).period_pos)]
    exact hperiod ▸ hperRaw k a
  let f := (finSigmaFinEquiv (n := n)).symm
  have hselected : (∑ k, dim (ι k)) ≤ D := by
    calc
      (∑ k, dim (ι k)) = ∑ k ∈ S, dim k := by
        rw [← Finset.sum_coe_sort S]
        exact e.sum_comp (fun k : S => dim k)
      _ ≤ ∑ k, dim k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ D := hsum
  have htotalFlat : (∑ j, sd (f j).1 (f j).2) ≤ D := by
    calc
      (∑ j, sd (f j).1 (f j).2) = ∑ k, dim (ι k) := by
        rw [Equiv.sum_comp f (fun ka => sd ka.1 ka.2), Fintype.sum_sigma]
        exact Finset.sum_congr rfl (fun k _ => htotal k)
      _ ≤ D := hselected
  have hC1 (j : Fin (∑ k, n k)) :
      Kraus.IsNBlkInjective (B (f j).1 (f j).2) ((D ^ 2 + 1) ^ 2) := by
    let C := B (f j).1 (f j).2
    have hpos : 0 < sd (f j).1 (f j).2 := hsd _ _
    let : NeZero (sd (f j).1 (f j).2) := ⟨hpos.ne'⟩
    obtain ⟨hIrr, hTP, hPrim⟩ := (IsPeriodic.one_iff_primitive C).mp (hperB _ _)
    have hIrrMap := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily C hIrr
    have hq := Kraus.wielandtIndex_le_general C hTP hIrrMap hPrim
    have hFrom := Kraus.hasFullWordSpanFrom_wielandtIndex C
      (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive C hTP hIrrMap hPrim)
    have hd : sd (f j).1 (f j).2 ≤ D :=
      (Finset.single_le_sum (fun j _ => Nat.zero_le (sd (f j).1 (f j).2))
        (Finset.mem_univ j)).trans htotalFlat
    have hd2 := Nat.pow_le_pow_left hd 2
    refine hFrom _ (hq.trans ?_)
    calc
      (sd (f j).1 (f j).2 ^ 2 - Kraus.krausRank C + 1) * sd (f j).1 (f j).2 ^ 2
          ≤ (D ^ 2 + 1) * D ^ 2 := Nat.mul_le_mul (by omega) hd2
      _ ≤ (D ^ 2 + 1) ^ 2 := by nlinarith
  have hblocked := sameMPV₂Pos_blockTensor_toTensorFromBlocks A μ blocks hSame p hp
  let γ : Fin r → ℂ := fun k => (μ k ^ p) ^ M
  have hdecomp (σ : Cfg (blockPhysDim d p) M) :
      mpv (blockTensor A p) σ = ∑ k, γ k * mpv (blockTensor (blocks k) p) σ := by
    rw [hblocked M hM σ, mpv_toTensorFromBlocks_eq_sum]
    rfl
  have hzero (k : Fin r) (hk : ¬period k ∣ N) (σ : Cfg (blockPhysDim d p) M) :
      mpv (blockTensor (blocks k) p) σ = 0 := by
    rw [mpv_blockTensor_eq_mpv_blockedFlatConfig]
    exact pgvwc07_stateVector_eq_zero_of_not_dvd (blocks k) (hper k)
      (by simpa only [hMp] using hk) _
  have hsumS (σ : Cfg (blockPhysDim d p) M) :
      mpv (blockTensor A p) σ = ∑ k ∈ S, γ k * mpv (blockTensor (blocks k) p) σ := by
    rw [hdecomp, Finset.sum_filter_of_ne]
    intro k _ hk
    by_contra hn
    exact right_ne_zero_of_mul hk (hzero k hn σ)
  have hsumSelected (σ : Cfg (blockPhysDim d p) M) :
      mpv (blockTensor A p) σ = ∑ k : Fin S.card,
        γ (ι k) * mpv (blockTensor (blocks (ι k)) p) σ := by
    rw [hsumS, ← Finset.sum_coe_sort S]
    exact (e.sum_comp (fun k : S => γ k * mpv (blockTensor (blocks k) p) σ)).symm
  have hflat := sameMPV₂_toTensorFromBlocks_refinement (fun k => μ (ι k) ^ p)
    (fun k => blockTensor (blocks (ι k)) p) n sd B hblock
  refine ⟨∑ k, n k, (fun j => sd (f j).1 (f j).2), (fun j => B (f j).1 (f j).2),
    (fun j => γ (ι (f j).1)), (fun j => hsd _ _), htotalFlat,
    (fun j => hperB _ _), hC1, (fun j => pow_ne_zero _ (pow_ne_zero _ (hμ _).ne')), ?_⟩
  intro σ
  calc
    mpv (blockTensor A p) σ =
        mpv (toTensorFromBlocks (fun k => μ (ι k) ^ p)
          (fun k => blockTensor (blocks (ι k)) p)) σ := by
      rw [mpv_toTensorFromBlocks_eq_sum]
      exact hsumSelected σ
    _ = _ := by
      rw [hflat M σ, mpv_toTensorFromBlocks_eq_sum]
      rfl

end MPSTensor
