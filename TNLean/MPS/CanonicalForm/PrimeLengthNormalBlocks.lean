/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.QuantumWielandt
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge
import TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Periodic.PeriodBound
import TNLean.MPS.Periodic.ScaledNormalization
import TNLean.MPS.Periodic.StateVectorDecomposition

/-!
# Normal blocks at lengths without small divisors

An arbitrary tensor has an actual finite-length expansion into separated
normal blocks when no integer between two and its bond dimension divides
the chain length. Nonprimitive periodic blocks vanish at that length;
phase-equivalent blocks are grouped and zero coefficients are removed.
Every surviving block has injectivity at the common general Wielandt
length and has no larger bond dimension than the original tensor.

This factors the tensor-independent canonical reduction out of the W-state
example. Source: SPWC10, arXiv:0909.5347, Theorem 5 proof, lines 858–880;
PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849–858 and the direct-sum
standing hypotheses at lines 1314–1330.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- At a length with no divisor between two and the original bond dimension,
there is an actual expansion into at most that many separated, canonically
normalized blocks. Their coefficients are nonzero, their bond dimensions
are positive and no larger, and every block is injective at \((D^2+1)^2\).
No canonical decomposition, periodic decomposition or injectivity estimate
is supplied as a hypothesis.
Source: SPWC10, Theorem 5 proof, lines 858–880; PGVWC07, Theorem 5,
lines 849–858, and phase grouping at lines 1314–1330. -/
theorem exists_normal_blocks_of_no_small_divisor {d D N : ℕ}
    (A : MPSTensor d D) (hN : 2 ≤ N)
    (hdiv : ∀ m : ℕ, 2 ≤ m → m ≤ D → ¬m ∣ N) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (B : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ),
      (∀ j, 0 < dim j) ∧ (∀ j, dim j ≤ D) ∧ r ≤ D ∧
      (∀ j, ∑ i, B j i * (B j i)ᴴ = 1) ∧
      (∀ j, ∃ ρ : Matrix (Fin (dim j)) (Fin (dim j)) ℂ, ρ.PosDef ∧
        Kraus.transferMap (fun i => (B j i)ᴴ) ρ = ρ) ∧
      (∀ j, Kraus.IsIrreducibleFamily (B j)) ∧
      (∀ j, Kraus.IsNBlkInjective (B j) ((D ^ 2 + 1) ^ 2)) ∧
      BlocksNotGaugePhaseEquiv (d := d) B ∧ (∀ j, c j ≠ 0) ∧
      ∀ σ : Cfg d N, mpv A σ = ∑ j, c j * mpv (B j) σ := by
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
      Kraus.transferMap (d := d) (D := dim k) (fun a => (Blk k a)ᴴ) Λ = Λ := fun k => by
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
  have hzero : ∀ k, m k ≠ 1 → ∀ σ : Cfg d N, mpv (Blk k) σ = 0 := fun k hk σ => by
    have hndvd : ¬ m k ∣ N :=
      hdiv _ ((Nat.two_le_iff _).2 ⟨(hPer k).period_pos.ne', hk⟩) (hmD k)
    have h0 := pgvwc07_stateVector_eq_zero_of_not_dvd (Bp k) (hPer k) hndvd σ
    rw [hmpvB k N σ] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (hζ k))
  -- A block of period `1` satisfies condition C1 at \((D^2+1)^2\).
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
  have hphase : ∀ j q, ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ σ : Cfg d N,
      mpv (Blk (cls.enum j q)) σ = ξ ^ N * mpv (Blk (cls.repr j)) σ := fun j q => by
    obtain ⟨ξ, hξ, h⟩ := cls.enum_phase j q
    exact ⟨ξ, hξ, h N hNpos⟩
  choose ξ _ hξ using hphase
  let γ : Fin cls.g → ℂ := fun j => ∑ q, μ (cls.enum j q) ^ N * ξ j q ^ N
  have hdecomp : ∀ σ : Cfg d N, mpv A σ = ∑ j, γ j * mpv (Blk (cls.repr j)) σ := fun σ => by
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
  have hsumT : ∀ σ : Cfg d N,
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
  have hTD : T.card ≤ D :=
    (Finset.card_le_univ T).trans (by simpa using hgr.trans hrD)
  refine ⟨T.card, (fun i => dim (cls.repr (ι i))),
    (fun i => Blk (cls.repr (ι i))), (fun i => γ (ι i)),
    (fun i => hdim _), (fun i => hdimD _), hTD,
    (fun i => hunital _), (fun i => hDual _), (fun i => hIrr _),
    (fun i => hC1 _ (hιT i).2), cls.blocks_not_equiv.comp hι,
    (fun i => (hιT i).1), ?_⟩
  intro σ
  rw [hsumT, ← Finset.sum_coe_sort T]
  exact (e.sum_comp (fun x : T => γ x * mpv (Blk (cls.repr x)) σ)).symm

end MPSTensor
