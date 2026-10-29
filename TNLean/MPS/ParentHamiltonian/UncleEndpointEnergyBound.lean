/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UnclePinnedTrialNorm
import TNLean.MPS.ParentHamiltonian.CyclicRestrictionNorm

/-!
# The actual finite two-wall trial has linear energy

The four pinned endpoint families are restrictions of explicit globally
pinned five-segment trials. Their actual squared norms grow at most
linearly in the remaining moving-wall length, uniformly in all padding.
The exact cyclic norm partition removes the redundant exterior-window
labels. Together with the derived endpoint residuals this bounds the actual
source trial energy by a constant times N, with no supplied state-rate or
energy-support premise.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- The four actual globally pinned trials, on the original source chain.
Their five segment lengths place the fixed wall at the indicated physical
endpoint; every cast is the proved source length equality.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
def uncleTrialPinnedGlobalState
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1)) :
    EuclideanSpace ℂ (Cfg d (6 * N + 1)) :=
  if i.val = N - 1 then
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm fun σ ↦
      uncleTwoWallTrial A B R L N 1 (3 * N - 1) (N + 1) N
        (σ ∘ Fin.cast (by omega))
  else if i.val = 2 * N then
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm fun σ ↦
      uncleTwoWallTrial A B R L (2 * N) 1 (2 * N - 1) (N + 1) N
        (σ ∘ Fin.cast (by omega))
  else if i.val = 4 * N - 1 then
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm fun σ ↦
      uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) 1 (2 * N)
        (σ ∘ Fin.cast (by omega))
  else if i.val = 5 * N then
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm fun σ ↦
      uncleTwoWallTrial A B R L N (N + 1) (3 * N - 1) 1 N
        (σ ∘ Fin.cast (by omega))
  else 0

/-- Restricting each actual globally pinned trial gives exactly the
explicit local pinned endpoint vector, including every exterior word.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem cyclicRestrictES_pinnedGlobalState_eq
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1))
    (hi : i ∈ uncleTrialEndpointBonds N hN) (τ : Cfg d (6 * N + 1)) :
    cyclicRestrictES (Fin.pos i) 2 i τ (uncleTrialPinnedGlobalState A B R L N hN i) =
      uncleTrialPinnedEndpointState A B R L N hN i τ := by
  have h01 : N - 1 < 2 * N := by omega
  have h12 : 2 * N < 4 * N - 1 := by omega
  have h23 : 4 * N - 1 < 5 * N := by omega
  rcases (mem_uncleTrialEndpointBonds_iff N hN i).mp hi with rfl | rfl | rfl | rfl
  · simp only [uncleTrialPinnedGlobalState, uncleTrialPinnedEndpointState,
      Fin.val_mk, if_pos rfl]
    ext σ
    change uncleTwoWallTrial A B R L N 1 (3 * N - 1) (N + 1) N
      ((cyclicCfg (by omega) 2 (⟨N - 1, by omega⟩ : Fin (6 * N + 1)) σ τ) ∘
        Fin.cast (by omega)) = _
    rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by omega),
      uncleTwoWallTrial_cast_apply_segments]
    simp only [show N + 1 + (3 * N - 1) = 4 * N by omega,
      show 4 * N + (N + 1) = 5 * N + 1 by omega]
    rw [uncleConfigSegment_contiguous_end τ 0 N (N - 1) _ hN (by omega) σ,
      uncleConfigSegment_contiguous_start τ N 1 (N - 1) _ (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ (N + 1) (3 * N - 1) (N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) (N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (5 * N + 1) N (N - 1) _ σ (by omega)]
    have hB : uncleConfigSegment τ (N + 1) (3 * N - 1) (by omega) =
        uncleConfigSegment τ (N + 1) N (by omega) ++
          uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega) := by
      simpa only [show N + (2 * N - 1) = 3 * N - 1 by omega,
        show N + 1 + N = 2 * N + 1 by omega] using
          uncleConfigSegment_add τ (N + 1) N (2 * N - 1) (by omega)
    rw [hB]
    simp [uncleTwoWallCoefficient, uncleConfigSegment, uncleDomainWallWord,
      Kraus.evalWord_append, Matrix.mul_assoc]
  · simp only [uncleTrialPinnedGlobalState, uncleTrialPinnedEndpointState, Fin.val_mk,
      if_neg (ne_of_gt h01), if_pos rfl]
    ext σ
    change uncleTwoWallTrial A B R L (2 * N) 1 (2 * N - 1) (N + 1) N
      ((cyclicCfg (by omega) 2 (⟨2 * N, by omega⟩ : Fin (6 * N + 1)) σ τ) ∘
        Fin.cast (by omega)) = _
    rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by omega),
      uncleTwoWallTrial_cast_apply_segments]
    simp only [show 2 * N + 1 + (2 * N - 1) = 4 * N by omega,
      show 4 * N + (N + 1) = 5 * N + 1 by omega]
    rw [uncleConfigSegment_contiguous_outside τ 0 (2 * N) (2 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_end τ (2 * N) 1 (2 * N) _ (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (2 * N + 1) (2 * N - 1) (2 * N) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) (2 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (5 * N + 1) N (2 * N) _ σ (by omega)]
    have hA : uncleConfigSegment τ 0 (2 * N) (by omega) =
        uncleConfigSegment τ 0 N (by omega) ++ uncleConfigSegment τ N N (by omega) := by
      simpa only [Nat.zero_add, show N + N = 2 * N by omega] using
        uncleConfigSegment_add τ 0 N N (by omega)
    rw [hA]
    simp [uncleTwoWallCoefficient, uncleConfigSegment, uncleDomainWallWord,
      Kraus.evalWord_append, show (2 * N - 1) - 1 = 2 * N - 2 by omega, Matrix.mul_assoc]
  · simp only [uncleTrialPinnedGlobalState, uncleTrialPinnedEndpointState, Fin.val_mk,
      if_neg (ne_of_gt (h01.trans h12)), if_neg (ne_of_gt h12), if_pos rfl]
    ext σ
    change uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) 1 (2 * N)
      ((cyclicCfg (by omega) 2 (⟨4 * N - 1, by omega⟩ : Fin (6 * N + 1)) σ τ) ∘
        Fin.cast (by omega)) = _
    rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by omega),
      uncleTwoWallTrial_cast_apply_segments]
    simp only [show N + (N + 1) = 2 * N + 1 by omega,
      show 2 * N + 1 + (2 * N - 1) = 4 * N by omega]
    rw [uncleConfigSegment_contiguous_outside τ 0 N (4 * N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ N (N + 1) (4 * N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_end τ (2 * N + 1) (2 * N - 1) (4 * N - 1) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (4 * N) 1 (4 * N - 1) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ (4 * N + 1) (2 * N) (4 * N - 1) _ σ
        (by omega)]
    have hA : uncleConfigSegment τ (4 * N + 1) (2 * N) (by omega) =
        uncleConfigSegment τ (4 * N + 1) N (by omega) ++
          uncleConfigSegment τ (5 * N + 1) N (by omega) := by
      simpa only [show N + N = 2 * N by omega,
        show 4 * N + 1 + N = 5 * N + 1 by omega] using
          uncleConfigSegment_add τ (4 * N + 1) N N (by omega)
    rw [hA]
    simp only [uncleTwoWallCoefficient_rotate]
    simp [uncleConfigSegment, uncleDomainWallWord, Kraus.evalWord_append,
      show (2 * N - 1) - 1 = 2 * N - 2 by omega, Matrix.mul_assoc]
  · simp only [uncleTrialPinnedGlobalState, uncleTrialPinnedEndpointState, Fin.val_mk,
      if_neg (ne_of_gt (h01.trans (h12.trans h23))), if_neg (ne_of_gt (h12.trans h23)),
      if_neg (ne_of_gt h23), if_pos rfl]
    ext σ
    change uncleTwoWallTrial A B R L N (N + 1) (3 * N - 1) 1 N
      ((cyclicCfg (by omega) 2 (⟨5 * N, by omega⟩ : Fin (6 * N + 1)) σ τ) ∘
        Fin.cast (by omega)) = _
    rw [cyclicCfg_eq_contiguousCfg (by omega) (by omega) (by omega),
      uncleTwoWallTrial_cast_apply_segments]
    simp only [show N + (N + 1) = 2 * N + 1 by omega,
      show 2 * N + 1 + (3 * N - 1) = 5 * N by omega]
    rw [uncleConfigSegment_contiguous_outside τ 0 N (5 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ N (N + 1) (5 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (2 * N + 1) (3 * N - 1) (5 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_end τ (5 * N) 1 (5 * N) _ (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (5 * N + 1) N (5 * N) _ hN (by omega) σ]
    have hB : uncleConfigSegment τ (2 * N + 1) (3 * N - 1) (by omega) =
        uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega) ++
          uncleConfigSegment τ (4 * N) N (by omega) := by
      simpa only [show 2 * N - 1 + N = 3 * N - 1 by omega,
        show 2 * N + 1 + (2 * N - 1) = 4 * N by omega] using
          uncleConfigSegment_add τ (2 * N + 1) (2 * N - 1) N (by omega)
    rw [hB]
    simp only [uncleTwoWallCoefficient_rotate]
    simp [uncleConfigSegment, uncleDomainWallWord, Kraus.evalWord_append, Matrix.mul_assoc]

/-- The four actual globally pinned states have a common linear
squared-norm bound in N+1, under precisely the normalized block inputs
needed for their actual one-wall Gram bounds. No state-rate premise is
supplied. Source: arXiv:1210.6613, Lemma lowenergystates, lines 1289–1296. -/
theorem norm_uncleTrialPinnedGlobalState_sq_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hfixA : Kraus.adjointMap A ρA = ρA) (hfixB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1)),
      i ∈ uncleTrialEndpointBonds N hN →
        ‖uncleTrialPinnedGlobalState A B R L N hN i‖ ^ 2 ≤ C * ((N + 1 : ℕ) : ℝ) := by
  obtain ⟨CR, hCR, hR⟩ := norm_uncleTwoWallTrial_one_wall_sq_le_mul
    A B R L hA hB ρB hρB hfixB hBA
  obtain ⟨CL, hCL, hL⟩ := norm_uncleTwoWallTrial_second_wall_sq_le_mul
    A B R L hA hB ρA hρA hfixA hAB
  let C := max CR CL
  have hC : 0 < C := lt_of_lt_of_le hCR (le_max_left _ _)
  refine ⟨C, hC, fun N hN i hi ↦ ?_⟩
  have h01 : N - 1 < 2 * N := by omega
  have h12 : 2 * N < 4 * N - 1 := by omega
  have h23 : 4 * N - 1 < 5 * N := by omega
  have hRC : CR ≤ C := le_max_left _ _
  have hLC : CL ≤ C := le_max_right _ _
  rcases (mem_uncleTrialEndpointBonds_iff N hN i).mp hi with rfl | rfl | rfl | rfl
  · simp only [uncleTrialPinnedGlobalState, Fin.val_mk, if_pos rfl,
      norm_uncleTwoWallTrial_cast]
    exact (hR N (3 * N - 1) (N + 1) N).trans
      (mul_le_mul_of_nonneg_right hRC (by positivity))
  · simp only [uncleTrialPinnedGlobalState, Fin.val_mk, if_neg (ne_of_gt h01), if_pos rfl,
      norm_uncleTwoWallTrial_cast]
    exact (hR (2 * N) (2 * N - 1) (N + 1) N).trans
      (mul_le_mul_of_nonneg_right hRC (by positivity))
  · simp only [uncleTrialPinnedGlobalState, Fin.val_mk,
      if_neg (ne_of_gt (h01.trans h12)), if_neg (ne_of_gt h12), if_pos rfl,
      norm_uncleTwoWallTrial_cast]
    exact (hL N (N + 1) (2 * N - 1) (2 * N)).trans
      (mul_le_mul_of_nonneg_right hLC (by positivity))
  · simp only [uncleTrialPinnedGlobalState, Fin.val_mk,
      if_neg (ne_of_gt (h01.trans (h12.trans h23))), if_neg (ne_of_gt (h12.trans h23)),
      if_neg (ne_of_gt h23), if_pos rfl, norm_uncleTwoWallTrial_cast]
    exact (hL N (N + 1) (3 * N - 1) N).trans
      (mul_le_mul_of_nonneg_right hLC (by positivity))

/-- The energy of the actual source two-wall trial is uniformly O(N).
The bound is derived from the actual four pinned residuals, actual Gram
estimates and the exact cyclic norm partition, rather than a supplied
energy or state-rate condition. These are the source normalized-block
hypotheses used for the variational construction; no injective perturbation
or generic nonvanishing is needed for this energy upper bound alone.
Source: arXiv:1210.6613, Lemma lowenergystates, item 3, lines 1289–1296. -/
theorem re_inner_uncleHamiltonianES_trial_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hfixA : Kraus.adjointMap A ρA = ρA) (hfixB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N →
      let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)
      (⟪uncleHamiltonianES A B R L (6 * N + 1) φ, φ⟫_ℂ).re ≤ C * N := by
  obtain ⟨C, hC, hPinned⟩ := norm_uncleTrialPinnedGlobalState_sq_le_mul A B R L hA hB
    ρA hρA ρB hρB hfixA hfixB hAB hBA
  refine ⟨8 * C, by positivity, fun N hN ↦ ?_⟩
  dsimp only
  by_cases hd : d = 0
  · subst d
    have hzero : uncleTwoWallTrialSource A B R L N = 0 := by
      funext σ
      exact Fin.elim0 (σ ⟨0, by omega⟩)
    simp [hzero]
  calc
    _ ≤ (((d ^ 2 : ℕ) : ℝ)⁻¹) * ∑ i ∈ uncleTrialEndpointBonds N hN,
        ∑ τ : Cfg d (6 * N + 1), ‖uncleTrialPinnedEndpointState A B R L N hN i τ‖ ^ 2 :=
      re_inner_uncleHamiltonianES_trial_le_pinnedEndpoint_norms A B R L N hN
    _ = ∑ i ∈ uncleTrialEndpointBonds N hN,
        ‖uncleTrialPinnedGlobalState A B R L N hN i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [← cyclicRestrictES_pinnedGlobalState_eq A B R L N hN i hi]
      exact inv_pow_mul_sum_norm_sq_cyclicRestrictES hd (by omega) i _
    _ ≤ ∑ _i ∈ uncleTrialEndpointBonds N hN, C * ((N + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun i hi ↦ hPinned N hN i hi
    _ = 4 * (C * ((N + 1 : ℕ) : ℝ)) := by
      simp only [Finset.sum_const, uncleTrialEndpointBonds_card, nsmul_eq_mul]
    _ ≤ 8 * C * N := by
      push_cast
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
      nlinarith [mul_le_mul_of_nonneg_left hNreal hC.le]

end MPSTensor
