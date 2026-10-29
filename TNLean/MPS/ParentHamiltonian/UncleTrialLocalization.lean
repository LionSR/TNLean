/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTwoWallTrial
import TNLean.MPS.ParentHamiltonian.WrappingWindowLastSiteFactorization

/-!
# Localization of the finite uncle trial's energy

Only the four bonds at the endpoints of the two moving-wall intervals can
contribute to the source trial's energy. The periodic bond across the cut
is an ordinary A/A bond and also vanishes. This is an exact finite-chain
statement, before any norm or endpoint-energy estimate.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- A local pair disjoint from a numbered segment leaves its word fixed. -/
theorem uncleConfigSegment_contiguous_outside {T : ℕ}
    (τ : Cfg d T) (s n i : ℕ) (hs : s + n ≤ T) (σ : Cfg d 2)
    (h : s + n ≤ i ∨ i + 2 ≤ s) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) s n hs =
      uncleConfigSegment τ s n hs := by
  apply congrArg List.ofFn
  funext j
  change contiguousCfg i 2 σ τ ⟨s + j.val, by omega⟩ = _
  rw [contiguousCfg, dite_eq_right (by
    change ¬(i ≤ s + j.val ∧ s + j.val < i + 2)
    rcases h with h | h <;> omega)]

private theorem uncleConfigSegment_contiguous_inside {T : ℕ}
    (τ : Cfg d T) (s n i : ℕ) (hs : s + n ≤ T) (σ : Cfg d 2)
    (hsi : s ≤ i) (hi : i + 2 ≤ s + n) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) s n hs =
      uncleConfigSegment τ s (i - s) (by omega) ++ List.ofFn σ ++
        uncleConfigSegment τ (i + 2) (s + n - (i + 2)) (by omega) := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show n = (i - s + 2) + (s + n - (i + 2)) by omega),
    List.ofFn_add, List.ofFn_add]
  refine congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (List.ofFn_inj.mpr (funext fun j ↦ ?_))
      (List.ofFn_inj.mpr (funext fun j ↦ ?_)))
    (List.ofFn_inj.mpr (funext fun j ↦ ?_))
  · change contiguousCfg i 2 σ τ ⟨s + j.val, by omega⟩ = τ ⟨s + j.val, by omega⟩
    rw [contiguousCfg, dite_eq_right (by
      change ¬(i ≤ s + j.val ∧ s + j.val < i + 2)
      omega)]
  · change contiguousCfg i 2 σ τ ⟨s + (i - s + j.val), by omega⟩ = σ j
    rw [contiguousCfg, dite_eq_left (by
      change i ≤ s + (i - s + j.val) ∧ s + (i - s + j.val) < i + 2
      omega)]
    apply congrArg σ
    exact Fin.ext (by change s + (i - s + j.val) - i = j.val; omega)
  · change contiguousCfg i 2 σ τ ⟨s + (i - s + 2 + j.val), by omega⟩ =
      τ ⟨i + 2 + j.val, by omega⟩
    rw [contiguousCfg, dite_eq_right (by
      change ¬(i ≤ s + (i - s + 2 + j.val) ∧ s + (i - s + 2 + j.val) < i + 2)
      omega)]
    apply congrArg τ
    exact Fin.ext (by change s + (i - s + 2 + j.val) = i + 2 + j.val; omega)

private theorem trace_evalWord_pair_mem_groundSpace {c : ℕ} (C : MPSTensor d c)
    (P Q : Matrix (Fin c) (Fin c) ℂ) :
    (fun σ : Cfg d 2 ↦ Matrix.trace (P * Kraus.evalWord C (List.ofFn σ) * Q)) ∈
      groundSpace C 2 := by
  refine ⟨Q * P, ?_⟩
  ext σ
  simpa only [groundSpaceMap_apply, Matrix.mul_assoc] using
    Matrix.trace_mul_comm (Kraus.evalWord C (List.ofFn σ) * Q) P

/-- Fixed exterior contractions of a pure A pair lie in the actual local uncle kernel. -/
theorem uncleInteractionES_uniform_slice_left_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P Q : Matrix (Fin a) (Fin a) ℂ) (u v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * Kraus.evalWord A (u ++ List.ofFn σ ++ v) * Q))) = 0 := by
  apply uncleInteractionES_apply_eq_zero_left
  rw [mem_groundSpaceES_iff]
  simpa only [LinearEquiv.apply_symm_apply, Kraus.evalWord_append, Matrix.mul_assoc] using
    trace_evalWord_pair_mem_groundSpace A (P * Kraus.evalWord A u) (Kraus.evalWord A v * Q)

/-- Fixed exterior contractions of a pure B pair lie in the actual local uncle kernel. -/
theorem uncleInteractionES_uniform_slice_right_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P Q : Matrix (Fin b) (Fin b) ℂ) (u v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * Kraus.evalWord B (u ++ List.ofFn σ ++ v) * Q))) = 0 := by
  apply uncleInteractionES_apply_eq_zero_right
  rw [mem_groundSpaceES_iff]
  simpa only [LinearEquiv.apply_symm_apply, Kraus.evalWord_append, Matrix.mul_assoc] using
    trace_evalWord_pair_mem_groundSpace B (P * Kraus.evalWord B u) (Kraus.evalWord B v * Q)

private theorem uncle_uniform_middle
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (p r u v x y : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ uncleTwoWallCoefficient A B R L p r (u ++ List.ofFn σ ++ v) x y)) = 0 := by
  have hfun :
      (fun σ : Cfg d 2 ↦
        uncleTwoWallCoefficient A B R L p r (u ++ List.ofFn σ ++ v) x y) =
      (fun σ ↦ Matrix.trace (Kraus.evalWord B (u ++ List.ofFn σ ++ v) *
        (uncleDomainWallWord B A L x * Kraus.evalWord A y *
          Kraus.evalWord A p * uncleDomainWallWord A B R r))) := by
    funext σ
    simpa only [Matrix.mul_assoc] using
      uncleTwoWallCoefficient_rotate A B R L p r (u ++ List.ofFn σ ++ v) x y
  rw [hfun]
  simpa only [Matrix.one_mul] using uncleInteractionES_uniform_slice_right_eq_zero A B R L 1
    (uncleDomainWallWord B A L x * Kraus.evalWord A y *
      Kraus.evalWord A p * uncleDomainWallWord A B R r) u v

/-- The four source interval-end bonds, in zero-based coordinates.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
def uncleTrialEndpointBonds (N : ℕ) (hN : 0 < N) : Finset (Fin (6 * N + 1)) :=
  {⟨N - 1, by omega⟩, ⟨2 * N, by omega⟩, ⟨4 * N - 1, by omega⟩, ⟨5 * N, by omega⟩}

/-- Membership in the actual four endpoint bonds is the corresponding
four-way coordinate equality. -/
theorem mem_uncleTrialEndpointBonds_iff (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1)) :
    i ∈ uncleTrialEndpointBonds N hN ↔
      i = ⟨N - 1, by omega⟩ ∨ i = ⟨2 * N, by omega⟩ ∨
        i = ⟨4 * N - 1, by omega⟩ ∨ i = ⟨5 * N, by omega⟩ := by
  simp only [uncleTrialEndpointBonds, Finset.mem_insert, Finset.mem_singleton]

/-- The four endpoint bonds are distinct for every positive source size. -/
theorem uncleTrialEndpointBonds_card (N : ℕ) (hN : 0 < N) :
    (uncleTrialEndpointBonds N hN).card = 4 := by
  have h01 : N - 1 < 2 * N := by omega
  have h12 : 2 * N < 4 * N - 1 := by omega
  have h23 : 4 * N - 1 < 5 * N := by omega
  simp [uncleTrialEndpointBonds, Fin.ext_iff, ne_of_lt h01, ne_of_lt h12,
    ne_of_lt h23, ne_of_lt (h01.trans h12), ne_of_lt (h12.trans h23),
    ne_of_lt (h01.trans (h12.trans h23))]

private theorem uncleTrial_contiguous_cancel
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : ℕ) (hi : i + 2 ≤ 6 * N + 1)
    (h0 : i ≠ N - 1) (h1 : i ≠ 2 * N) (h2 : i ≠ 4 * N - 1) (h3 : i ≠ 5 * N)
    (τ : Cfg d (6 * N + 1)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N))) = 0 := by
  have hcases : i + 2 ≤ N ∨
      (N ≤ i ∧ i + 2 ≤ 2 * N + 1) ∨
      (2 * N + 1 ≤ i ∧ i + 2 ≤ 4 * N) ∨
      (4 * N ≤ i ∧ i + 2 ≤ 5 * N + 1) ∨
      5 * N + 1 ≤ i := by omega
  rcases hcases with hc | ⟨hc, hd⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩ | hc
  · have hfun : contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N) =
        fun σ ↦ uncleTwoWallCoefficient A B R L
          (uncleConfigSegment τ 0 i (by omega) ++ List.ofFn σ ++
            uncleConfigSegment τ (i + 2) (N - (i + 2)) (by omega))
          (uncleConfigSegment τ N (N + 1) (by omega))
          (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
          (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
          (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
      funext σ
      simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
      rw [uncleConfigSegment_contiguous_inside τ 0 N i _ σ (by omega) (by omega)]
      simp only [Nat.sub_zero, Nat.zero_add]
      rw [uncleConfigSegment_contiguous_outside τ N (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (5 * N + 1) N i _ σ (by omega)]
    rw [hfun]
    simpa only [uncleTwoWallCoefficient, Matrix.one_mul, Matrix.mul_assoc] using
      uncleInteractionES_uniform_slice_left_eq_zero A B R L 1
        (uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)) *
          Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
          uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
          Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)))
        (uncleConfigSegment τ 0 i (by omega))
        (uncleConfigSegment τ (i + 2) (N - (i + 2)) (by omega))
  · have hfun : contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N) =
        fun σ ↦ uncleTwoWallCoefficient A B R L
          (uncleConfigSegment τ 0 N (by omega))
          (uncleConfigSegment τ N (i - N) (by omega) ++ List.ofFn σ ++
            uncleConfigSegment τ (i + 2) (2 * N + 1 - (i + 2)) (by omega))
          (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
          (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
          (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
      funext σ
      simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
      rw [uncleConfigSegment_contiguous_inside τ N (N + 1) i _ σ hc (by omega)]
      rw [uncleConfigSegment_contiguous_outside τ 0 N i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (5 * N + 1) N i _ σ (by omega)]
      simp only [show N + (N + 1) = 2 * N + 1 by omega]
    rw [hfun]
    exact uncleInteractionES_twoWall_slice_first_eq_zero A B R L _ _ _ _ _ _
  · have hfun : contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N) =
        fun σ ↦ uncleTwoWallCoefficient A B R L
          (uncleConfigSegment τ 0 N (by omega))
          (uncleConfigSegment τ N (N + 1) (by omega))
          (uncleConfigSegment τ (2 * N + 1) (i - (2 * N + 1)) (by omega) ++
            List.ofFn σ ++ uncleConfigSegment τ (i + 2) (4 * N - (i + 2)) (by omega))
          (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
          (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
      funext σ
      simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
      rw [uncleConfigSegment_contiguous_inside τ (2 * N + 1) (2 * N - 1) i _ σ hc
        (by omega)]
      rw [uncleConfigSegment_contiguous_outside τ 0 N i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ N (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (5 * N + 1) N i _ σ (by omega)]
      simp only [show 2 * N + 1 + (2 * N - 1) = 4 * N by omega]
    rw [hfun]
    exact uncle_uniform_middle A B R L _ _ _ _ _ _
  · have hfun : contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N) =
        fun σ ↦ uncleTwoWallCoefficient A B R L
          (uncleConfigSegment τ 0 N (by omega))
          (uncleConfigSegment τ N (N + 1) (by omega))
          (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
          (uncleConfigSegment τ (4 * N) (i - 4 * N) (by omega) ++ List.ofFn σ ++
            uncleConfigSegment τ (i + 2) (5 * N + 1 - (i + 2)) (by omega))
          (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
      funext σ
      simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
      rw [uncleConfigSegment_contiguous_inside τ (4 * N) (N + 1) i _ σ hc (by omega)]
      rw [uncleConfigSegment_contiguous_outside τ 0 N i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ N (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (5 * N + 1) N i _ σ (by omega)]
      simp only [show 4 * N + (N + 1) = 5 * N + 1 by omega]
    rw [hfun]
    exact uncleInteractionES_twoWall_slice_second_eq_zero A B R L _ _ _ _ _ _
  · have hfun : contiguousRestrictₗ i 2 hi τ (uncleTwoWallTrialSource A B R L N) =
        fun σ ↦ uncleTwoWallCoefficient A B R L
          (uncleConfigSegment τ 0 N (by omega))
          (uncleConfigSegment τ N (N + 1) (by omega))
          (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
          (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
          (uncleConfigSegment τ (5 * N + 1) (i - (5 * N + 1)) (by omega) ++
            List.ofFn σ ++ uncleConfigSegment τ (i + 2) (6 * N + 1 - (i + 2)) (by omega)) := by
      funext σ
      simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
      rw [uncleConfigSegment_contiguous_inside τ (5 * N + 1) N i _ σ hc (by omega)]
      rw [uncleConfigSegment_contiguous_outside τ 0 N i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ N (N + 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) i _ σ (by omega),
        uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) i _ σ (by omega)]
      simp only [show 5 * N + 1 + N = 6 * N + 1 by omega]
    rw [hfun]
    simpa only [uncleTwoWallCoefficient, Matrix.mul_one, Matrix.mul_assoc] using
      uncleInteractionES_uniform_slice_left_eq_zero A B R L
        (Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
          uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)) *
          Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
          uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega))) 1
        (uncleConfigSegment τ (5 * N + 1) (i - (5 * N + 1)) (by omega))
        (uncleConfigSegment τ (i + 2) (6 * N + 1 - (i + 2)) (by omega))

private theorem uncleConfigSegment_last_outside
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) (σ : Cfg d 2)
    (s n : ℕ) (hs : 1 ≤ s) (hn : s + n ≤ 6 * N) :
    uncleConfigSegment
        (cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ)
        s n (by omega) = uncleConfigSegment τ s n (by omega) := by
  apply congrArg List.ofFn
  funext j
  exact cyclicCfg_complement_site (by omega) (by omega) (by omega) σ τ
    (show 2 - 1 ≤ s + j.val by omega) (show s + j.val < 6 * N + 1 - 1 by omega)

private theorem uncleConfigSegment_last_prefix
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) (σ : Cfg d 2) :
    uncleConfigSegment
        (cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ)
        0 N (by omega) = [σ 1] ++ uncleConfigSegment τ 1 (N - 1) (by omega) := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show N = 1 + (N - 1) by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · simp only [List.ofFn_succ, List.ofFn_zero, Nat.zero_add]
    congr 1
    change cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ
      ⟨0, by omega⟩ = σ 1
    exact cyclicCfg_window_site (by omega) (by omega) (by omega) σ τ
      (k := 0) (by omega)
  · apply congrArg List.ofFn
    funext j
    change cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ
      ⟨1 + j.val, by omega⟩ = τ ⟨1 + j.val, by omega⟩
    exact cyclicCfg_complement_site (by omega) (by omega) (by omega) σ τ
      (show 2 - 1 ≤ 1 + j.val by omega) (show 1 + j.val < 6 * N + 1 - 1 by omega)

private theorem uncleConfigSegment_last_suffix
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) (σ : Cfg d 2) :
    uncleConfigSegment
        (cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ)
        (5 * N + 1) N (by omega) =
      uncleConfigSegment τ (5 * N + 1) (N - 1) (by omega) ++ [σ 0] := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show N = (N - 1) + 1 by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext j
    change cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ
      ⟨5 * N + 1 + j.val, by omega⟩ = τ ⟨5 * N + 1 + j.val, by omega⟩
    exact cyclicCfg_complement_site (by omega) (by omega) (by omega) σ τ
      (show 2 - 1 ≤ 5 * N + 1 + j.val by omega)
      (show 5 * N + 1 + j.val < 6 * N + 1 - 1 by omega)
  · simp only [List.ofFn_succ, List.ofFn_zero]
    congr 1
    change cyclicCfg (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) σ τ
      ⟨5 * N + 1 + (N - 1), by omega⟩ = σ 0
    have hsite : (⟨5 * N + 1 + (N - 1), by omega⟩ : Fin (6 * N + 1)) =
        ⟨6 * N, by omega⟩ := Fin.ext (by
          change 5 * N + 1 + (N - 1) = 6 * N
          omega)
    rw [hsite]
    exact cyclicCfg_last_eq (by omega) (by omega) (by omega) σ τ

private theorem uncleTrial_wrap_cancel
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) τ
        (uncleTwoWallTrialSource A B R L N))) = 0 := by
  let M := Kraus.evalWord A (uncleConfigSegment τ 1 (N - 1) (by omega)) *
    uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)) *
    Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
    uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
    Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) (N - 1) (by omega))
  have hfun : cyclicRestrictₗ (by omega) 2 (⟨6 * N, by omega⟩ : Fin (6 * N + 1)) τ
      (uncleTwoWallTrialSource A B R L N) = groundSpaceMap A 2 M := by
    ext σ
    simp only [cyclicRestrictₗ_apply, uncleTwoWallTrialSource]
    rw [uncleConfigSegment_last_prefix N hN τ σ,
      uncleConfigSegment_last_suffix N hN τ σ,
      uncleConfigSegment_last_outside N hN τ σ N (N + 1) (by omega) (by omega),
      uncleConfigSegment_last_outside N hN τ σ (2 * N + 1) (2 * N - 1)
        (by omega) (by omega),
      uncleConfigSegment_last_outside N hN τ σ (4 * N) (N + 1) (by omega) (by omega)]
    simpa only [uncleTwoWallCoefficient, groundSpaceMap_apply, Kraus.evalWord_append,
      Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, List.ofFn_succ,
      List.ofFn_zero, Fin.succ_zero_eq_one, M, Matrix.mul_assoc] using
        Matrix.trace_mul_comm (A (σ 1) * M) (A (σ 0))
  apply uncleInteractionES_apply_eq_zero_left
  rw [mem_groundSpaceES_iff, LinearEquiv.apply_symm_apply, hfun]
  exact ⟨M, rfl⟩

/-- Every actual cyclic local projector vanishes on the source trial away
from its four interval-end bonds. This includes the periodic A/A bond.
No perturbation injectivity or normalization is assumed. Source:
arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_cyclicRestrict_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1))
    (hi : i ∉ uncleTrialEndpointBonds N hN) (τ : Cfg d (6 * N + 1)) :
    uncleInteractionES A B R L
      (cyclicRestrictES (Fin.pos i) 2 i τ
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N))) = 0 := by
  have hidx : i.val ≠ N - 1 ∧ i.val ≠ 2 * N ∧
      i.val ≠ 4 * N - 1 ∧ i.val ≠ 5 * N := by
    simpa only [uncleTrialEndpointBonds, Finset.mem_insert, Finset.mem_singleton,
      not_or, Fin.ext_iff] using hi
  change uncleInteractionES A B R L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (Fin.pos i) 2 i τ (uncleTwoWallTrialSource A B R L N))) = 0
  by_cases hlast : i.val = 6 * N
  · have heq : i = ⟨6 * N, by omega⟩ := Fin.ext hlast
    rw [heq]
    exact uncleTrial_wrap_cancel A B R L N hN τ
  · have hbound : i.val + 2 ≤ 6 * N + 1 := by omega
    rw [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) (by omega) hbound]
    exact uncleTrial_contiguous_cancel A B R L N hN i.val hbound
      hidx.1 hidx.2.1 hidx.2.2.1 hidx.2.2.2 τ

/-- The actual finite uncle Hamiltonian applied to the source trial is
exactly the sum of its four endpoint contributions. This is a finite
identity, without an energy estimate or supplied support condition.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleHamiltonianES_trial_eq_sum_endpoints
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) :
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleHamiltonianES A B R L (6 * N + 1) φ =
      ∑ i ∈ uncleTrialEndpointBonds N hN, (((d ^ 2 : ℕ) : ℂ)⁻¹) •
        ∑ τ : Cfg d (6 * N + 1), (cyclicRestrictES (Fin.pos i) 2 i τ).adjoint
          (uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ φ)) := by
  dsimp only
  calc
    _ = ∑ i : Fin (6 * N + 1), (((d ^ 2 : ℕ) : ℂ)⁻¹) •
        ∑ τ : Cfg d (6 * N + 1), (cyclicRestrictES (Fin.pos i) 2 i τ).adjoint
          (uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ
            ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
              (uncleTwoWallTrialSource A B R L N)))) := by
      simp [uncleHamiltonianES]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp_rw [uncleInteractionES_trial_cyclicRestrict_eq_zero A B R L N hN i hi]
      simp

end MPSTensor
