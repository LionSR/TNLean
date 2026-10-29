/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialEnergy

/-!
# Pinned-wall endpoint residuals

At an endpoint of a moving interval, the actual local uncle projector kills
the contribution in which the wall lies elsewhere. The remaining wall is
pinned to the endpoint physical site. The opposite moving interval retains
its actual one-wall sum, as needed for the source linear-energy estimate.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
No norm growth or asymptotic energy estimate is supplied as a premise.
-/

noncomputable section

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d a b : ℕ}

/-- At the left R endpoint only the wall at the second local site survives.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_pin_upper_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin b) (Fin a) ℂ)
    (v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * A (σ 0) *
        uncleDomainWallWord A B R (σ 1 :: v) * Q))) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (P * A (σ 0) * R (σ 1) * Kraus.evalWord B v * Q))) := by
  have hfun :
      (fun σ : Cfg d 2 ↦ Matrix.trace
        (P * A (σ 0) * uncleDomainWallWord A B R (σ 1 :: v) * Q)) =
      (fun σ ↦ Matrix.trace (P * A (σ 0) * A (σ 1) *
        uncleDomainWallWord A B R v * Q)) +
      (fun σ ↦ Matrix.trace (P * A (σ 0) * R (σ 1) * Kraus.evalWord B v * Q)) := by
    funext σ
    simp [uncleDomainWallWord, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
      Matrix.mul_assoc]
  have hkill := uncleInteractionES_uniform_slice_left_eq_zero A B R L P
    (uncleDomainWallWord A B R v * Q) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Fin.succ_zero_eq_one,
    Matrix.mul_assoc] at hkill
  simp only [Matrix.mul_assoc] at hfun hkill ⊢
  rw [hfun, map_add, map_add, hkill, zero_add]

/-- At the right R endpoint only the wall at the first local site survives.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_pin_upper_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin b) (Fin a) ℂ)
    (u : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * uncleDomainWallWord A B R (u ++ [σ 0]) *
        B (σ 1) * Q))) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (P * Kraus.evalWord A u * R (σ 0) * B (σ 1) * Q))) := by
  have hfun :
      (fun σ : Cfg d 2 ↦ Matrix.trace (P * uncleDomainWallWord A B R (u ++ [σ 0]) *
        B (σ 1) * Q)) =
      (fun σ ↦ Matrix.trace (P * Kraus.evalWord A u * R (σ 0) * B (σ 1) * Q)) +
      (fun σ ↦ Matrix.trace (B (σ 0) * B (σ 1) *
        (Q * P * uncleDomainWallWord A B R u))) := by
    funext σ
    rw [uncleDomainWallWord_append]
    simp only [uncleDomainWallWord, Kraus.evalWord_cons, Kraus.evalWord_nil,
      Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add]
    simpa only [Matrix.mul_assoc] using congrArg
      (fun z : ℂ ↦ Matrix.trace
        (P * Kraus.evalWord A u * R (σ 0) * B (σ 1) * Q) + z)
      (Matrix.trace_mul_comm
        (P * uncleDomainWallWord A B R u) (B (σ 0) * B (σ 1) * Q))
  have hkill := uncleInteractionES_uniform_slice_right_eq_zero A B R L 1
    (Q * P * uncleDomainWallWord A B R u) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.one_mul,
    Fin.succ_zero_eq_one] at hkill
  simp only [Matrix.mul_assoc] at hfun hkill ⊢
  rw [hfun, map_add, map_add, hkill, add_zero]

/-- At the left L endpoint only the wall at the second local site survives.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_pin_lower_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ)
    (v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * B (σ 0) *
        uncleDomainWallWord B A L (σ 1 :: v) * Q))) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (P * B (σ 0) * L (σ 1) * Kraus.evalWord A v * Q))) := by
  have hfun :
      (fun σ : Cfg d 2 ↦ Matrix.trace
        (P * B (σ 0) * uncleDomainWallWord B A L (σ 1 :: v) * Q)) =
      (fun σ ↦ Matrix.trace (P * B (σ 0) * B (σ 1) *
        uncleDomainWallWord B A L v * Q)) +
      (fun σ ↦ Matrix.trace (P * B (σ 0) * L (σ 1) * Kraus.evalWord A v * Q)) := by
    funext σ
    simp [uncleDomainWallWord, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
      Matrix.mul_assoc]
  have hkill := uncleInteractionES_uniform_slice_right_eq_zero A B R L P
    (uncleDomainWallWord B A L v * Q) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Fin.succ_zero_eq_one,
    Matrix.mul_assoc] at hkill
  simp only [Matrix.mul_assoc] at hfun hkill ⊢
  rw [hfun, map_add, map_add, hkill, zero_add]

/-- At the right L endpoint only the wall at the first local site survives.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_pin_lower_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ)
    (u : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * uncleDomainWallWord B A L (u ++ [σ 0]) *
        A (σ 1) * Q))) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (P * Kraus.evalWord B u * L (σ 0) * A (σ 1) * Q))) := by
  have hfun :
      (fun σ : Cfg d 2 ↦ Matrix.trace (P * uncleDomainWallWord B A L (u ++ [σ 0]) *
        A (σ 1) * Q)) =
      (fun σ ↦ Matrix.trace (P * Kraus.evalWord B u * L (σ 0) * A (σ 1) * Q)) +
      (fun σ ↦ Matrix.trace (A (σ 0) * A (σ 1) *
        (Q * P * uncleDomainWallWord B A L u))) := by
    funext σ
    rw [uncleDomainWallWord_append]
    simp only [uncleDomainWallWord, Kraus.evalWord_cons, Kraus.evalWord_nil,
      Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add]
    simpa only [Matrix.mul_assoc] using congrArg
      (fun z : ℂ ↦ Matrix.trace
        (P * Kraus.evalWord B u * L (σ 0) * A (σ 1) * Q) + z)
      (Matrix.trace_mul_comm
        (P * uncleDomainWallWord B A L u) (A (σ 0) * A (σ 1) * Q))
  have hkill := uncleInteractionES_uniform_slice_left_eq_zero A B R L 1
    (Q * P * uncleDomainWallWord B A L u) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.one_mul,
    Fin.succ_zero_eq_one] at hkill
  simp only [Matrix.mul_assoc] at hfun hkill ⊢
  rw [hfun, map_add, map_add, hkill, add_zero]

/-- A pair crossing the end of a numbered segment varies only its final letter. -/
theorem uncleConfigSegment_contiguous_end {T : ℕ}
    (τ : Cfg d T) (s n i : ℕ) (hs : s + n ≤ T) (hn : 0 < n)
    (hi : s + n = i + 1) (σ : Cfg d 2) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) s n hs =
      uncleConfigSegment τ s (n - 1) (by omega) ++ [σ 0] := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show n = (n - 1) + 1 by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext j
    change contiguousCfg i 2 σ τ ⟨s + j.val, by omega⟩ = τ ⟨s + j.val, by omega⟩
    rw [contiguousCfg, dite_eq_right (by
      change ¬(i ≤ s + j.val ∧ s + j.val < i + 2)
      omega)]
  · simp only [List.ofFn_succ, List.ofFn_zero]
    congr 1
    change contiguousCfg i 2 σ τ ⟨s + (n - 1), by omega⟩ = σ 0
    rw [contiguousCfg, dite_eq_left (by
      change i ≤ s + (n - 1) ∧ s + (n - 1) < i + 2
      omega)]
    apply congrArg σ
    exact Fin.ext (by change s + (n - 1) - i = 0; omega)

/-- A pair crossing the start of a numbered segment varies only its first letter. -/
theorem uncleConfigSegment_contiguous_start {T : ℕ}
    (τ : Cfg d T) (s n i : ℕ) (hs : s + n ≤ T) (hn : 0 < n)
    (hi : s = i + 1) (σ : Cfg d 2) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) s n hs =
      [σ 1] ++ uncleConfigSegment τ (i + 2) (n - 1) (by omega) := by
  subst s
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show n = 1 + (n - 1) by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · simp only [List.ofFn_succ, List.ofFn_zero]
    congr 1
    change contiguousCfg i 2 σ τ ⟨i + 1, by omega⟩ = σ 1
    rw [contiguousCfg, dite_eq_left (by
      change i ≤ i + 1 ∧ i + 1 < i + 2
      omega)]
    apply congrArg σ
    exact Fin.ext (by change i + 1 - i = 1; omega)
  · apply congrArg List.ofFn
    funext j
    change contiguousCfg i 2 σ τ ⟨i + 1 + (1 + j.val), by omega⟩ =
      τ ⟨i + 2 + j.val, by omega⟩
    rw [contiguousCfg, dite_eq_right (by
      change ¬(i ≤ i + 1 + (1 + j.val) ∧ i + 1 + (1 + j.val) < i + 2)
      omega)]
    apply congrArg τ
    exact Fin.ext (by change i + 1 + (1 + j.val) = i + 2 + j.val; omega)

/-- The actual first endpoint residual pins the R wall at site N and
retains precisely the source L-wall sum in the other interval.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_pin_first_endpoint
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) :
    let p := uncleConfigSegment τ 0 (N - 1) (by omega)
    let r := uncleConfigSegment τ (N + 1) N (by omega)
    let w := uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)
    let x := uncleConfigSegment τ (4 * N) (N + 1) (by omega)
    let y := uncleConfigSegment τ (5 * N + 1) N (by omega)
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleInteractionES A B R L
        (cyclicRestrictES (by omega) 2 (⟨N - 1, by omega⟩ : Fin (6 * N + 1)) τ φ) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (Kraus.evalWord A p * A (σ 0) * R (σ 1) *
          Kraus.evalWord B r * Kraus.evalWord B w *
          uncleDomainWallWord B A L x * Kraus.evalWord A y))) := by
  dsimp only
  change uncleInteractionES A B R L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (by omega) 2 (⟨N - 1, by omega⟩ : Fin (6 * N + 1)) τ
        (uncleTwoWallTrialSource A B R L N))) = _
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ
    (i := (⟨N - 1, by omega⟩ : Fin (6 * N + 1))) (L := 2)
    (by omega) (by omega) (by change N - 1 + 2 ≤ 6 * N + 1; omega)]
  have hfun : contiguousRestrictₗ (N - 1) 2 (by omega) τ
      (uncleTwoWallTrialSource A B R L N) =
      fun σ ↦ uncleTwoWallCoefficient A B R L
        (uncleConfigSegment τ 0 (N - 1) (by omega) ++ [σ 0])
        (σ 1 :: uncleConfigSegment τ (N + 1) N (by omega))
        (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
        (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
        (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
    funext σ
    simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
    rw [uncleConfigSegment_contiguous_end τ 0 N (N - 1) _ hN (by omega) σ,
      uncleConfigSegment_contiguous_start τ N (N + 1) (N - 1) _ (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) (N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) (N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (5 * N + 1) N (N - 1) _ σ (by omega)]
    simp only [show N - 1 + 2 = N + 1 by omega, Nat.add_sub_cancel_right, List.singleton_append]
  rw [hfun]
  simpa only [uncleTwoWallCoefficient, Kraus.evalWord_append, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_assoc] using
      uncleInteractionES_pin_upper_left A B R L
        (Kraus.evalWord A (uncleConfigSegment τ 0 (N - 1) (by omega)))
        (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
          uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
          Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)))
        (uncleConfigSegment τ (N + 1) N (by omega))

/-- The actual second endpoint residual pins the R wall at site 2N and
retains precisely the source L-wall sum in the other interval.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_pin_second_endpoint
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) :
    let p := uncleConfigSegment τ 0 N (by omega)
    let r := uncleConfigSegment τ N N (by omega)
    let w := uncleConfigSegment τ (2 * N + 2) (2 * N - 2) (by omega)
    let x := uncleConfigSegment τ (4 * N) (N + 1) (by omega)
    let y := uncleConfigSegment τ (5 * N + 1) N (by omega)
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleInteractionES A B R L
        (cyclicRestrictES (by omega) 2 (⟨2 * N, by omega⟩ : Fin (6 * N + 1)) τ φ) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (Kraus.evalWord A p * Kraus.evalWord A r * R (σ 0) *
          B (σ 1) * Kraus.evalWord B w *
          uncleDomainWallWord B A L x * Kraus.evalWord A y))) := by
  dsimp only
  change uncleInteractionES A B R L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (by omega) 2 (⟨2 * N, by omega⟩ : Fin (6 * N + 1)) τ
        (uncleTwoWallTrialSource A B R L N))) = _
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ
    (i := (⟨2 * N, by omega⟩ : Fin (6 * N + 1))) (L := 2)
    (by omega) (by omega) (by change 2 * N + 2 ≤ 6 * N + 1; omega)]
  have hfun : contiguousRestrictₗ (2 * N) 2 (by omega) τ
      (uncleTwoWallTrialSource A B R L N) =
      fun σ ↦ uncleTwoWallCoefficient A B R L
        (uncleConfigSegment τ 0 N (by omega))
        (uncleConfigSegment τ N N (by omega) ++ [σ 0])
        (σ 1 :: uncleConfigSegment τ (2 * N + 2) (2 * N - 2) (by omega))
        (uncleConfigSegment τ (4 * N) (N + 1) (by omega))
        (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
    funext σ
    simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
    rw [uncleConfigSegment_contiguous_end τ N (N + 1) (2 * N) _ (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (2 * N + 1) (2 * N - 1) (2 * N) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ 0 N (2 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (4 * N) (N + 1) (2 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (5 * N + 1) N (2 * N) _ σ (by omega)]
    simp only [show (2 * N - 1) - 1 = 2 * N - 2 by omega,
      Nat.add_sub_cancel_right, List.singleton_append]
  rw [hfun]
  simpa only [uncleTwoWallCoefficient, Kraus.evalWord_cons, Matrix.mul_assoc] using
    uncleInteractionES_pin_upper_right A B R L
      (Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)))
      (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 2) (2 * N - 2) (by omega)) *
        uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)))
      (uncleConfigSegment τ N N (by omega))

/-- The actual third endpoint residual pins the L wall at site 4N and
retains precisely the source R-wall sum, after the rectangular trace rotation.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_pin_third_endpoint
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) :
    let p := uncleConfigSegment τ 0 N (by omega)
    let r := uncleConfigSegment τ N (N + 1) (by omega)
    let w := uncleConfigSegment τ (2 * N + 1) (2 * N - 2) (by omega)
    let x := uncleConfigSegment τ (4 * N + 1) N (by omega)
    let y := uncleConfigSegment τ (5 * N + 1) N (by omega)
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleInteractionES A B R L
        (cyclicRestrictES (by omega) 2 (⟨4 * N - 1, by omega⟩ : Fin (6 * N + 1)) τ φ) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (Kraus.evalWord B w * B (σ 0) * L (σ 1) *
          Kraus.evalWord A x * Kraus.evalWord A y * Kraus.evalWord A p *
          uncleDomainWallWord A B R r))) := by
  dsimp only
  change uncleInteractionES A B R L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (by omega) 2 (⟨4 * N - 1, by omega⟩ : Fin (6 * N + 1)) τ
        (uncleTwoWallTrialSource A B R L N))) = _
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ
    (i := (⟨4 * N - 1, by omega⟩ : Fin (6 * N + 1))) (L := 2)
    (by omega) (by omega) (by change 4 * N - 1 + 2 ≤ 6 * N + 1; omega)]
  have hfun : contiguousRestrictₗ (4 * N - 1) 2 (by omega) τ
      (uncleTwoWallTrialSource A B R L N) =
      fun σ ↦ uncleTwoWallCoefficient A B R L
        (uncleConfigSegment τ 0 N (by omega))
        (uncleConfigSegment τ N (N + 1) (by omega))
        (uncleConfigSegment τ (2 * N + 1) (2 * N - 2) (by omega) ++ [σ 0])
        (σ 1 :: uncleConfigSegment τ (4 * N + 1) N (by omega))
        (uncleConfigSegment τ (5 * N + 1) N (by omega)) := by
    funext σ
    simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
    rw [uncleConfigSegment_contiguous_end τ (2 * N + 1) (2 * N - 1) (4 * N - 1) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (4 * N) (N + 1) (4 * N - 1) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_outside τ 0 N (4 * N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ N (N + 1) (4 * N - 1) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (5 * N + 1) N (4 * N - 1) _ σ (by omega)]
    simp only [show (2 * N - 1) - 1 = 2 * N - 2 by omega,
      show 4 * N - 1 + 2 = 4 * N + 1 by omega, Nat.add_sub_cancel_right, List.singleton_append]
  rw [hfun]
  simpa only [uncleTwoWallCoefficient_rotate, Kraus.evalWord_append, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_assoc] using
      uncleInteractionES_pin_lower_left A B R L
        (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 2) (by omega)))
        (Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)) *
          Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
          uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)))
        (uncleConfigSegment τ (4 * N + 1) N (by omega))

/-- The actual fourth endpoint residual pins the L wall at site 5N and
retains precisely the source R-wall sum, after the rectangular trace rotation.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_pin_fourth_endpoint
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (τ : Cfg d (6 * N + 1)) :
    let p := uncleConfigSegment τ 0 N (by omega)
    let r := uncleConfigSegment τ N (N + 1) (by omega)
    let w := uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)
    let x := uncleConfigSegment τ (4 * N) N (by omega)
    let y := uncleConfigSegment τ (5 * N + 2) (N - 1) (by omega)
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleInteractionES A B R L
        (cyclicRestrictES (by omega) 2 (⟨5 * N, by omega⟩ : Fin (6 * N + 1)) τ φ) =
      uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
        (fun σ ↦ Matrix.trace (Kraus.evalWord B w * Kraus.evalWord B x * L (σ 0) *
          A (σ 1) * Kraus.evalWord A y * Kraus.evalWord A p *
          uncleDomainWallWord A B R r))) := by
  dsimp only
  change uncleInteractionES A B R L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (cyclicRestrictₗ (by omega) 2 (⟨5 * N, by omega⟩ : Fin (6 * N + 1)) τ
        (uncleTwoWallTrialSource A B R L N))) = _
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ
    (i := (⟨5 * N, by omega⟩ : Fin (6 * N + 1))) (L := 2)
    (by omega) (by omega) (by change 5 * N + 2 ≤ 6 * N + 1; omega)]
  have hfun : contiguousRestrictₗ (5 * N) 2 (by omega) τ
      (uncleTwoWallTrialSource A B R L N) =
      fun σ ↦ uncleTwoWallCoefficient A B R L
        (uncleConfigSegment τ 0 N (by omega))
        (uncleConfigSegment τ N (N + 1) (by omega))
        (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega))
        (uncleConfigSegment τ (4 * N) N (by omega) ++ [σ 0])
        (σ 1 :: uncleConfigSegment τ (5 * N + 2) (N - 1) (by omega)) := by
    funext σ
    simp only [contiguousRestrictₗ_apply, uncleTwoWallTrialSource]
    rw [uncleConfigSegment_contiguous_end τ (4 * N) (N + 1) (5 * N) _
        (by omega) (by omega) σ,
      uncleConfigSegment_contiguous_start τ (5 * N + 1) N (5 * N) _ hN (by omega) σ,
      uncleConfigSegment_contiguous_outside τ 0 N (5 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ N (N + 1) (5 * N) _ σ (by omega),
      uncleConfigSegment_contiguous_outside τ (2 * N + 1) (2 * N - 1) (5 * N) _ σ (by omega)]
    simp only [Nat.add_sub_cancel_right, List.singleton_append]
  rw [hfun]
  simpa only [uncleTwoWallCoefficient_rotate, Kraus.evalWord_cons, Matrix.mul_assoc] using
    uncleInteractionES_pin_lower_right A B R L
      (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)))
      (Kraus.evalWord A (uncleConfigSegment τ (5 * N + 2) (N - 1) (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
        uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)))
      (uncleConfigSegment τ (4 * N) N (by omega))

/-- The four explicit pinned-wall local vectors. Outside the endpoint set
this vector is zero. Each endpoint contains only the opposite moving-wall
sum, with all its actual exterior physical coordinates retained.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
def uncleTrialPinnedEndpointState
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1)) (τ : Cfg d (6 * N + 1)) :
    EuclideanSpace ℂ (Cfg d 2) :=
  (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm fun σ ↦
    if i.val = N - 1 then
      Matrix.trace (Kraus.evalWord A (uncleConfigSegment τ 0 (N - 1) (by omega)) *
        A (σ 0) * R (σ 1) *
        Kraus.evalWord B (uncleConfigSegment τ (N + 1) N (by omega)) *
        Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
        uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)))
    else if i.val = 2 * N then
      Matrix.trace (Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ N N (by omega)) * R (σ 0) * B (σ 1) *
        Kraus.evalWord B (uncleConfigSegment τ (2 * N + 2) (2 * N - 2) (by omega)) *
        uncleDomainWallWord B A L (uncleConfigSegment τ (4 * N) (N + 1) (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)))
    else if i.val = 4 * N - 1 then
      Matrix.trace (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 2) (by omega)) *
        B (σ 0) * L (σ 1) *
        Kraus.evalWord A (uncleConfigSegment τ (4 * N + 1) N (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ (5 * N + 1) N (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
        uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)))
    else if i.val = 5 * N then
      Matrix.trace (Kraus.evalWord B (uncleConfigSegment τ (2 * N + 1) (2 * N - 1) (by omega)) *
        Kraus.evalWord B (uncleConfigSegment τ (4 * N) N (by omega)) * L (σ 0) * A (σ 1) *
        Kraus.evalWord A (uncleConfigSegment τ (5 * N + 2) (N - 1) (by omega)) *
        Kraus.evalWord A (uncleConfigSegment τ 0 N (by omega)) *
        uncleDomainWallWord A B R (uncleConfigSegment τ N (N + 1) (by omega)))
    else 0

/-- The actual endpoint restriction has exactly the projected pinned-wall
residual, with no supplied endpoint-support condition. Source:
arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem uncleInteractionES_trial_eq_pinnedEndpointState
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (i : Fin (6 * N + 1))
    (hi : i ∈ uncleTrialEndpointBonds N hN) (τ : Cfg d (6 * N + 1)) :
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ φ) =
      uncleInteractionES A B R L (uncleTrialPinnedEndpointState A B R L N hN i τ) := by
  have h01 : N - 1 < 2 * N := by omega
  have h12 : 2 * N < 4 * N - 1 := by omega
  have h23 : 4 * N - 1 < 5 * N := by omega
  have hcases : i = ⟨N - 1, by omega⟩ ∨ i = ⟨2 * N, by omega⟩ ∨
      i = ⟨4 * N - 1, by omega⟩ ∨ i = ⟨5 * N, by omega⟩ := by
    exact (mem_uncleTrialEndpointBonds_iff N hN i).mp hi
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa [uncleTrialPinnedEndpointState] using
      uncleInteractionES_trial_pin_first_endpoint A B R L N hN τ
  · simpa [uncleTrialPinnedEndpointState, ne_of_gt h01] using
      uncleInteractionES_trial_pin_second_endpoint A B R L N hN τ
  · simpa [uncleTrialPinnedEndpointState, ne_of_gt h12, ne_of_gt (h01.trans h12)] using
      uncleInteractionES_trial_pin_third_endpoint A B R L N hN τ
  · simpa [uncleTrialPinnedEndpointState, ne_of_gt h23, ne_of_gt (h12.trans h23),
      ne_of_gt (h01.trans (h12.trans h23))] using
      uncleInteractionES_trial_pin_fourth_endpoint A B R L N hN τ

/-- The actual trial energy is bounded by the four explicit one-moving-wall
endpoint norms, after deriving the removal of the other wall sum.
Estimating these actual finite norms is the remaining source asymptotic step;
no norm-growth or energy-rate premise is supplied here.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem re_inner_uncleHamiltonianES_trial_le_pinnedEndpoint_norms
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) :
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    (⟪uncleHamiltonianES A B R L (6 * N + 1) φ, φ⟫_ℂ).re ≤
      (((d ^ 2 : ℕ) : ℝ)⁻¹) * ∑ i ∈ uncleTrialEndpointBonds N hN,
        ∑ τ : Cfg d (6 * N + 1), ‖uncleTrialPinnedEndpointState A B R L N hN i τ‖ ^ 2 := by
  dsimp only
  rw [re_inner_uncleHamiltonianES_trial_eq_sum_endpoints A B R L N hN]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro τ _
  rw [uncleInteractionES_trial_eq_pinnedEndpointState A B R L N hN i hi τ]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_uncleInteractionES_apply_le A B R L _)

end MPSTensor
