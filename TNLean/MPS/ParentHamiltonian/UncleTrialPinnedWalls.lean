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

open scoped Matrix BigOperators

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
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_assoc] at hkill
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
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
      (P * uncleDomainWallWord A B R u) (B (σ 0) * B (σ 1) * Q)
  have hkill := uncleInteractionES_uniform_slice_right_eq_zero A B R L 1
    (Q * P * uncleDomainWallWord A B R u) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.one_mul] at hkill
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
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_assoc] at hkill
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
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
      (P * uncleDomainWallWord B A L u) (A (σ 0) * A (σ 1) * Q)
  have hkill := uncleInteractionES_uniform_slice_left_eq_zero A B R L 1
    (Q * P * uncleDomainWallWord B A L u) [] []
  simp only [List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.one_mul] at hkill
  simp only [Matrix.mul_assoc] at hfun hkill ⊢
  rw [hfun, map_add, map_add, hkill, add_zero]

private theorem uncleConfigSegment_contiguous_end {T : ℕ}
    (τ : Cfg d T) (s n i : ℕ) (hs : s + n ≤ T) (hn : 0 < n)
    (hi : s + n = i + 1) (σ : Cfg d 2) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) s n hs =
      uncleConfigSegment τ s (n - 1) (by omega) ++ [σ 0] := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show n = (n - 1) + 1 by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext j
    exact dif_neg (by omega)
  · simp only [List.ofFn_succ, List.ofFn_zero]
    congr 1
    rw [contiguousCfg, dif_pos (by omega)]
    apply congrArg σ
    exact Fin.ext (by change s + (n - 1) - i = 0; omega)

private theorem uncleConfigSegment_contiguous_start {T : ℕ}
    (τ : Cfg d T) (n i : ℕ) (hs : i + 1 + n ≤ T) (hn : 0 < n) (σ : Cfg d 2) :
    uncleConfigSegment (contiguousCfg i 2 σ τ) (i + 1) n hs =
      [σ 1] ++ uncleConfigSegment τ (i + 2) (n - 1) (by omega) := by
  unfold uncleConfigSegment
  rw [List.ofFn_congr (show n = 1 + (n - 1) by omega), List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · simp only [List.ofFn_succ, List.ofFn_zero, Nat.add_zero]
    congr 1
    rw [contiguousCfg, dif_pos (by omega)]
    apply congrArg σ
    exact Fin.ext (by change i + 1 - i = 1; omega)
  · apply congrArg List.ofFn
    funext j
    rw [contiguousCfg, dif_neg (by omega)]
    apply congrArg τ
    exact Fin.ext (by change i + 1 + (1 + j.val) = i + 2 + j.val; omega)

end MPSTensor
