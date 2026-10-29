/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveApproximation
import TNLean.MPS.AreaLaw.ViableSet.PrefixMPS

/-!
# Arbitrary accuracy with a uniform polynomial degree

Fix the local dimension and a positive lower bound for the original gap.
Product-state padding caps that lower bound at one and increases the chain
length from `L` to `L + 2 R²`. Apply the same successive viable-set construction
to this actual interaction, before choosing any ground pair. A normalized
column of its stage-`L` witness, with its phase chosen, remains in the actual
retained stage-`L` span and has squared error at most `R⁻²`.

The natural polynomial coefficient and degree are chosen before both `L` and
`R`. No independent MPS existence theorem or computational running-time bound
is used.

This product-ancilla argument is a consequence of the proved LVV13
construction (arXiv:1307.5143v1, `algo53.tex`, final successive induction,
lines 652--678), rather than a claim that padding appears in the source.
The underlying construction retains the trimming corrections and Gaussian
error-reduction scope documented in `SuccessiveApproximation`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The capped-gap successive error is strictly below one. -/
theorem lvvSuccessiveError_min_lt_one {Delta : ℝ} (hDelta : 0 < Delta) :
    lvvSuccessiveError (min Delta 1) < 1 := by
  have hpos : 0 ≤ min Delta 1 := le_min hDelta.le zero_le_one
  have hle : min Delta 1 ≤ 1 := min_le_right _ _
  unfold lvvSuccessiveError
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr hle)]

/-- A single uniform natural polynomial bounds a padded successive run and an
arbitrarily accurate original-chain MPS in its actual retained prefix span.
The families are selected before the original ground energy and vector. -/
theorem exists_uniform_positive_chain_successive_accuracy {q : ℕ} (hq : 2 ≤ q)
    {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ L : ℕ, 1 ≤ L → ∀ R : ℕ, 1 ≤ R →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j.val (j.val + 2))) (_h0 : ∀ j, 0 ≤ h j) (_h1 : ∀ j, h j ≤ 1),
      let N := L + 2 * R ^ 2
      let hi : L ≤ N := Nat.le_add_right _ _
      let z : Fin q := ⟨0, by omega⟩
      ∃ S : (i : ℕ) → Finset (LeftBlockVector N q i),
        S 0 = {emptyLeftVector N q} ∧
        (∀ i : ℕ, i ≤ N → (S i).card ≤ P * (N + 1) ^ d ∧
          (∀ v ∈ S i, IsLeftOpenMPS (P * (N + 1) ^ d) v) ∧
          ∀ (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
            IsGappedGroundState (∑ j, h j) E Γ Delta →
            IsViable (paddedGroundVector hi z Γ)
              (lvvSuccessiveError (min Delta 1) / N) (S i : Set (LeftBlockVector N q i))) ∧
        ∀ (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          IsGappedGroundState (∑ j, h j) E Γ Delta →
          ∃ w ∈ Submodule.span ℂ (S L : Set (LeftBlockVector N q L)), ‖w‖ = 1 ∧
            ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)).symm w - Γ‖ ^ 2 ≤
              1 / (R : ℝ) ^ 2 ∧
            IsOpenMPS L q (P * (N + 1) ^ d) (fun x ↦ w (leftConfigOfFin x)) := by
  classical
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  obtain ⟨P, d, hP, hrun⟩ := exists_uniform_positive_chain_successive_approximation hq hg
  refine ⟨P ^ 2, 2 * d, by nlinarith, ?_⟩
  intro L hL R hR h hs h0 h1
  dsimp only
  let N := L + 2 * R ^ 2
  have hi : L ≤ N := Nat.le_add_right _ _
  have hN : 1 ≤ N := hL.trans hi
  let z : Fin q := ⟨0, by omega⟩
  obtain ⟨S, hS0, hS, _⟩ := hrun N hN (paddedInteraction hi z h)
    (paddedInteraction_supported hi z h hs)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2)
  let B := P * (N + 1) ^ d
  have hB : 1 ≤ B := by
    simpa only [one_mul] using Nat.mul_le_mul hP (Nat.one_le_pow' d N)
  have hbudget : P ^ 2 * (N + 1) ^ (2 * d) = B ^ 2 := by
    simp only [B, mul_pow, pow_mul, mul_comm 2 d]
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : lvvSuccessiveError (min Delta 1) / N < 1 := by
    apply (div_lt_one hNreal).mpr
    exact (lvvSuccessiveError_min_lt_one hDelta).trans_le (by exact_mod_cast hN)
  refine ⟨S, hS0, ?_, ?_⟩
  · intro i hiN
    obtain ⟨hcard, hmps, hviable⟩ := hS i hiN
    refine ⟨hcard.trans (hBB.trans_eq hbudget.symm), ?_, ?_⟩
    · intro v hv
      exact (hmps v hv).mono (max_le_max le_rfl (hBB.trans_eq hbudget.symm))
    · intro E Γ hgs
      exact hviable E (paddedGroundVector hi z Γ)
        (isGappedGroundState_paddedInteraction hL hi z h hgs hDelta)
  · intro E Γ hgs
    obtain ⟨hcard, hmps, hviable⟩ := hS L hi
    have hpad := isGappedGroundState_paddedInteraction hL hi z h hgs hDelta
    obtain ⟨w, hw, hwnorm, herror, hmpsw⟩ :=
      (hviable E _ hpad).exists_prefix_mps_of_paddedGroundVector hi z hgs.1 hδ hmps
    refine ⟨w, hw, hwnorm, ?_, hmpsw.mono ?_⟩
    · have hRreal : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast (show 0 < R by omega))
      have hNR : 2 * (R : ℝ) ^ 2 ≤ N := by
        exact_mod_cast (show 2 * R ^ 2 ≤ N from Nat.le_add_left _ _)
      have hsmall : 2 * (lvvSuccessiveError (min Delta 1) / N) ≤ 1 / (R : ℝ) ^ 2 := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ hNreal hRreal).mpr
        have hc := mul_le_mul_of_nonneg_right (lvvSuccessiveError_min_lt_one hDelta).le
          hRreal.le
        nlinarith
      exact herror.trans hsmall
    · rw [hbudget, max_eq_right hB]
      exact (Nat.mul_le_mul_right B hcard).trans_eq (pow_two B).symm

end TNLean.MPS.AreaLaw
