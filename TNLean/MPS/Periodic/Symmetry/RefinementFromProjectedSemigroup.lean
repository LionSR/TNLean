/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.InjectivePositiveMapRank
import QICLean.Channel.Semigroup.LindbladForm.GKSLTheorem
import QICLean.Channel.Schwarz.Closure
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Bounded roots of projected channel semigroups

Let `P` be an idempotent channel commuting with a GKSL generator `L`.
Every channel `exp(tL) P`, for `t ≥ 0`, has the explicit channel root
`exp((t/p)L) P`, whose Choi rank is at most the target's Choi rank.
This includes singular nonunital targets in arbitrary dimension.

The projection-semigroup representation is an explicit restriction relative
to arXiv:1708.00029, Theorem 4.1, converse. No representation theorem for
general divisible channels is asserted; see
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix

private theorem expSemigroup_injective {D : ℕ}
    (L : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (t : ℝ) :
    Function.Injective (expSemigroup L t) := by
  have hleft : expSemigroup L (-t) * expSemigroup L t = 1 := by
    change (expSemigroup L (-t)).comp (expSemigroup L t) = LinearMap.id
    rw [← expSemigroup_comp, neg_add_cancel, expSemigroup_zero]
  have hInv : Function.LeftInverse (expSemigroup L (-t)) (expSemigroup L t) := by
    intro X
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => T X) hleft
  exact hInv.injective

private theorem commute_expSemigroup {D : ℕ}
    {P L : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hComm : Commute P L) (t : ℝ) : Commute P (expSemigroup L t) := by
  have hCLM : Commute (endEquiv P) (endEquiv L) := by
    change endEquiv P * endEquiv L = endEquiv L * endEquiv P
    simpa only [map_mul] using congrArg endEquiv hComm.eq
  change P * expSemigroup L t = expSemigroup L t * P
  apply endEquiv.injective
  simp only [map_mul, expSemigroup_toCLM]
  exact (hCLM.smul_right (t : ℂ)).exp_right.eq

private theorem expSemigroup_pow {D : ℕ}
    (L : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (t : ℝ) (n : ℕ) :
    expSemigroup L t ^ n = expSemigroup L ((n : ℝ) * t) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, expSemigroup_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change (expSemigroup L ((n : ℝ) * t)).comp (expSemigroup L t) = _
    rw [← expSemigroup_comp]
    congr 1
    push_cast
    ring

namespace Channel

/-- Choi rank cannot decrease along a channel semigroup after any fixed
completely positive map. The fixed map may be singular and nonunital.
This supports the bounded-root step in arXiv:1708.00029, Theorem 4.1. -/
theorem choiRank_comp_expSemigroup_mono {D : ℕ}
    {L P : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hL : IsGKSLGenerator L) (hP : IsCPMap P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    choiRank (expSemigroup L s * P) ≤ choiRank (expSemigroup L t * P) := by
  have hComp : expSemigroup L (t - s) ∘ₗ (expSemigroup L s * P) =
      expSemigroup L t * P := by
    change expSemigroup L (t - s) * (expSemigroup L s * P) = _
    rw [← mul_assoc]
    change (expSemigroup L (t - s)).comp (expSemigroup L s) * P = _
    rw [← expSemigroup_comp, sub_add_cancel]
  have hRank := choiRank_le_comp_of_injective
    (F := expSemigroup L (t - s)) (G := expSemigroup L s * P)
    (hL (t - s) (sub_nonneg.mpr hst)).cp
    ((hL s hs).cp.comp hP) (expSemigroup_injective L (t - s))
  rwa [hComp] at hRank

/-- A commuting channel projection followed by Markovian evolution has a
channel root with Choi rank at most that of the target, for every positive
integer exponent. The projection-semigroup representation is an explicit
restriction relative to arXiv:1708.00029, Theorem 4.1, converse; no unitality,
irreducibility, or invertibility of the target is assumed. -/
theorem exists_root_choiRank_le_of_projected_semigroup {D : ℕ}
    {L P : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hL : IsGKSLGenerator L) (hP : IsChannel P) (hIdem : P * P = P)
    (hComm : Commute P L) {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : 0 < p) :
    ∃ F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      IsChannel F ∧ F ^ p = expSemigroup L t * P ∧
        choiRank F ≤ choiRank (expSemigroup L t * P) := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hOne : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hs : 0 ≤ t / p := div_nonneg ht hpReal.le
  have hst : t / p ≤ t := by
    apply (div_le_iff₀ hpReal).mpr
    nlinarith
  let F := expSemigroup L (t / p) * P
  have hF : IsChannel F :=
    ⟨(hL (t / p) hs).cp.comp hP.cp, (hL (t / p) hs).tp.comp hP.tp⟩
  have hPowPall (n : ℕ) : P ^ (n + 1) = P := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hIdem]
  have hPowP : P ^ p = P := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    exact hPowPall n
  have hPow : F ^ p = expSemigroup L t * P := by
    change (expSemigroup L (t / p) * P) ^ p = _
    rw [(commute_expSemigroup hComm (t / p)).symm.mul_pow,
      expSemigroup_pow, hPowP]
    have hTime : (p : ℝ) * (t / p) = t := by field_simp [ne_of_gt hpReal]
    rw [hTime]
  exact ⟨F, hF, hPow, choiRank_comp_expSemigroup_mono hL hP.cp hs hst⟩

end Channel

namespace MPSTensor

/-- Every tensor whose transfer map is a commuting channel projection
followed by Markovian evolution is refinable for every positive exponent,
on its original physical alphabet. The projection-semigroup representation
is an explicit restriction relative to arXiv:1708.00029, Theorem 4.1;
singular nonunital targets and arbitrary bond dimensions are allowed. -/
theorem isPRefinable_of_projected_semigroup_transfer {d D p : ℕ}
    (B : MPSTensor d D) (hp : 0 < p)
    {L P : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hL : IsGKSLGenerator L) (hP : IsChannel P) (hIdem : P * P = P)
    (hComm : Commute P L) {t : ℝ} (ht : 0 ≤ t)
    (hB : Kraus.transferMap B = expSemigroup L t * P) : IsPRefinable B p := by
  obtain ⟨F, hF, hPow, hRank⟩ :=
    Channel.exists_root_choiRank_le_of_projected_semigroup hL hP hIdem hComm ht hp
  have hBound : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (expSemigroup L t * P) := hRank
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hB.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F (hB.trans hPow.symm)
    ⟨Channel.choiRank F, hBound, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor
