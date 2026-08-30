/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.ZMod.Basic
import TNLean.Algebra.LSymbol
import TNLean.Algebra.ScalarThreeCocycleInversion

/-!
# Scalar three-cocycles for Z₂

This file proves the scalar part of the Z₂ anomaly calculation in
arXiv:2502.20257, Appendix `app:Z2`, lines 5207--5341. It identifies the
inversion scalar with a ratio of normalized L-symbols and classifies normalized
scalar three-cocycles on `Multiplicative (ZMod 2)` by their value at the
nonidentity generator.

The tensor identity following `eq:sigmadiag`, which relates this scalar to an
involutive dagger gauge, is not asserted here.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace LSymbol

/-- For normalized L-symbols, the inversion scalar is the ratio

`σ(g) = Lˣ_{g⁻¹,g} / L^{g • x}_{g,g⁻¹}`.

This is the scalar calculation after `eq:sigmadiag` in arXiv:2502.20257,
Appendix `app:Z2`, lines 5291--5295. -/
theorem sigma_eq_div {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hLn : IsNormalized L) (x : X) (g : G) :
    ScalarThreeCochain.sigma ω g = L x g⁻¹ g / L (g • x) g g⁻¹ := by
  have h := hL x g g⁻¹ g
  simp only [inv_mul_cancel, mul_inv_cancel, hLn.1, hLn.2, one_mul, mul_one] at h
  simp only [ScalarThreeCochain.sigma, div_eq_mul_inv, h]
  group

end LSymbol

namespace ScalarThreeCochain

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

private lemma z2_cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = s₂ := by
  revert g
  decide

private lemma z2Generator_inv : s₂⁻¹ = s₂ := by
  decide

private lemma z2Generator_mul_self : s₂ * s₂ = 1 := by
  decide

/-- A normalized scalar three-cochain on Z₂ has trivial gauge class exactly
when its inversion scalar at the nonidentity generator is one.

For the forward implication, the gauge two-cochain need not be normalized.
Normalization of its coboundary instead forces both identity-axis restrictions
to equal one common constant, by `isNormalized_coboundary_iff`; at the triple
of nonidentity elements this constant and the remaining self-pair factor
cancel. This is the direct two-element calculation underlying
arXiv:2502.20257, Appendix `app:Z2`, lines 5327--5341. -/
theorem isTrivialGaugeClass_iff_sigma_generator_eq_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hωn : IsNormalized ω) :
    IsTrivialGaugeClass ω ↔ sigma ω s₂ = 1 := by
  constructor
  · rintro ⟨β, hβ⟩
    have hcob : IsNormalized (coboundary β) := by
      rw [show coboundary β = ω by
        rw [← hβ]
        funext g h k
        simp only [fusionGauge, mul_one]]
      exact hωn
    obtain ⟨c, hleft, hright⟩ := (isNormalized_coboundary_iff β).1 hcob
    have hvalue := congrFun (congrFun (congrFun hβ s₂) s₂) s₂
    simp only [fusionGauge, coboundary, z2Generator_mul_self, hleft, hright,
      mul_one] at hvalue
    simp only [sigma, z2Generator_inv, ← hvalue]
    rw [mul_comm c]
    simp
  · intro hsigma
    have hω : ω = fun _ _ _ => 1 := by
      funext g h k
      rcases z2_cases g with rfl | rfl <;>
        rcases z2_cases h with rfl | rfl <;>
          rcases z2_cases k with rfl | rfl
      all_goals first
        | simp only [hωn.1, hωn.2.1, hωn.2.2]
        | simpa only [sigma, z2Generator_inv] using hsigma
    rw [hω]
    exact CohomologousTo.refl _

/-- The inversion scalar of a normalized scalar three-cocycle on Z₂ is either
one or minus one. This is the scalar sign dichotomy used in
arXiv:2502.20257, Appendix `app:Z2`, lines 5297--5319. -/
theorem sigma_generator_eq_one_or_eq_neg_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hω : IsCocycle ω)
    (hωn : IsNormalized ω) :
    sigma ω s₂ = 1 ∨ sigma ω s₂ = -1 := by
  have hinv := sigma_inv ω hω hωn s₂
  rw [z2Generator_inv] at hinv
  have hmul : sigma ω s₂ * sigma ω s₂ = 1 := by
    calc
      sigma ω s₂ * sigma ω s₂ = (sigma ω s₂)⁻¹ * sigma ω s₂ :=
        congrArg (fun z => z * sigma ω s₂) hinv
      _ = 1 := inv_mul_cancel _
  have hmulVal : (sigma ω s₂ : ℂ) * (sigma ω s₂ : ℂ) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hmul
  rcases mul_self_eq_one_iff.mp hmulVal with hone | hneg
  · left
    exact Units.ext hone
  · right
    exact Units.ext hneg

/-- A normalized scalar three-cocycle on Z₂ has nontrivial gauge class exactly
when its inversion scalar at the nonidentity generator is minus one.

This is the scalar cohomology classification in the first proposition of
arXiv:2502.20257, Appendix `app:Z2`, lines 5320--5341. It does not include the
pending tensor-level identification with the involutive dagger-gauge sign. -/
theorem not_isTrivialGaugeClass_iff_sigma_generator_eq_neg_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hω : IsCocycle ω)
    (hωn : IsNormalized ω) :
    ¬ IsTrivialGaugeClass ω ↔ sigma ω s₂ = -1 := by
  rw [not_congr (isTrivialGaugeClass_iff_sigma_generator_eq_one hωn)]
  rcases sigma_generator_eq_one_or_eq_neg_one hω hωn with hone | hneg
  · simp [hone]
  · simp [hneg]

end ScalarThreeCochain

end TNLean.Algebra
