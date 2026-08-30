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
arXiv:2502.20257, Appendix `app:Z2`, lines 5326--5341. It identifies the
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
Appendix `app:Z2`, lines 5326--5329. -/
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

private lemma z2_generator_inv : s₂⁻¹ = s₂ := by
  decide

private lemma z2_generator_mul_self : s₂ * s₂ = 1 := by
  decide

/-- A normalized scalar three-cochain on Z₂ has trivial gauge class exactly
when its inversion scalar at the nonidentity generator is one.

For the forward implication, the gauge two-cochain need not be normalized.
Normalization of its coboundary instead forces both identity-axis restrictions
to equal one common constant, by `isNormalized_coboundary_iff`; at the triple
of nonidentity elements this constant and the remaining self-pair factor
cancel. This formalizes the normalized-cochain classification used in
arXiv:2502.20257, Appendix `app:Z2`, lines 5331--5341. -/
theorem isTrivialGaugeClass_iff_sigma_generator_eq_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hωn : IsNormalized ω) :
    IsTrivialGaugeClass ω ↔ sigma ω s₂ = 1 := by
  constructor
  · rintro ⟨β, hβ⟩
    have hcob_eq : coboundary β = ω := by
      funext g h k
      simpa only [fusionGauge, mul_one] using congrFun (congrFun (congrFun hβ g) h) k
    have hcob : IsNormalized (coboundary β) := hcob_eq ▸ hωn
    obtain ⟨c, hleft, hright⟩ := (isNormalized_coboundary_iff β).1 hcob
    have hvalue := congrFun (congrFun (congrFun hβ s₂) s₂) s₂
    simp only [fusionGauge, coboundary, z2_generator_mul_self, hleft, hright,
      mul_one] at hvalue
    simp only [sigma, z2_generator_inv, ← hvalue]
    rw [mul_comm c]
    exact div_self' _
  · intro hsigma
    have hω : ω = fun _ _ _ => 1 := by
      funext g h k
      rcases z2_cases g with rfl | rfl <;>
        rcases z2_cases h with rfl | rfl <;>
          rcases z2_cases k with rfl | rfl
      all_goals first
        | simp only [hωn.1, hωn.2.1, hωn.2.2]
        | simpa only [sigma, z2_generator_inv] using hsigma
    rw [hω]
    exact CohomologousTo.refl _

/-- The inversion scalar of a normalized scalar three-cocycle on Z₂ is either
one or minus one. This is the scalar counterpart of the sign discussion in
arXiv:2502.20257, Appendix `app:Z2`, lines 5331--5341. It does not use the
tensor identity in that discussion. -/
theorem sigma_generator_eq_one_or_eq_neg_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hω : IsCocycle ω)
    (hωn : IsNormalized ω) :
    sigma ω s₂ = 1 ∨ sigma ω s₂ = -1 := by
  have hinv := sigma_inv ω hω hωn s₂
  rw [z2_generator_inv] at hinv
  exact (Units.inv_eq_self_iff _).mp hinv.symm

/-- A normalized scalar three-cocycle on Z₂ has nontrivial gauge class exactly
when its inversion scalar at the nonidentity generator is minus one.

This is the scalar cohomology classification in arXiv:2502.20257,
Appendix `app:Z2`, lines 5331--5341. It does not include the tensor-level
identification with the involutive dagger-gauge sign. -/
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
