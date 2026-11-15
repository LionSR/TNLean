/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Nat.Choose.Basic

/-!
# Exact conjugation phases in cyclic endpoint words

The endpoint audit of arXiv:2405.00439, Section V, `detectG`
(`Papers/2405.00439/MPU-DW.tex`, lines 2108–2117), gives local words
`u^(-r-2) w⁻¹ u^r w u²`. This module proves their exact phase in an arbitrary
group, assuming that conjugation by `w⁻¹` sends `u` to `c u`, with `c` commuting
with `u`. Their ordered product for `0 ≤ r < m` is `c^(m.choose 2)`.

**Scope:** these are group identities with an explicit conjugation hypothesis.
They apply to matrix unitary groups without introducing a separate representation
structure. They do not construct the clock and shift matrices, identify the full
spatial detector with the product of these local words, or prove the source's
anomaly detection assertion. Those comparisons remain separate from the exact
algebraic statements below.
-/

namespace MPOTensor
namespace FiniteGroupDetector

variable {Γ : Type*} [Group Γ]

/-- Normal form of a conjugation word when its conjugation phase commutes with
the bulk operator. Project algebraic statement used in the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem conjugation_word_eq_zpow (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (a b d : ℤ) :
    u ^ a * w⁻¹ * u ^ b * w * u ^ d = c ^ b * u ^ (a + b + d) := by
  have hpow : w⁻¹ * u ^ b * w = c ^ b * u ^ b := by
    calc
      w⁻¹ * u ^ b * w = (w⁻¹ * u * w) ^ b := by
        simpa only [inv_inv] using (conj_zpow (i := b) (a := w⁻¹) (b := u)).symm
      _ = (c * u) ^ b := by rw [hconj]
      _ = c ^ b * u ^ b := hc.mul_zpow b
  calc
    u ^ a * w⁻¹ * u ^ b * w * u ^ d = u ^ a * (w⁻¹ * u ^ b * w) * u ^ d := by
      simp only [mul_assoc]
    _ = u ^ a * (c ^ b * u ^ b) * u ^ d := by rw [hpow]
    _ = c ^ b * (u ^ a * u ^ b * u ^ d) := by
      rw [← mul_assoc (u ^ a) (c ^ b) (u ^ b), (hc.zpow_zpow b a).symm.eq]
      simp only [mul_assoc]
    _ = c ^ b * u ^ (a + b + d) := by rw [← zpow_add, ← zpow_add]

/-- The local word whose bulk powers cancel in the cyclic endpoint audit.
Source context: arXiv:2405.00439, `detectG`, lines 2108–2117; this word is an
explicit auxiliary expression, not a new definition of the source detector. -/
def endpointConjugationWord (u w : Γ) (r : ℕ) : Γ :=
  u ^ (-((r : ℤ) + 2)) * w⁻¹ * u ^ (r : ℤ) * w * u ^ (2 : ℤ)

/-- The local endpoint word has exactly the `r`th power of the conjugation phase.
Project algebraic statement for the audit of arXiv:2405.00439, `detectG`,
lines 2108–2117, conditional on the displayed conjugation identity. -/
theorem endpointConjugationWord_eq_pow (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (r : ℕ) :
    endpointConjugationWord u w r = c ^ r := by
  rw [endpointConjugationWord, conjugation_word_eq_zpow u w c hc hconj]
  have hexp : -((r : ℤ) + 2) + r + 2 = 0 := by omega
  simp [hexp]

/-- The ordered product of `m` local endpoint words is the triangular power of
their conjugation phase. This is an exact group identity, with no finite-group
or spatial comparison assumed implicitly. Project statement for the audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem prod_endpointConjugationWord_eq_pow (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (m : ℕ) :
    ((List.range m).map (endpointConjugationWord u w)).prod = c ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.prod_range_succ, ih, endpointConjugationWord_eq_pow u w c hc hconj,
      ← pow_add]
    congr 1
    simp [Nat.choose_succ_succ, Nat.add_comm]

/-- At even cyclic order `2k`, the endpoint product is the half-order power
of the phase. A nonidentity half-order power therefore obstructs a trivial
detector. This is conditional only on the local conjugation and phase-period
identities, not on a value of the entire product. Project algebraic statement
for the audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem prod_endpointConjugationWord_even (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (k : ℕ) (hperiod : c ^ (2 * k) = 1) :
    ((List.range (2 * k)).map (endpointConjugationWord u w)).prod = c ^ k := by
  rw [prod_endpointConjugationWord_eq_pow u w c hc hconj]
  by_cases hk : k = 0
  · subst k
    simp
  have hchoose : (2 * k).choose 2 = k * (2 * k - 1) := by
    rw [Nat.choose_two_right]
    have hmul : 2 * k * (2 * k - 1) = k * (2 * k - 1) * 2 := by
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hmul]
    omega
  have hsum : (2 * k).choose 2 + k = (2 * k) * k := by
    rw [hchoose]
    calc
      k * (2 * k - 1) + k = k * (2 * k - 1 + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = k * (2 * k) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)]
      _ = (2 * k) * k := Nat.mul_comm _ _
  have hpair : c ^ k * c ^ k = 1 := by
    rw [← pow_add, show k + k = 2 * k by omega, hperiod]
  have hcancel : c ^ ((2 * k).choose 2) * c ^ k = 1 := by
    rw [← pow_add, hsum, pow_mul, hperiod, one_pow]
  calc
    c ^ ((2 * k).choose 2) = c ^ ((2 * k).choose 2) * (c ^ k * c ^ k) := by
      rw [hpair, mul_one]
    _ = (c ^ ((2 * k).choose 2) * c ^ k) * c ^ k := by rw [mul_assoc]
    _ = c ^ k := by rw [hcancel, one_mul]

end FiniteGroupDetector
end MPOTensor
