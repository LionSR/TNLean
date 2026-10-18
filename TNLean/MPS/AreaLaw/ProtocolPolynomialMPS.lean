/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolCutCoordinates
import TNLean.MPS.AreaLaw.OpenMPSRank
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Polynomial original-site bond bounds from actual physical party cut ranks

The original-site vector is exactly the
pullback of the physical party vector along mainConfigurationEquiv. Its norm
is unchanged. Actual internal party-prefix rank bounds give all original-site
cut ranks by the existing coordinate and cut-growth argument. The existing
internal-cut rank constructor then supplies a matrix product representation
of this same vector, without normalization or replacement of the vector.

The numerical estimate retains both ceiling errors. The logarithmic width
contributes the prefactor q^40; the rounded alphabet bound contributes
(Cp+1)^χ. The natural exponent and prefactor depend only on q,D,Cp,alpha and χ,
not on the length or the vector. No division by log q is used.

These are auxiliary consumers of rank bounds. No circuit, compression output,
physical family, approximation error or complete Theorem B is constructed.

Source: the one-dimensional note, Part II, proof of Theorem B,
part2b_mps_protocol.tex, lines 605–615. The constructor is the existing
open-boundary rank theorem associated with Part IIa, prop:VC, lines 39–62.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

/-- Both ceiling errors give a polynomial bound with constants independent of
L and w. The natural alpha is the exponent of the alphabet bound.
Source: Part II, proof of Theorem B, lines 605–615. -/
theorem polynomial_bond_bound_of_ceil_width
    {q : ℕ} {D Cp : ℝ} {α : ℕ} (χ : ℕ)
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hCp : 0 ≤ Cp) (hα : 0 < α)
    {L w : ℕ} (hL : 2 ≤ L) (hw : w = ⌈D * Real.log L⌉₊) :
    ((q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ : ℕ) : ℝ) ≤
      (q : ℝ) ^ 40 * (Cp + 1) ^ χ *
        (L : ℝ) ^ (max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)) := by
  let N := max 1 ⌈Cp * (L : ℝ) ^ α⌉₊
  let u := ⌈40 * D * Real.log q⌉₊
  let n := max 1 (u + χ * α)
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hLR : 1 ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hL0 : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hLR
  have hwidth : (w : ℝ) ≤ D * Real.log L + 1 := by
    rw [hw]
    exact (Nat.ceil_lt_add_one (mul_nonneg (zero_le_one.trans hD) hlogL)).le
  have hu : 40 * D * Real.log q ≤ (u : ℝ) := Nat.le_ceil _
  have hqfactor : (q : ℝ) ^ (40 * w) ≤ (q : ℝ) ^ 40 * (L : ℝ) ^ u := by
    apply (Real.log_le_log_iff (pow_pos hq0 _) (mul_pos (pow_pos hq0 _) (pow_pos hL0 _))).mp
    rw [Real.log_mul (pow_ne_zero _ hq0.ne') (pow_ne_zero _ hL0.ne')]
    simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
    have h₁ := mul_le_mul_of_nonneg_right hwidth
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) hlogq)
    have h₂ := mul_le_mul_of_nonneg_right hu hlogL
    nlinarith
  have hLpower : (1 : ℝ) ≤ (L : ℝ) ^ α :=
    hLR.trans (le_self_pow₀ hLR hα.ne')
  have hceil : (⌈Cp * (L : ℝ) ^ α⌉₊ : ℝ) ≤ Cp * (L : ℝ) ^ α + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hCp (pow_nonneg hL0.le _))).le
  have hN : (N : ℝ) ≤ (Cp + 1) * (L : ℝ) ^ α := by
    dsimp only [N]
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · nlinarith [mul_nonneg hCp (pow_nonneg hL0.le α)]
    · nlinarith
  have hNpower := pow_le_pow_left₀ (Nat.cast_nonneg N) hN χ
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    (q : ℝ) ^ (40 * w) * (N : ℝ) ^ χ
        ≤ ((q : ℝ) ^ 40 * (L : ℝ) ^ u) * ((Cp + 1) * (L : ℝ) ^ α) ^ χ :=
      mul_le_mul hqfactor hNpower (pow_nonneg (Nat.cast_nonneg N) _)
        (mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg hL0.le _))
    _ = (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ (u + χ * α) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm α χ, pow_add]
      ac_rfl
    _ ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hLR (le_max_right 1 (u + χ * α))) (by positivity)

/-- A unit physical party vector with the actual polynomial block-prefix rank
bounds gives a unit original-site MPS with an explicit polynomial bond bound.
The party-prefix rank bounds are auxiliary inputs, not physical conclusions.
Source: Part II, proof of Theorem B, lines 605–615. -/
theorem isOpenMPS_of_polynomial_partyPrefix_bounds
    {q : ℕ} {D Cp : ℝ} {α : ℕ} (χ : ℕ)
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hCp : 0 ≤ Cp) (hα : 0 < α)
    {L w : ℕ} (hL : 2 ≤ L) (hw : w = ⌈D * Real.log L⌉₊)
    (hlarge : 60 * w ≤ L)
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    (hψ : ‖ψ‖ = 1)
    (hprefix : ∀ r : ℕ, 0 < r → r ≤ stageCount L w →
      (TNLean.PEPS.WholeGroup.flattening (fun y ↦ ψ y)
        (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤
          (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ) :
    let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
      WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    let B := q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ
    let n := max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)
    ‖Φ‖ = 1 ∧ (∀ k : ℕ, k ≤ L → (cutMatrix Φ k).rank ≤ B) ∧
      IsOpenMPS L q B (fun x ↦ Φ x) ∧ 1 ≤ n ∧
        (B : ℝ) ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n := by
  classical
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
    WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
  let R := (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ
  let B := q ^ (40 * w) * R
  let n := max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)
  change ‖Φ‖ = 1 ∧ (∀ k : ℕ, k ≤ L → (cutMatrix Φ k).rank ≤ B) ∧
    IsOpenMPS L q B (fun x ↦ Φ x) ∧ 1 ≤ n ∧
      (B : ℝ) ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n
  have hw1 : 1 ≤ w := by
    rw [hw]
    apply Nat.one_le_ceil_iff.mpr
    exact mul_pos (lt_of_lt_of_le zero_lt_one hD)
      (Real.log_pos (by exact_mod_cast (by omega : 1 < L)))
  have hR : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))))
  have hnorm : ‖Φ‖ = 1 := by
    change ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv L w q).symm ψ‖ = 1
    rw [LinearIsometryEquiv.norm_map, hψ]
  have hcuts (k : ℕ) (hk : k ≤ L) : (cutMatrix Φ k).rank ≤ B :=
    rank_cutMatrix_le_of_partyPrefix_bounds ψ hq hw1 hlarge hR hprefix k hk
  have hmps : IsOpenMPS L q B (fun x ↦ Φ x) :=
    isOpenMPS_of_internal_cutMatrix_rank_le Φ (fun k _ hk ↦ hcuts k hk.le)
  exact ⟨hnorm, hcuts, hmps, le_max_left _ _,
    polynomial_bond_bound_of_ceil_width χ hq hD hCp hα hL hw⟩

end TNLean.MPS.AreaLaw.ChainSweep
