/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Existence

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Zero-tail MPV transport

This module contains generic lemmas for transporting decompositions of an MPS
tensor into a zero tail plus a nonzero part.
-/

namespace MPSTensor

/-- Transport a zero-tail decomposition along an MPV equivalence of its nonzero part. -/
theorem zeroTail_eq_of_sameMPV₂
    {d D L L' z : ℕ} (A : MPSTensor d D) (live : MPSTensor d L)
    (flat : MPSTensor d L')
    (hZeroTail : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ + mpv live σ)
    (hFlat : SameMPV₂ live flat) :
    ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ + mpv flat σ := by
  intro N σ
  calc
    mpv A σ = mpv (zeroMPSTensor d z) σ + mpv live σ := hZeroTail N σ
    _ = mpv (zeroMPSTensor d z) σ + mpv flat σ := by
      rw [hFlat N σ]

/-- At positive lengths, a zero-tail decomposition reduces to the nonzero part. -/
theorem sameMPV₂Pos_of_zeroTail_eq
    {d D L z : ℕ} (A : MPSTensor d D) (live : MPSTensor d L)
    (hZeroTail : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ + mpv live σ) :
    SameMPV₂Pos A live := by
  intro N hN σ
  have hZero : mpv (zeroMPSTensor d z) σ = 0 := by
    rw [mpv_zeroMPSTensor]
    simp [Nat.ne_of_gt hN]
  calc
    mpv A σ = mpv (zeroMPSTensor d z) σ + mpv live σ := hZeroTail N σ
    _ = mpv live σ := by
      rw [hZero, zero_add]

/-- Remove matching zero tails from two MPV identities.

If `A` and `B` have the same MPVs, and each is expressed as a zero tail plus a nonzero part,
then equality of the zero-tail dimensions gives full `SameMPV₂` equality of the nonzero parts.
For positive lengths the zero tails vanish; at length zero this is exactly the missing
zero-tail condition. -/
theorem sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
    {d D₁ D₂ L₁ L₂ z₁ z₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (liveA : MPSTensor d L₁) (liveB : MPSTensor d L₂)
    (hSame : SameMPV₂ A B)
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z₁) σ + mpv liveA σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d z₂) σ + mpv liveB σ)
    (hz : z₁ = z₂) :
    SameMPV₂ liveA liveB := by
  intro N σ
  have hsum :
      mpv (zeroMPSTensor d z₁) σ + mpv liveA σ =
        mpv (zeroMPSTensor d z₂) σ + mpv liveB σ := by
    calc
      mpv (zeroMPSTensor d z₁) σ + mpv liveA σ = mpv A σ := (hA N σ).symm
      _ = mpv B σ := hSame N σ
      _ = mpv (zeroMPSTensor d z₂) σ + mpv liveB σ := hB N σ
  by_cases hN : N = 0
  · subst hN
    have hz₁mpv : mpv (zeroMPSTensor d z₁) σ = (z₁ : ℂ) := by
      rw [mpv_zeroMPSTensor]
      simp
    have hz₂mpv : mpv (zeroMPSTensor d z₂) σ = (z₂ : ℂ) := by
      rw [mpv_zeroMPSTensor]
      simp
    have hsum' :
        (z₂ : ℂ) + mpv liveA σ = (z₂ : ℂ) + mpv liveB σ := by
      rw [hz₁mpv, hz₂mpv] at hsum
      rw [hz] at hsum
      exact hsum
    exact add_left_cancel hsum'
  · have hz₁mpv : mpv (zeroMPSTensor d z₁) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [hN]
    have hz₂mpv : mpv (zeroMPSTensor d z₂) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [hN]
    have hsum' : (0 : ℂ) + mpv liveA σ = 0 + mpv liveB σ := by
      rw [hz₁mpv, hz₂mpv] at hsum
      exact hsum
    simpa [zero_add] using hsum'

end MPSTensor
