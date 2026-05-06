/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.Core.BlockingInfrastructure

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# All-zero-block MPV transport

This module contains generic lemmas for transporting decompositions of an MPS
tensor into an all-zero-block contribution plus a nonzero part.  The `zeroTail`
names in this file are the formal variables for the total bond dimension of the
all-zero leftover blocks, corresponding to the source-paper allowance
`∑ k, D_k ≤ D`.
-/

namespace MPSTensor

/-! ## Zero-tail and weight transport through blocking -/

/-- Reblocking preserves an all-zero-block/nonzero-part MPV decomposition.

The positive-period hypothesis is exactly what keeps the all-zero-block contribution
confined to length zero after blocking: a blocked chain of positive length expands
to a positive number of original sites. -/
lemma zeroTail_mpv_decomp_blockTensor
    {d D L z p : ℕ}
    (A : MPSTensor d D) (nonzeroPart : MPSTensor d L)
    (hp : 0 < p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ + mpv nonzeroPart σ) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (blockTensor (d := d) (D := L) nonzeroPart p) σ := by
  intro N σ
  let σflat := blockedFlatConfig (d := d) p σ
  rw [mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) A p σ]
  rw [hMPV (N * p) σflat]
  have hNP_iff : N * p = 0 ↔ N = 0 := by
    rw [Nat.mul_eq_zero]
    exact ⟨fun h => h.resolve_right hp.ne', fun h => Or.inl h⟩
  have hZero :
      mpv (zeroMPSTensor d z) σflat =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ := by
    rw [mpv_zeroMPSTensor, mpv_zeroMPSTensor]
    simp [hNP_iff]
  rw [hZero]
  congr 1
  exact (mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) nonzeroPart p σ).symm

/-- Reblocking an all-zero-block plus weighted nonzero-block decomposition transports every
nonzero-block weight to the corresponding blocking power. -/
lemma zeroTail_toTensorFromBlocks_blockPower
    {d D r z p : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D)
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hp : 0 < p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μ k) ^ p)
            (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) σ := by
  intro N σ
  have hBlock :=
    zeroTail_mpv_decomp_blockTensor
      (d := d) (D := D) (L := ∑ k : Fin r, dim k) (z := z) (p := p)
      A (toTensorFromBlocks (d := d) (μ := μ) blocks) hp hMPV N σ
  have hNonzeroPart := sameMPV₂_blockTensor_toTensorFromBlocks
    (d := d) (dim := dim) μ blocks p
  calc
    mpv (blockTensor (d := d) (D := D) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (blockTensor (d := d) (D := ∑ k : Fin r, dim k)
            (toTensorFromBlocks (d := d) (μ := μ) blocks) p) σ := hBlock
    _ = mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μ k) ^ p)
            (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) σ := by
          rw [hNonzeroPart N σ]

/-- Transport an all-zero-block decomposition along an MPV equivalence of its nonzero part. -/
lemma zeroTail_eq_of_sameMPV₂
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
lemma sameMPV₂Pos_of_zeroTail_eq
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
lemma sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
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
