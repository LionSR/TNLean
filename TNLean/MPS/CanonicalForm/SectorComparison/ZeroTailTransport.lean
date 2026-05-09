/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.Core.BlockingInfrastructure

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Zero-block MPV transport

This module contains generic lemmas for transporting decompositions of an MPS
tensor into a zero block plus a nonzero part.  The Lean formalization uses the
name "zero tail" (`zeroTailDim`, `zeroMPSTensor`) as an internal bookkeeping
term; the source paper (arXiv:1606.00608, Section~2.3) calls these "zero blocks."
-/

namespace MPSTensor

/-! ## Zero-tail and weight transport through blocking -/

/-- Reblocking preserves a zero-tail/nonzero-part MPV decomposition.

The positive-period hypothesis is exactly what keeps the zero-tail contribution
confined to length zero after blocking: a blocked chain of positive length expands
to a positive number of original sites. -/
theorem zeroTail_mpv_decomp_blockTensor
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

/-- Reblocking a zero-tail plus weighted nonzero-block decomposition transports every
nonzero-block weight to the corresponding blocking power. -/
theorem zeroTail_toTensorFromBlocks_blockPower
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

/-- Transport the length-zero identity for assembled nonzero block sums through
physical blocking, with weights raised to the blocking power. -/
theorem zeroTail_identity_toTensorFromBlocks_blockPower
    {d rA rB zeroTailA zeroTailB p : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (μA : Fin rA → ℂ) (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) :
    ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun j => (μA j) ^ p)
            (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) p)) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ := by
  intro σ
  let σflat := blockedFlatConfig (d := d) p σ
  have hA := sameMPV₂_blockTensor_toTensorFromBlocks
    (d := d) (dim := dimA) μA blocksA p
  have hB := sameMPV₂_blockTensor_toTensorFromBlocks
    (d := d) (dim := dimB) μB blocksB p
  calc
    (zeroTailA : ℂ) +
        mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun j => (μA j) ^ p)
          (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) p)) σ
        = (zeroTailA : ℂ) +
            mpv (blockTensor (d := d) (D := ∑ j : Fin rA, dimA j)
              (toTensorFromBlocks (d := d) (μ := μA) blocksA) p) σ := by
          rw [← hA 0 σ]
    _ = (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σflat := by
          rw [mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d)
            (toTensorFromBlocks (d := d) (μ := μA) blocksA) p σ]
    _ = (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σflat := by
          let σ0 : Fin 0 → Fin d := fun i => Fin.elim0 i
          have hA0 :
              mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σflat =
                mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ0 := by
            let σ0' : Fin (0 * p) → Fin d := fun i => σ0 (Fin.cast (by simp) i)
            have hσ : σflat = σ0' := by
              funext i
              exact Fin.elim0 (Fin.cast (by simp) i)
            rw [hσ]
            simp [σ0']
          have hB0 :
              mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σflat =
                mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ0 := by
            let σ0' : Fin (0 * p) → Fin d := fun i => σ0 (Fin.cast (by simp) i)
            have hσ : σflat = σ0' := by
              funext i
              exact Fin.elim0 (Fin.cast (by simp) i)
            rw [hσ]
            simp [σ0']
          calc
            (zeroTailA : ℂ) +
                mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σflat
                = (zeroTailA : ℂ) +
                    mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ0 := by
                  rw [hA0]
            _ = (zeroTailB : ℂ) +
                    mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ0 := hZero σ0
            _ = (zeroTailB : ℂ) +
                    mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σflat := by
                  rw [hB0]
    _ = (zeroTailB : ℂ) +
            mpv (blockTensor (d := d) (D := ∑ k : Fin rB, dimB k)
              (toTensorFromBlocks (d := d) (μ := μB) blocksB) p) σ := by
          rw [mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d)
            (toTensorFromBlocks (d := d) (μ := μB) blocksB) p σ]
    _ = (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μB k) ^ p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ := by
          rw [hB 0 σ]

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
