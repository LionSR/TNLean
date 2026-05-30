/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.ZeroTailTransport

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Zero-tail comparison for nonzero block tensors

When two matrix-product-vector families are written as an all-zero leftover block
contribution plus a weighted nonzero block tensor, equality at positive lengths
compares the nonzero parts directly. The length-zero equation records the
residual all-zero leftover block contribution, and full equality of the nonzero parts
follows once the leftover dimensions agree.

Here "zero-tail" names the total bond dimension of the separated all-zero leftover
blocks. It is the dimension gap allowed by `∑ k, D_k ≤ D`, where the block
decomposition may include zero blocks.

## References

* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, zero-tail convention, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **Positive-length equality of nonzero block tensors.**

Suppose two tensors with the same MPV family are each written as an all-zero leftover block
contribution plus a weighted nonzero block tensor. Then the nonzero parts agree at every
positive length, since the all-zero leftover block contributes nothing there. The
length-zero coefficient is recovered separately, at the end, from equality of the bond
dimensions. -/
theorem nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
    {d D₁ D₂ rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) :
    SameMPV₂Pos
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB) := by
  intro N hN σ
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  have hAσ := hA N σ
  have hBσ := hB N σ
  rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hAσ
  rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hBσ
  calc
    mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ = mpv A σ := hAσ.symm
    _ = mpv B σ := hSame N σ
    _ = mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := hBσ

/-- **Reblocked nonzero-block equality at positive length.**

If two tensors have the same MPVs and each is expressed as an all-zero leftover block plus a
weighted nonzero block tensor, then every positive common reblocking raises the
nonzero weights to powers and preserves positive-length equality of the nonzero parts.
The all-zero leftover block contributes only at length zero, so its coefficient is
recovered separately, at the end, from equality of the bond dimensions. -/
theorem nonzeroBlock_blockPower_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
    {d D₁ D₂ rA rB p : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hp : 0 < p)
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) :
    SameMPV₂Pos
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μA k) ^ p)
        (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μB k) ^ p)
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) := by
  have hAblock :=
    zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₁) (r := rA) (z := zeroTailA) (p := p) (dim := dimA)
      A μA blocksA hp hA
  have hBblock :=
    zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₂) (r := rB) (z := zeroTailB) (p := p) (dim := dimB)
      B μB blocksB hp hB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  exact
    nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      (d := blockPhysDim d p)
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      hAB zeroTailA zeroTailB
      (fun k => (μA k) ^ p)
      (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)
      (fun k => (μB k) ^ p)
      (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)
      hAblock hBblock

/-- **Recover full nonzero-block `SameMPV₂` once all-zero leftover blocks agree.**

This combines the positive-length theorem with the single additional
length-zero datum needed to remove the all-zero leftover blocks. It does not assert that the
leftover dimensions agree automatically; that remains a separate CPSV length-zero
condition for the unconditional after-blocking sector comparison. -/
theorem nonzeroBlock_sameMPV₂_of_sameMPV₂_of_zeroTail_eq
    {d D₁ D₂ rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hZeroTail : zeroTailA = zeroTailB) :
    SameMPV₂ (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB) :=
  -- The nonzero block tensors are the live parts of the two zero-tail
  -- decompositions, so this is the generic zero-tail cancellation lemma.
  sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq A B
    (toTensorFromBlocks (d := d) (μ := μA) blocksA)
    (toTensorFromBlocks (d := d) (μ := μB) blocksB)
    hSame hA hB hZeroTail

end MPSTensor
