/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.TPPrimitiveReduction

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Zero-tail comparison for nonzero block tensors

When two matrix-product-vector families are written as a zero-tail contribution
plus a weighted nonzero block tensor, equality at positive lengths compares the
nonzero parts directly.  The length-zero equation records the residual
zero-tail contribution, and full equality of the nonzero parts follows once the
zero tails agree.

## References

* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, zero tail, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **Zero-tail identity for nonzero block tensors.**

Suppose two tensors with the same MPV family are each written as a zero-tail
contribution plus a weighted nonzero block tensor. Then the nonzero parts agree at every
positive length, while the length-zero equation gives exactly the difference
between the zero-tail dimensions and the nonzero block bond dimensions.

This is the local length-zero identity needed before a full `SameMPV₂` comparison of the
nonzero block tensors can be recovered: the only missing datum is equality of the
two zero-tail dimensions (or an equivalent replacement for the `N = 0` case). -/
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
    (∀ {N : ℕ}, 0 < N → ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
    (∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) := by
  constructor
  · intro N hN σ
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hAσ := hA N σ
    have hBσ := hB N σ
    rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hAσ
    rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hBσ
    calc
      mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ = mpv A σ := hAσ.symm
      _ = mpv B σ := hSame N σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := hBσ
  · intro σ
    have hAσ := hA 0 σ
    have hBσ := hB 0 σ
    rw [mpv_zeroMPSTensor, if_pos rfl] at hAσ
    rw [mpv_zeroMPSTensor, if_pos rfl] at hBσ
    calc
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ
          = mpv A σ := hAσ.symm
      _ = mpv B σ := hSame 0 σ
      _ = (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := hBσ

/-- **Reblocked nonzero-block equality with a zero-tail identity.**

If two tensors have the same MPVs and each is expressed as a zero tail plus a
weighted nonzero block tensor, then every positive common reblocking transports the
nonzero weights to powers, preserves positive-length equality of the nonzero parts,
and leaves the zero-tail contribution as the sole length-zero term. -/
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
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) ∧
    (∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μA k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ) := by
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
  have hBook :=
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
  exact ⟨fun N hN σ => hBook.1 hN σ, hBook.2⟩

/-- **Recover full nonzero-block `SameMPV₂` once zero tails agree.**

This combines the positive-length theorem with the single additional
length-zero datum needed to remove the zero tails. It does not assert that the
zero-tail dimensions agree automatically; that remains a separate paper-level
length-zero condition for the unconditional after-blocking sector comparison. -/
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
      (toTensorFromBlocks (d := d) (μ := μB) blocksB) := by
  have hBook :=
    nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      A B hSame zeroTailA zeroTailB μA blocksA μB blocksB hA hB
  intro N σ
  by_cases hN : N = 0
  · subst N
    have h0 := hBook.2 σ
    have h0' : (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := by
      simpa [hZeroTail] using h0
    exact add_left_cancel h0'
  · exact hBook.1 (Nat.pos_of_ne_zero hN) σ

end MPSTensor
