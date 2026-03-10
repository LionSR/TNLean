/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.Construction
import TNLean.MPS.FundamentalTheoremMulti

/-!
# End-to-end multi-block Fundamental Theorem from per-block SameMPV

This file provides the complete pipeline from per-block `SameMPV` to:
- Per-block gauge equivalence
- Global gauge equivalence of block-diagonal tensors
- Block-permutation decomposition

It also handles the single-block case where `SameMPV₂` directly gives `SameMPV`.

## Main results

* `fundamentalTheorem_multiBlock_full` — full multi-block FT with per-block + global gauge
* `fundamentalTheorem_multiBlock_decomposition` — version with block-permutation decomposition
* `sameMPV₂_single_block` — for `r = 1`, SameMPV₂ gives per-block SameMPV (no PF needed)
* `fundamentalTheorem_singleBlock_fromMPV₂` — single-block FT from SameMPV₂
* `fundamentalTheorem_multiBlock_fromSameMPV₂` — end-to-end from SameMPV₂ + separation hyp
* `perBlock_sameMPV_iff_gaugeEquiv` — SameMPV ↔ GaugeEquiv under injectivity

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197)
* [Cirac2017MPS] De las Cuevas, Schuch, Pérez-García, Cirac (arXiv:2011.12127)
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Full multi-block Fundamental Theorem -/
section FullMultiBlock

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **The full multi-block Fundamental Theorem of MPS.**

Given injective block tensors `A_k` with per-block `SameMPV (A k) (B k)`, we get:
1. Per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`
2. Global gauge equivalence of the block-diagonal tensors -/
theorem fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  ⟨fun k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fundamentalTheorem_multiBlock_global μ A B hA hSame⟩

/-- **Multi-block FT with explicit gauge matrices.** -/
theorem fundamentalTheorem_multiBlock_explicit
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) :=
  ⟨fun k => (fundamentalTheorem_singleBlock (hA k) (hSame k)).choose,
   fun k => (fundamentalTheorem_singleBlock (hA k) (hSame k)).choose_spec⟩

/-- **Multi-block FT with decomposition.** -/
theorem fundamentalTheorem_multiBlock_decomposition
    [∀ k, NeZero (dim k)]
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
      (X : ∀ i, GL (Fin (dim i)) ℂ),
    ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap (piAlgEquiv A B hA hSame).toRingEquiv σ i M) =
        (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) :=
  piAlgEquiv_decomposition A B hA hSame

end FullMultiBlock

/-! ### Single-block separation from `SameMPV₂`

When there is only **one** block (`r = 1`), the `SameMPV₂` condition on block-diagonal tensors
immediately yields per-block `SameMPV`, provided the scaling factor `μ₀` is nonzero.  This is
because the weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` degenerates to
`μ₀^N · mpv(A₀, σ) = μ₀^N · mpv(B₀, σ)`, and dividing by `μ₀^N ≠ 0` gives the result.

This lets us close the gap completely for single-block canonical forms, avoiding the need for
quantum Perron–Frobenius theory in this special case.
-/
section SingleBlockSeparation

variable {dim₀ : ℕ}

/-- For a single block, `SameMPV₂` on the block-diagonal tensor gives `SameMPV` on the block
    tensor, provided the scaling factor is nonzero. -/
theorem sameMPV₂_single_block
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    SameMPV A₀ B₀ := by
  intro N σ
  have := sameMPV₂_summed_blocks (fun _ : Fin 1 => μ₀) (fun _ => A₀) (fun _ => B₀) hSame₂ N σ
  simp only [Fin.sum_univ_one] at this
  exact mul_left_cancel₀ (pow_ne_zero N hμ) this

/-- **Single-block Fundamental Theorem from `SameMPV₂`.**

For canonical forms with one block, `SameMPV₂` (with `μ₀ ≠ 0`) gives full gauge equivalence
without any separation hypothesis. -/
theorem fundamentalTheorem_singleBlock_fromMPV₂
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hA : IsInjective A₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    GaugeEquiv A₀ B₀ :=
  fundamentalTheorem_singleBlock hA (sameMPV₂_single_block μ₀ hμ A₀ B₀ hSame₂)

end SingleBlockSeparation

/-! ### End-to-end theorems from `SameMPV₂` with explicit separation hypothesis

These theorems provide the complete pipeline: `SameMPV₂` → per-block `SameMPV` (via `hSep`)
→ per-block `GaugeEquiv` → global `GaugeEquiv` → block-permutation decomposition.

The separation hypothesis `hSep` is needed for `r ≥ 2` (quantum PF theory); for `r = 1` it
is proved by `sameMPV₂_single_block`. -/
section EndToEnd

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **End-to-end multi-block FT from `SameMPV₂`.**

Starting from `SameMPV₂` on block-diagonal tensors, the per-block separation hypothesis
(the only piece requiring PF theory) yields:
- Per-block gauge equivalence `GaugeEquiv (A k) (B k)` for all `k`
- Global gauge equivalence of the block-diagonal tensors
- Block-permutation decomposition of the Pi-algebra automorphism

The `hSame₂` hypothesis is retained so that this theorem continues to present the full end-to-end
interface, even though the current wrapper proof only uses the supplied separation data `hSep`. -/
theorem fundamentalTheorem_multiBlock_fromSameMPV₂
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (hSep : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) ∧
    (∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
       (X : ∀ i, GL (Fin (dim i)) ℂ),
     ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
       (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
         (componentMap (piAlgEquiv A B hA hSep).toRingEquiv σ i M) =
         (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
           ((X i)⁻¹ : GL (Fin (dim i)) ℂ)) := by
  let _ := hSame₂
  exact
    ⟨fun k => fundamentalTheorem_singleBlock (hA k) (hSep k),
      fundamentalTheorem_multiBlock_global μ A B hA hSep,
      piAlgEquiv_decomposition A B hA hSep⟩

/-- **End-to-end multi-block FT with explicit gauge matrices.**

As above, `hSame₂` is kept for interface compatibility, while the wrapper proof itself only uses
`hSep`. -/
theorem fundamentalTheorem_multiBlock_explicit_fromSameMPV₂
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (hSep : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  let _ := hSame₂
  exact fundamentalTheorem_multiBlock_explicit A B hA hSep

end EndToEnd

/-! ### Equivalence: per-block SameMPV ↔ per-block GaugeEquiv (under injectivity) -/
section Equivalence

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **Per-block SameMPV ↔ per-block GaugeEquiv**, under per-block injectivity.

This is the clean reformulation of the single-block Fundamental Theorem applied blockwise:
the hypothesis that each block `A_k` generates the same MPV family as `B_k` is equivalent to
the conclusion that they are related by per-block gauge transforms. -/
theorem perBlock_sameMPV_iff_gaugeEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (∀ k, SameMPV (A k) (B k)) ↔ (∀ k, GaugeEquiv (A k) (B k)) :=
  ⟨fun hSame k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fun hGauge k => (hGauge k).sameMPV⟩

/-- Global `SameMPV` follows from per-block `SameMPV` for block-diagonal tensors. -/
theorem global_sameMPV_of_perBlock
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  sameMPV_toTensorFromBlocks_of_blockSameMPV μ A B hSame

end Equivalence

end MPSTensor
