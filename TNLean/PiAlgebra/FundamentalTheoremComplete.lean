/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.Construction
import TNLean.MPS.FundamentalTheorem.Multi

/-!
# Per-block MPV equality and gauge equivalence of direct sums

For injective blocks, `SameMPV (A k) (B k)` gives
`B_k^i = X_k A_k^i X_k⁻¹`. Hence the weighted direct sums satisfy
`⊕_k μ_k B_k^i = (⊕_k X_k) (⊕_k μ_k A_k^i) (⊕_k X_k⁻¹)`.
The product-algebra automorphism also decomposes as a block permutation and
inner conjugations on the matrix factors.

It also handles the single-block case where `SameMPV₂` directly gives `SameMPV`.

## Main results

* `fundamentalTheorem_multiBlock_full` — per-block and direct-sum gauge equivalence
* `fundamentalTheorem_multiBlock_decomposition` — auxiliary lemma exposing block permutation
* `sameMPV₂_single_block` — for `r = 1`, SameMPV₂ gives per-block SameMPV (no PF needed)
* `fundamentalTheorem_singleBlock_fromMPV₂` — single-block FT from SameMPV₂
* `perBlock_sameMPV_iff_gaugeEquiv` — auxiliary lemma for SameMPV ↔ GaugeEquiv under injectivity

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197)
* [CPSV21] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix product states and projected entangled pair states*, arXiv:2011.12127.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Per-block and direct-sum gauge equivalence -/
section FullMultiBlock

variable {r : ℕ} {dim : Fin r → ℕ}

/-- From `∀ k, 𝓥(A_k)=𝓥(B_k)` with each `A_k` injective, obtain both
`∀ k, GaugeEquiv (A k) (B k)` and
`GaugeEquiv (⊕_k μ_k A_k) (⊕_k μ_k B_k)`. -/
lemma fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  ⟨fundamentalTheorem_multiBlock_blocks A B hA hSame,
    fundamentalTheorem_multiBlock_global μ A B hA hSame⟩

/-- Extract explicit matrices `X_k` such that `B_k^i = X_k A_k^i X_k⁻¹`. -/
lemma fundamentalTheorem_multiBlock_explicit
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  classical
  let hGauge := fundamentalTheorem_multiBlock_blocks A B hA hSame
  exact ⟨fun k => (hGauge k).choose, fun k => (hGauge k).choose_spec⟩

/-- Decompose the product-algebra automorphism attached to per-block `SameMPV` data. -/
lemma fundamentalTheorem_multiBlock_decomposition
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
lemma sameMPV₂_single_block
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

/-! ### Equivalence: per-block SameMPV ↔ per-block GaugeEquiv (under injectivity) -/
section Equivalence

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **Per-block SameMPV ↔ per-block GaugeEquiv**, under per-block injectivity.

This is the clean reformulation obtained by applying the single-block Fundamental Theorem to
each block:
the hypothesis that each block `A_k` generates the same MPV family as `B_k` is equivalent to
the conclusion that they are related by per-block gauge transforms. -/
lemma perBlock_sameMPV_iff_gaugeEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (∀ k, SameMPV (A k) (B k)) ↔ (∀ k, GaugeEquiv (A k) (B k)) :=
  ⟨fun hSame k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fun hGauge k => (hGauge k).sameMPV⟩

end Equivalence

end MPSTensor
