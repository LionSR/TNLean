/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison

/-!
# Open ground spaces at a supplied simultaneous injectivity length

Simultaneous injectivity at a positive length \(S\) propagates to every
larger length without normalization assumptions on the original blocks.
For every range \(S+1\leq R\leq N\), the open parent-Hamiltonian kernel
is precisely the full local matrix product space on \(N\) sites.

Independent primitive gauges are used only in the proof. They retain the
specified length and all local matrix product spaces.
Source: arXiv:2011.12127, Section IV.C, lines 2114--2129.
-/

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]

/-- Simultaneous injectivity at a positive length propagates to every larger
length, without normalization assumptions on the original blocks.
Source: arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem wordTupleSpanTop_of_ge
    (A : (j : Fin r) → MPSTensor d (dim j)) {S n : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hSn : S ≤ n) :
    WordTupleSpanTop A n := by
  classical
  choose B ζ ρ hζ hGauge _hmpv hP _hρ _hGS _hPI _hCGS using
    fun j ↦ exists_isPrimitiveMPS_gauge_of_isNormal
      ⟨S, hS, isNBlkInjective_of_wordTupleSpanTop A hSpan j⟩
  have hSpanB : WordTupleSpanTop B n :=
    wordTupleSpanTop_of_ge_of_tracePreserving B
      (wordTupleSpanTop_of_family_gaugeEquiv
        (wordTupleSpanTop_of_family_smul A ζ hζ hSpan) hGauge)
      (fun j ↦ (hP j).norm) hSn
  simpa only [inv_smul_smul₀ (hζ _)] using
    wordTupleSpanTop_of_family_smul (fun j ↦ ζ j • A j) (fun j ↦ (ζ j)⁻¹)
      (fun j ↦ inv_ne_zero (hζ j))
      (wordTupleSpanTop_of_family_gaugeEquiv_symm hSpanB hGauge)

/-- At every range exceeding the supplied simultaneous injectivity length,
the open parent-Hamiltonian kernel is the full local matrix product space.
The original blocks need no normalization hypotheses.
Source: arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
    [NeZero d] (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R N : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    LinearMap.ker (openParentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ) A) R N) =
      groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  obtain ⟨B, ρ, hP, _hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  have hLocal : ∀ L, groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      groundSpace (toTensorFromBlocks (d := d) (μ := μ) B) L :=
    fun L ↦ groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L)
  rw [openParentHamiltonianES_eq_of_groundSpace_eq (hLocal R) N]
  simpa only [groundSpaceES, hLocal N] using
    ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
      μ B hμ (fun j ↦ (hP j).norm)
      (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving B hSpanB
        (fun j ↦ (hP j).norm) hn) hR hRN

end MPSTensor
