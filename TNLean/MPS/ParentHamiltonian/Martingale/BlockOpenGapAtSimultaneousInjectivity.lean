/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap

/-!
# Open-chain gaps at a supplied simultaneous injectivity length

A simultaneous word span at a positive length \(S\) gives a positive
open-chain gap at each prescribed interaction range \(R\geq S+1\),
uniformly over an unbounded sequence of chain lengths. This supplies one
open interval satisfying the strict finite-range Knabe inequality.

Independent primitive normalization preserves the local spaces and the
specified length \(S\). The grouped martingale estimate first gives an
open-chain gap at a sufficiently large range \(2p\), on all lengths
\(pM\) with \(M\geq2\). Finite-interval comparison transfers this gap to
the original prescribed range without changing the local kernels.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii) and Section 6;
arXiv:2011.12127, Section IV.C, lines 2114--2129 and 2183--2187.
The finite-range Knabe coefficient is recorded in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- A supplied simultaneous injectivity length gives a positive open-chain
gap at every range \(R\geq S+1\), uniformly over lengths \(pM\) for some
\(p>0\) and all \(M\geq2\). Normalization is derived internally and no
inequivalence hypothesis is imposed on the original blocks.
Source: arXiv:cond-mat/9410110, Theorem 2.1(ii) and Section 6, with the
block-injective local spaces of arXiv:2011.12127, lines 2114--2129. -/
theorem exists_openParentHamiltonianES_toTensorFromBlocks_gap_subsequence_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ p : ℕ, 0 < p ∧ R ≤ 2 * p ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ M : ℕ, 2 ≤ M → ∀ v ∈
        (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) (p * M))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R (p * M) v‖ := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  let T := toTensorFromBlocks (d := d) (μ := μ) B
  have hKernel : ∀ L N : ℕ, S + 1 ≤ L → L ≤ N →
      LinearMap.ker (openParentHamiltonianES T L N) = groundSpaceES T N :=
    fun L N hSL hLN ↦
      ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
        μ B hμ hS hSpanB hSL hLN
  obtain ⟨p, hRp, hp, γ, hγ, hLong⟩ :=
    exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) R
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_parentInteractionES_openParentHamiltonianES_comparison
      T (hKernel R (2 * p) hR (by omega))
  have hGapB : ∀ M : ℕ, 2 ≤ M → ∀ v ∈ (groundSpaceES T (p * M))ᗮ,
      (κ * γ / (2 * p - R + 1 : ℕ)) * ‖v‖ ≤
        ‖openParentHamiltonianES T R (p * M) v‖ := by
    intro M hM
    have hN : 2 * p ≤ p * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left p hM
    exact openParentHamiltonianES_gap_of_long_gap_at_length T (by omega) (by omega) hN
      hκ hγ hLocal (hKernel R (p * M) hR (by omega))
      (hKernel (2 * p) (p * M) (by omega) hN)
      (by
        have hLongM : ∀ v ∈ (LinearMap.ker
            (openParentHamiltonianES T (2 * p) (p * M)))ᗮ,
            γ * ‖v‖ ≤ ‖openParentHamiltonianES T (2 * p) (p * M) v‖ := hLong M hM
        rwa [hKernel (2 * p) (p * M) (by omega) hN] at hLongM)
  have hLocalGS : ∀ L, groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      groundSpace T L :=
    fun L ↦ groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L)
  refine ⟨p, hp, by omega, κ * γ / (2 * p - R + 1 : ℕ),
    div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (by omega)), ?_⟩
  intro M hM
  rw [openParentHamiltonianES_eq_of_groundSpace_eq (hLocalGS R) (p * M)]
  simpa only [groundSpaceES, hLocalGS (p * M)] using hGapB M hM

/-- Simultaneous injectivity supplies an open parent interval whose gap
satisfies the strict finite-range Knabe threshold at the prescribed range.
Source: arXiv:2011.12127, Section IV.C, lines 2183--2187; the coefficient
is recorded in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_strict_openParentHamiltonianES_toTensorFromBlocks_window_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ m : ℕ, R ≤ m ∧ ∃ γ : ℝ, 0 < γ ∧
      ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ ∧
      ∀ v ∈ (groundSpaceES
        (toTensorFromBlocks (d := d) (μ := μ) A) (m + R - 1))ᗮ,
        γ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R (m + R - 1) v‖ := by
  obtain ⟨p, hp, _hRp, δ, hδ, hGap⟩ :=
    exists_openParentHamiltonianES_toTensorFromBlocks_gap_subsequence_of_wordTupleSpanTop
      μ A hμ hS hSpan hR
  obtain ⟨n, hn⟩ := exists_lt_nsmul hδ (((R : ℝ) - 1) ^ 2)
  let M := n + 2 * R + 2
  let m := p * M + 1 - R
  have hMle : M ≤ p * M := Nat.le_mul_of_pos_left M hp
  have hm : R ≤ m := by dsimp only [m, M] at *; omega
  have hnm : n ≤ m := by dsimp only [m, M] at *; omega
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * δ := by
    calc
      ((R : ℝ) - 1) ^ 2 < n • δ := hn
      _ = (n : ℝ) * δ := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) hδ.le
  have hLength : m + R - 1 = p * M := by dsimp only [m, M] at *; omega
  refine ⟨m, hm, δ, hδ, hnum, ?_⟩
  rw [hLength]
  exact hGap M (by dsimp only [M]; omega)

end MPSTensor
