/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockOpenGapAllLengths

/-!
# Open-chain gaps at every length at simultaneous injectivity

A simultaneous word span at a positive length \(S\) gives a uniform positive
open-chain gap at each interaction range \(R\geq S+1\), for every chain
length \(N\geq R\). The tensor is a weighted direct sum with nonzero
coefficients. No primitive normalization or separation hypothesis is imposed
on the supplied blocks: these properties are derived from simultaneous
injectivity, with all local ground spaces preserved.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
arXiv:2011.12127, Section IV.C, lines 2114--2129.

**Scope restriction (sufficient interaction range):** The result assumes
\(R\geq S+1\). This is the sufficient range of the intersection argument,
not a restriction of the source definition of a parent interaction. The
shorter-range assertion is recorded in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex` and
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Simultaneous injectivity at a positive length \(S\) gives a positive
open-chain parent gap at every range \(R\geq S+1\), uniform over all
chain lengths \(N\geq R\). Primitive normalization, separation of blocks,
and equality of the open-chain kernel with the boundary-condition space are
derived internally. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2
and Section 6; arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈
      (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  let T := toTensorFromBlocks (d := d) (μ := μ) B
  have hKernel : ∀ L N : ℕ, S + 1 ≤ L → L ≤ N →
      LinearMap.ker (openParentHamiltonianES T L N) = groundSpaceES T N :=
    fun L N hSL hLN ↦
      ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
        μ B hμ hS hSpanB hSL hLN
  obtain ⟨p, hRp, hp, γ, hγ, hLong⟩ :=
    exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_all_of_isPrimitiveMPS
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) R
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_parentInteractionES_openParentHamiltonianES_comparison
      T (hKernel R (2 * p) hR (by omega))
  have hEventual := openParentHamiltonianES_gap_of_long_gap T
    (by omega : 0 < R) (by omega : R ≤ 2 * p) hκ hγ hLocal
    (fun N hN ↦ hKernel R N hR (by omega))
    (fun N hN ↦ hKernel (2 * p) N (by omega) hN)
    (fun N hN v hv ↦ hLong N v (by rwa [hKernel (2 * p) N (by omega) hN]))
  obtain ⟨δ, hδ, hGapB⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ R ≤ N → ∀ v ∈ (groundSpaceES T N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES T R N v‖)
    (fun N γ η hle hgap hN v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap hN v hv))
    (fun N ↦ (LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES T R N)).imp fun η h ↦
        ⟨h.1, fun hN v hv ↦ h.2 v (by rwa [hKernel R N hR hN])⟩)
    (div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (by omega)))
    (fun N hN _ ↦ hEventual N hN)
  have hLocalGS : ∀ L, groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      groundSpace T L :=
    fun L ↦ groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L)
  refine ⟨δ, hδ, ?_⟩
  exact fun N hN ↦ by
    simpa only [openParentHamiltonianES_eq_of_groundSpace_eq (hLocalGS R) N,
      groundSpaceES, hLocalGS N] using hGapB N hN

end MPSTensor
