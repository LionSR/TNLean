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
theorem exists_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  let T := toTensorFromBlocks (d := d) (μ := μ) B
  have hKernel : ∀ L N : ℕ, S + 1 ≤ L → L ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction T L N).hamiltonian) =
          groundSpaceES T N :=
    fun L N hSL hLN ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
        μ B hμ hS hSpanB hSL hLN
  obtain ⟨p, hRp, hp, γ, hγ, hLong⟩ :=
    exists_ge_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_all_of_fixedPointGap
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) R
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison
      T (hKernel R (2 * p) hR (by omega))
  obtain ⟨δ, hδ, hGapB⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction T R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z)
    (fun N γ η hle hgap ↦ ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N ↦ ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction T R N))
    (div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (Nat.succ_pos (2 * p - R))))
    (fun N hN ↦ toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length T _
      (posSemidef_toMatrix'_parentInteraction T R) (by omega) hκ hγ hLocal
      (hKernel R N hR (by omega)) (hKernel (2 * p) N (by omega) hN) (hLong N))
  have hLocalGS : groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) R = groundSpace T R :=
    groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ (fun j ↦ hGS j R)
  refine ⟨δ, hδ, fun N _ ↦ ?_⟩
  rw [parentChainInteraction_eq_of_groundSpace_eq hLocalGS N]
  exact hGapB N

end MPSTensor
