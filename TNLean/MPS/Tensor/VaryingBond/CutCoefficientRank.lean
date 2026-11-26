/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.CutRank
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationCuts

/-!
# Coordinates of physical cut ranks

The cut matrix `ManyBody.cutMatrix (leftBlock N k) ψ` indexes the sites before the cut by the
members of the left block `leftBlock N k`. The minimal-representation coefficient matrix
indexes them by the sites `s` with `s < k`, and the remaining sites by the sites `s` with
`k ≤ s`. Both index the same sites, so at every cut `k` the two matrices differ only by
reindexing, and their ranks are equal, without a condition on the cut position, the local
dimension or the coefficient tensor.

Numbering the sites of the left block by `Fin k`, for `k ≤ N`, reads its configurations as
configurations of a chain of `k` sites.

Source: the minimal representation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the Schmidt cut-rank
interpretation is arXiv:quant-ph/0608197, local
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 444--458.
-/

namespace MPSPreparation

open TNLean.MPS.AreaLaw (leftBlock mem_leftBlock)

variable {d N k : ℕ}

/-- Numbered prefix sites are identified with the actual sites before a
valid cut. Source: Section 5 of the exact MPU circuit note. -/
def cutPrefixSiteEquiv (hk : k ≤ N) : Fin k ≃ {s : Fin N // s.val < k} where
  toFun i := ⟨Fin.castLE hk i, i.isLt⟩
  invFun s := ⟨s.val.val, s.property⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

/-- Numbered suffix sites are identified with the actual sites after a
valid cut, by adding the cut position. Source: Section 5 of the exact
MPU circuit note. -/
def cutSuffixSiteEquiv (hk : k ≤ N) : Fin (N - k) ≃ {s : Fin N // k ≤ s.val} where
  toFun i := ⟨⟨k + i.val, by have := i.isLt; omega⟩, Nat.le_add_right k i.val⟩
  invFun s := ⟨s.val.val - k, by have := s.val.isLt; have := s.property; omega⟩
  left_inv i := Fin.ext (by dsimp; omega)
  right_inv s := Subtype.ext (Fin.ext (by dsimp; have := s.property; omega))

/-- Prefix configurations in the two cut-coordinate conventions.
Source: Section 5 of the exact MPU circuit note. -/
def cutPrefixConfigEquiv (hk : k ≤ N) : (Fin k → Fin d) ≃ CutPrefixConfig d N k :=
  Equiv.arrowCongr (cutPrefixSiteEquiv hk) (Equiv.refl (Fin d))

/-- Suffix configurations in the two cut-coordinate conventions.
Source: Section 5 of the exact MPU circuit note. -/
def cutSuffixConfigEquiv (hk : k ≤ N) :
    (Fin (N - k) → Fin d) ≃ CutSuffixConfig d N k :=
  Equiv.arrowCongr (cutSuffixSiteEquiv hk) (Equiv.refl (Fin d))

variable (d N k) in
/-- The configurations of the left block are the prefix configurations: both are indexed by the
sites before the cut. Source: Section 5 of the exact MPU circuit note. -/
def leftBlockConfigEquiv :
    ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (leftBlock N k) ≃ CutPrefixConfig d N k :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight fun _ ↦ mem_leftBlock) (Equiv.refl (Fin d))

variable (d N k) in
/-- The configurations outside the left block are the suffix configurations: both are indexed
by the sites from the cut on. Source: Section 5 of the exact MPU circuit note. -/
def leftBlockComplConfigEquiv :
    ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (leftBlock N k) ≃ CutSuffixConfig d N k :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight fun _ ↦ by simp only [mem_leftBlock, not_lt])
    (Equiv.refl (Fin d))

/-- At every physical cut, the finite-chain coefficient matrix is the cut matrix across the left
block after the reindexing of both configuration spaces.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`
and arXiv:quant-ph/0608197, lines 444--458. -/
theorem cutCoefficientMatrix_eq_reindex_cutMatrix (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    cutCoefficientMatrix ψ k =
      (ManyBody.cutMatrix (leftBlock N k) ψ).reindex (leftBlockConfigEquiv d N k)
        (leftBlockComplConfigEquiv d N k) := by
  ext u v
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, ManyBody.cutMatrix_apply]
  apply congrArg ψ
  funext s
  by_cases hs : s.val < k
  · rw [ManyBody.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.mpr hs), dite_eq_left hs]
    rfl
  · rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ fun h ↦ hs (mem_leftBlock.mp h),
      dite_eq_right hs]
    rfl

/-- The minimal-representation coefficient rank is the Schmidt cut rank across the left block
at every cut. No cut-position, local-dimension or nonzero-tensor hypothesis is needed.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex` and
arXiv:quant-ph/0608197, lines 456--458. -/
theorem cutCoefficientRank_eq_cutRank (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    cutCoefficientRank ψ k = ManyBody.cutRank (leftBlock N k) ψ := by
  rw [cutCoefficientRank, ManyBody.cutRank, cutCoefficientMatrix_eq_reindex_cutMatrix ψ k,
    Matrix.rank_reindex]

end MPSPreparation
