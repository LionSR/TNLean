/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CutRank
import TNLean.MPS.Preparation.MinimalCutRepresentationCuts

/-!
# Coordinates of physical cut ranks

The canonical cut matrix numbers the prefix sites by `Fin k` and the
suffix sites by `Fin (N - k)`. The minimal-representation coefficient
matrix instead indexes these sites by their actual subsets of `Fin N`.
For every valid cut `k ≤ N`, explicit site equivalences induce
configuration equivalences, and the two matrices differ only by reindexing.
Their ranks are consequently equal, without a condition on the local
dimension or the coefficient tensor.

Source: the minimal representation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the Schmidt cut-rank
interpretation is arXiv:quant-ph/0608197, local
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 444--458.
-/

namespace MPSPreparation

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

/-- At a valid physical cut, the finite-chain coefficient matrix is the
canonical cut matrix after the explicit configuration reindexing.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`
and arXiv:quant-ph/0608197, lines 444--458. -/
theorem cutCoefficientMatrix_eq_reindex_cutMatrix
    (ψ : (Fin N → Fin d) → ℂ) (hk : k ≤ N) :
    cutCoefficientMatrix ψ k =
      (cutMatrix ψ k).reindex (cutPrefixConfigEquiv hk) (cutSuffixConfigEquiv hk) := by
  ext u v
  apply congrArg ψ
  funext s
  by_cases hs : s.val < k
  case neg =>
    have hle : k ≤ s.val := Nat.le_of_not_lt hs
    simp [cutConfig, hs, cutSuffixConfigEquiv, Equiv.arrowCongr,
      cutSuffixSiteEquiv, Nat.add_sub_of_le hle]
  case pos =>
    simp [cutConfig, hs, cutPrefixConfigEquiv, Equiv.arrowCongr, cutPrefixSiteEquiv]

/-- The minimal-representation coefficient rank is the canonical Schmidt
cut rank at every valid cut. No local-dimension or nonzero-tensor
hypothesis is needed. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex` and
arXiv:quant-ph/0608197, lines 456--458. -/
theorem cutCoefficientRank_eq_cutRank (ψ : (Fin N → Fin d) → ℂ) (hk : k ≤ N) :
    cutCoefficientRank ψ k = cutRank ψ k := by
  rw [cutCoefficientRank, cutRank, cutCoefficientMatrix_eq_reindex_cutMatrix ψ hk,
    Matrix.rank_reindex]

end MPSPreparation
