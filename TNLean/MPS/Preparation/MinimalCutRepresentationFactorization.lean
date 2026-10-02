/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentation
import TNLean.MPS.MPU.AffineFactorizationRank

/-!
# Spanning factors of the minimal physical cuts

The basis construction of a minimal open-boundary chain gives explicit
prefix and suffix factors of each physical coefficient flattening. Their
ranks equal the bond dimension, and consequently their physical rows and
columns span the whole bond space. The factors obey the constructed site
recurrences and have scalar endpoint factors equal to one.

The final existence theorem attaches these certificates to the same exact
open-boundary representation. It assumes a nonzero tensor of positive length
and an upper bound on its physical cut ranks, with no supplied spanning data.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- The prefix factor whose columns are the chosen cut-basis vectors, evaluated
on physical prefix configurations.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutPrefixMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    Matrix (CutPrefixConfig d N k) (Fin (cutRank ψ k)) ℂ :=
  fun u q ↦ (B k q).val u

/-- The suffix factor whose columns are the coordinates of the physical
coefficient columns in the chosen cut basis.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutSuffixMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    Matrix (Fin (cutRank ψ k)) (CutSuffixConfig d N k) ℂ :=
  fun q v ↦ (B k).repr
    ⟨(cutCoefficientMatrix ψ k).col v, Submodule.subset_span ⟨v, rfl⟩⟩ q

/-- The physical coefficient flattening is the product of its cut-basis
prefix and suffix factors.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutCoefficientMatrix_eq_prefix_mul_suffix {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    cutCoefficientMatrix ψ k = cutPrefixMatrix ψ B k * cutSuffixMatrix ψ B k := by
  classical
  ext u v
  let w : cutColumnSpace ψ k :=
    ⟨(cutCoefficientMatrix ψ k).col v, Submodule.subset_span ⟨v, rfl⟩⟩
  have h := congrArg (fun x : cutColumnSpace ψ k ↦ x.val u) ((B k).sum_repr w)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  change (∑ q, (B k).repr w q * (B k q).val u) = cutCoefficientMatrix ψ k u v at h
  change cutCoefficientMatrix ψ k u v =
    ∑ q, (B k q).val u * (B k).repr w q
  simpa only [mul_comm] using h.symm

/-- The prefix factor has full column rank equal to the physical cut rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixMatrix_rank {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    (cutPrefixMatrix ψ B k).rank = cutRank ψ k := by
  have h : cutRank ψ k ≤ (cutPrefixMatrix ψ B k).rank := by
    change (cutCoefficientMatrix ψ k).rank ≤ _
    rw [cutCoefficientMatrix_eq_prefix_mul_suffix ψ B k]
    exact Matrix.rank_mul_le_left _ _
  exact le_antisymm (by simpa only [Fintype.card_fin] using
    Matrix.rank_le_card_width (cutPrefixMatrix ψ B k)) h

/-- The suffix factor has full row rank equal to the physical cut rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSuffixMatrix_rank {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    (cutSuffixMatrix ψ B k).rank = cutRank ψ k := by
  have h : cutRank ψ k ≤ (cutSuffixMatrix ψ B k).rank := by
    change (cutCoefficientMatrix ψ k).rank ≤ _
    rw [cutCoefficientMatrix_eq_prefix_mul_suffix ψ B k]
    exact Matrix.rank_mul_le_right _ _
  exact le_antisymm (by simpa only [Fintype.card_fin] using
    Matrix.rank_le_card_height (cutSuffixMatrix ψ B k)) h

/-- The physical prefix rows and suffix columns span the full minimal bond
space. Both spans are derived from the physical coefficient rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixMatrix_rows_and_cutSuffixMatrix_cols_span {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    Submodule.span ℂ (Set.range (cutPrefixMatrix ψ B k).row) = ⊤ ∧
      Submodule.span ℂ (Set.range (cutSuffixMatrix ψ B k).col) = ⊤ := by
  apply MPUCircuit.spans_eq_top_of_rank_mul_eq_card
  rw [← cutCoefficientMatrix_eq_prefix_mul_suffix ψ B k]
  simp only [Fintype.card_fin]
  rfl

/-- The prefix factors propagate by the same physical slicing matrices
that define the minimal open-boundary chain.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixMatrix_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (k : ℕ) (i : Fin d) (u : CutPrefixConfig d N k) (q : Fin (cutRank ψ (k + 1))) :
    cutPrefixMatrix ψ B (k + 1) (extendCutPrefix k u i) q =
      (cutPrefixMatrix ψ B k * cutSiteMatrix ψ B k i) u q := by
  classical
  have h := congrArg (fun x : cutColumnSpace ψ k ↦ x.val u)
    ((B k).sum_repr (cutSlice ψ k i (B (k + 1) q)))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  change (B (k + 1) q).val (extendCutPrefix k u i) =
    ∑ p, (B k p).val u * cutSiteMatrix ψ B k i p q
  simp only [cutSiteMatrix, LinearMap.toMatrix_apply]
  change (∑ p, (B k).repr (cutSlice ψ k i (B (k + 1) q)) p * (B k p).val u) =
    (B (k + 1) q).val (extendCutPrefix k u i) at h
  simpa only [mul_comm] using h.symm

/-- Slicing a next-cut physical column gives the preceding physical column
with that letter adjoined to its suffix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSlice_column {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (k : ℕ) (i : Fin d) (v : CutSuffixConfig d N (k + 1)) :
    cutSlice ψ k i
      ⟨(cutCoefficientMatrix ψ (k + 1)).col v, Submodule.subset_span ⟨v, rfl⟩⟩ =
      ⟨(cutCoefficientMatrix ψ k).col (extendCutSuffix k i v),
        Submodule.subset_span ⟨extendCutSuffix k i v, rfl⟩⟩ := by
  apply Subtype.ext
  funext u
  exact cutCoefficientMatrix_adjacent ψ k u i v

/-- The suffix factors propagate by the same physical slicing matrices
that define the minimal open-boundary chain.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSuffixMatrix_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (k : ℕ) (i : Fin d) (v : CutSuffixConfig d N (k + 1)) :
    (cutSuffixMatrix ψ B k).col (extendCutSuffix k i v) =
      cutSiteMatrix ψ B k i *ᵥ (cutSuffixMatrix ψ B (k + 1)).col v := by
  have h := LinearMap.toMatrix_mulVec_repr (B (k + 1)) (B k) (cutSlice ψ k i)
    ⟨(cutCoefficientMatrix ψ (k + 1)).col v, Submodule.subset_span ⟨v, rfl⟩⟩
  rw [cutSlice_column] at h
  exact h.symm

/-- The coefficient flattening of the constructed open-boundary chain
factors through the same cut-basis prefix and suffix matrices.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalCutChain_cutCoefficientMatrix_factorization {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hbound : ∀ k : Fin (N + 1), cutRank ψ k.val ≤ D) (k : ℕ) :
    cutCoefficientMatrix (minimalCutChain ψ hψ B hbound).coeff k =
      cutPrefixMatrix ψ B k * cutSuffixMatrix ψ B k := by
  have hcoeff : (minimalCutChain ψ hψ B hbound).coeff = ψ :=
    funext (minimalCutChain_coeff ψ hψ B hB0 hBN hbound)
  rw [hcoeff]
  exact cutCoefficientMatrix_eq_prefix_mul_suffix ψ B k

/-- The prefix factor at the left endpoint is one when its basis vector
is normalized to one.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixMatrix_zero {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (u : CutPrefixConfig d N 0)
    (q : Fin (cutRank ψ 0)) : cutPrefixMatrix ψ B 0 u q = 1 := by
  exact congrFun (hB0 q) u

/-- The suffix factor at the right endpoint is one when its basis vector
is the complete coefficient tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSuffixMatrix_last {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hBN : ∀ q, (B N q).val = fullCutVector ψ) (v : CutSuffixConfig d N N)
    (q : Fin (cutRank ψ N)) : cutSuffixMatrix ψ B N q v = 1 := by
  have hw : (⟨(cutCoefficientMatrix ψ N).col v,
      Submodule.subset_span ⟨v, rfl⟩⟩ : cutColumnSpace ψ N) = B N q := by
    apply Subtype.ext
    funext u
    exact (cutCoefficientMatrix_last ψ u v).trans (congrFun (hBN q) u).symm
  change (B N).repr _ q = 1
  rw [hw, Module.Basis.repr_self]
  simp

/-- Every nonzero tensor of positive length with bounded physical cut ranks
admits an exact minimal open-boundary representation together with a full-rank
factorization at each physical cut. The prefix-row and suffix-column spans
are derived, with no additional minimality hypotheses.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_obcChainTensor_minimal_factorizations {d N D : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (hbound : ∀ k : Fin (N + 1), cutRank ψ k.val ≤ D) :
    ∃ A : OBCChainTensor d D N,
      (∀ k, A.bondDim k = cutRank ψ k.val) ∧ (∀ σ, A.coeff σ = ψ σ) ∧
      ∀ k : Fin (N + 1),
        ∃ F : Matrix (CutPrefixConfig d N k.val) (Fin (A.bondDim k)) ℂ,
        ∃ G : Matrix (Fin (A.bondDim k)) (CutSuffixConfig d N k.val) ℂ,
          cutCoefficientMatrix A.coeff k.val = F * G ∧
          F.rank = A.bondDim k ∧ G.rank = A.bondDim k ∧
          Submodule.span ℂ (Set.range F.row) = ⊤ ∧
          Submodule.span ℂ (Set.range G.col) = ⊤ := by
  obtain ⟨B, hB0, hBN⟩ := exists_cutBasisFamily_with_endpoints ψ hψ hN
  refine ⟨minimalCutChain ψ hψ B hbound, (fun _ ↦ rfl),
    minimalCutChain_coeff ψ hψ B hB0 hBN hbound, ?_⟩
  intro k
  change ∃ F : Matrix (CutPrefixConfig d N k.val) (Fin (cutRank ψ k.val)) ℂ,
    ∃ G : Matrix (Fin (cutRank ψ k.val)) (CutSuffixConfig d N k.val) ℂ,
      cutCoefficientMatrix (minimalCutChain ψ hψ B hbound).coeff k.val = F * G ∧
      F.rank = cutRank ψ k.val ∧ G.rank = cutRank ψ k.val ∧
      Submodule.span ℂ (Set.range F.row) = ⊤ ∧
      Submodule.span ℂ (Set.range G.col) = ⊤
  obtain ⟨hF, hG⟩ := cutPrefixMatrix_rows_and_cutSuffixMatrix_cols_span ψ B k.val
  exact ⟨cutPrefixMatrix ψ B k.val, cutSuffixMatrix ψ B k.val,
    minimalCutChain_cutCoefficientMatrix_factorization ψ hψ B hB0 hBN hbound k.val,
    cutPrefixMatrix_rank ψ B k.val, cutSuffixMatrix_rank ψ B k.val, hF, hG⟩

end MPSPreparation
