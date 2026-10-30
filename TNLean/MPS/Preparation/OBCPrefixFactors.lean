/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CutCoefficientRank
import TNLean.MPS.Preparation.OBCCanonicalConfigurations

/-!
# Actual prefix factors of an arbitrary open-boundary representation

The physical prefix matrix is the actual product of the original site
matrices, restricted to the current virtual bond. Its adjacent-cut
recursion uses those original rectangular matrices. Every physical cut
coefficient column lies in its range, by the actual open-chain contraction.

Source: PGVWC07, arXiv:quant-ph/0608197, free-OBC and its local rectangular
maps, lines 461--522.
-/

open Matrix
open scoped BigOperators

namespace OBCChainTensor

open MPSPreparation

variable {d D N : ℕ} (B : OBCChainTensor d D N)

private def prefixProduct (k : Fin (N + 1)) (u : CutPrefixConfig d N k.val) :
    Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun p : Fin k.val ↦ B.zeroPad (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) p)
    (u ⟨Fin.castLE (Nat.lt_succ_iff.mp k.isLt) p, p.isLt⟩)).prod

/-- The actual physical prefix matrix of the supplied representation,
with columns indexed by its original virtual bond.
Source: PGVWC07, free-OBC, lines 461--522. -/
def physicalPrefixMatrix (k : Fin (N + 1)) :
    Matrix (CutPrefixConfig d N k.val) (Fin (B.bondDim k)) ℂ :=
  fun u a ↦ prefixProduct B k u ⟨0, B.bondBound_pos⟩ (Fin.castLE (B.bondDim_le k) a)

private theorem prefixProduct_outside (k : Fin (N + 1))
    (u : CutPrefixConfig d N k.val) (γ : Fin D) (hγ : B.bondDim k ≤ γ.val) :
    prefixProduct B k u ⟨0, B.bondBound_pos⟩ γ = 0 := by
  classical
  rcases k with ⟨k, hk⟩
  cases k with
  | zero =>
      have hγ0 : γ.val ≠ 0 := by
        have h := B.left_dim
        change B.bondDim 0 ≤ γ.val at hγ
        rw [h] at hγ
        omega
      simp only [prefixProduct, List.ofFn_zero, List.prod_nil]
      exact Matrix.one_apply_ne (fun h ↦ hγ0 (Fin.ext_iff.mp h).symm)
  | succ k =>
      rw [prefixProduct, List.ofFn_succ', List.prod_concat, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro β _
      apply mul_eq_zero_of_right
      apply Matrix.zeroPad_apply_eq_zero
      intro hlt
      have heq : (Fin.castLE (Nat.lt_succ_iff.mp hk) (Fin.last k)).succ =
          (⟨k + 1, hk⟩ : Fin (N + 1)) := Fin.ext rfl
      have hcol := hlt.2
      change γ.val < B.bondDim _ at hcol
      rw [heq] at hcol
      exact (not_lt_of_ge hγ) hcol

private theorem prefixProduct_step (p : Fin N) (u : CutPrefixConfig d N p.val) (i : Fin d) :
    prefixProduct B p.succ (extendCutPrefix p.val u i) =
      prefixProduct B p.castSucc u * B.zeroPad p i := by
  classical
  rw [prefixProduct, List.ofFn_succ', List.prod_concat]
  apply congrArg₂ (· * ·)
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext q
    simp only [extendCutPrefix, Fin.val_castLE, Fin.val_castSucc, q.isLt, dite_true]
    rfl
  · simp only [extendCutPrefix, Fin.val_castLE, Fin.val_last, Nat.lt_irrefl, dite_false]
    rfl

/-- The actual arbitrary-representation prefix factors propagate by the
original site matrices. Source: PGVWC07, free-OBC, local maps in
lines 475--486 and the factorization proof in lines 490--522. -/
theorem physicalPrefixMatrix_step (p : Fin N) (u : CutPrefixConfig d N p.val)
    (i : Fin d) (q : Fin (B.bondDim p.succ)) :
    physicalPrefixMatrix B p.succ (extendCutPrefix p.val u i) q =
      (physicalPrefixMatrix B p.castSucc * B.tensor p i) u q := by
  classical
  change prefixProduct B p.succ (extendCutPrefix p.val u i) ⟨0, B.bondBound_pos⟩
    (Fin.castLE (B.bondDim_le p.succ) q) = _
  rw [prefixProduct_step]
  simp only [Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (B.bondDim_le p.castSucc)]
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · change prefixProduct B p.castSucc u ⟨0, B.bondBound_pos⟩ γ *
        Matrix.zeroPad D (B.tensor p i) γ (Fin.castLE (B.bondDim_le p.succ) q) = _
    rw [Matrix.zeroPad_apply_of_lt (β := Fin.castLE (B.bondDim_le p.succ) q) _ hγ q.isLt]
    rfl
  · rw [prefixProduct_outside B p.castSucc u γ (not_lt.mp hγ), zero_mul]

/-- The left endpoint prefix factor is the scalar identity in the
one-dimensional endpoint bond coordinates.
Source: PGVWC07, endpoint convention preceding Theorem thm:OBC-Vidal. -/
theorem physicalPrefixMatrix_zero (u : CutPrefixConfig d N 0) (q : Fin (B.bondDim 0)) :
    physicalPrefixMatrix B 0 u q = 1 := by
  have hq : q.val = 0 := by have := q.isLt; have := B.left_dim; omega
  change prefixProduct B 0 u ⟨0, B.bondBound_pos⟩ (Fin.castLE (B.bondDim_le 0) q) = 1
  simp only [prefixProduct, Fin.val_zero, List.ofFn_zero, List.prod_nil]
  simp [Matrix.one_apply, Fin.ext_iff, hq]

/-- The right endpoint prefix factor is the actual represented physical
state, including its complete complex amplitude.
Source: PGVWC07, the OBC contraction in free-OBC, lines 461--486. -/
theorem physicalPrefixMatrix_last (u : CutPrefixConfig d N N)
    (q : Fin (B.bondDim (Fin.last N))) :
    physicalPrefixMatrix B (Fin.last N) u q = B.coeff (finalCutPrefixEquiv d N u) := by
  have hq : q.val = 0 := by have := q.isLt; have := B.right_dim; omega
  have hfull : prefixProduct B (Fin.last N) u =
      MPSChainTensor.eval B.zeroPad (finalCutPrefixEquiv d N u) := by
    rw [MPSChainTensor.eval_eq_prod_ofFn]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext p
    rfl
  rw [coeff_eq_eval_zeroPad]
  change prefixProduct B (Fin.last N) u ⟨0, B.bondBound_pos⟩
    (Fin.castLE (B.bondDim_le (Fin.last N)) q) = _
  have hq' : Fin.castLE (B.bondDim_le (Fin.last N)) q = ⟨0, B.bondBound_pos⟩ := Fin.ext hq
  rw [hq', hfull]

/-- The actual physical suffix matrix of the supplied representation,
with rows indexed by its original virtual bond.
Source: PGVWC07, free-OBC, actual boundary contractions in lines 461--522. -/
def physicalSuffixMatrix (k : Fin (N + 1)) :
    Matrix (Fin (B.bondDim k)) (CutSuffixConfig d N k.val) ℂ :=
  fun a v ↦ (List.ofFn fun q : Fin (N - k.val) ↦
    B.zeroPad ⟨k.val + q.val, by have := q.isLt; omega⟩
      (v ⟨⟨k.val + q.val, by have := q.isLt; omega⟩, Nat.le_add_right _ _⟩)).prod
        (Fin.castLE (B.bondDim_le k) a) ⟨0, B.bondBound_pos⟩

/-- Every actual physical cut coefficient matrix factors through the
original virtual bond by the actual prefix and suffix contractions.
Source: PGVWC07, the OBC contraction in free-OBC, lines 461--486. -/
theorem cutCoefficientMatrix_eq_physicalPrefix_mul_suffix (k : Fin (N + 1)) :
    cutCoefficientMatrix B.coeff k.val = physicalPrefixMatrix B k * physicalSuffixMatrix B k := by
  classical
  have hk : k.val ≤ N := Nat.lt_succ_iff.mp k.isLt
  rw [cutCoefficientMatrix_eq_reindex_cutMatrix B.coeff hk]
  ext u v
  change cutMatrix B.coeff k.val ((cutPrefixConfigEquiv hk).symm u)
    ((cutSuffixConfigEquiv hk).symm v) = _
  rw [cutMatrix, coeff_eq_eval_zeroPad, eval_cutConfig _ hk]
  simp only [Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (B.bondDim_le k)]
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · rfl
  · change prefixProduct B k u ⟨0, B.bondBound_pos⟩ γ * _ = 0
    rw [prefixProduct_outside B k u γ (not_lt.mp hγ), zero_mul]

/-- The actual physical cut column space is contained in the range of
the original-representation prefix matrix. This supplies the rectangular
maps to a minimal representation without assuming a gauge or rank equality.
Source: PGVWC07, free-OBC, lines 461--522. -/
theorem cutColumnSpace_le_range_physicalPrefixMatrix (k : Fin (N + 1)) :
    cutColumnSpace B.coeff k.val ≤ LinearMap.range (physicalPrefixMatrix B k).mulVecLin := by
  rw [cutColumnSpace, ← Matrix.range_mulVecLin,
    cutCoefficientMatrix_eq_physicalPrefix_mul_suffix B k, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

end OBCChainTensor
