/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.TranslationInvariantUniqueness
import TNLean.MPS.Preparation.CutCoefficientRank

/-!
# Exact physical cut ranks of injective periodic tensors

The actual coefficient matrix across a physical cut factors through the
left and right virtual cut vectors. When condition C1 holds on both sides,
the right factor has a right inverse, the physical column space equals
the span of the left cut vectors, and the cut rank is exactly the square
of the virtual dimension. For a canonical tensor, C1 at one length
propagates to every longer length after removing the positive block weight.
Thus every cut with sufficiently long prefix and suffix has the doubled
bond dimension used in the quadratic reconstruction window.

This supplies the physical rank and column-space step, rather than
assuming an invertible window gauge or a solution of system (S). The
comparison with a prescribed unique OBC canonical window remains separate.

Source: PGVWC07, arXiv:quant-ph/0608197, the proposition on condition C1,
MPSarchive.tex lines 911--931, and Theorem 8, lines 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators

namespace MPSTensor

variable {d D N k : ℕ}

/-- The actual physical cut matrix is the product of its left and right
virtual cut factors, with the column-first virtual convention of the
condition-C1 proof. No injectivity hypothesis is needed.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
theorem cutMatrix_mpv_eq_cutVector_mul (A : MPSTensor d D) (hk : k ≤ N) :
    cutMatrix (mpv A (N := N)) k =
      (fun σ a ↦ leftCutVector A k a σ) *
        (fun a τ ↦ rightCutVector A (N - k) a τ) := by
  classical
  ext σ τ
  have heval := eval_cutConfig (fun _ : Fin N ↦ A) hk σ τ
  rw [MPSChainTensor.eval_const] at heval
  have hleft : (List.ofFn fun p : Fin k ↦ A (σ p)).prod =
      Kraus.evalWord A (List.ofFn σ) :=
    (MPSChainTensor.eval_eq_prod_ofFn (fun _ : Fin k ↦ A) σ).symm.trans
      (MPSChainTensor.eval_const A σ)
  have hright : (List.ofFn fun p : Fin (N - k) ↦ A (τ p)).prod =
      Kraus.evalWord A (List.ofFn τ) :=
    (MPSChainTensor.eval_eq_prod_ofFn (fun _ : Fin (N - k) ↦ A) τ).symm.trans
      (MPSChainTensor.eval_const A τ)
  change Kraus.evalWord A (List.ofFn (cutConfig σ τ)) = _ at heval
  rw [hleft, hright] at heval
  change Matrix.trace (Kraus.evalWord A (List.ofFn (cutConfig σ τ))) = _
  rw [heval, ← Kraus.evalWord_append]
  exact coeff_append_eq_sum_cutVector A σ τ

/-- Under C1 on the suffix, its actual virtual cut factor has a right
inverse. This reads the left virtual coefficient from the physical suffix.
Source: the independent right cut vectors in PGVWC07, lines 928--931. -/
theorem exists_rightInverse_rightCutVector {A : MPSTensor d D} {m : ℕ}
    (hC1 : Kraus.IsNBlkInjective A m) :
    ∃ S : Matrix (Fin m → Fin d) (Fin D × Fin D) ℂ,
      (fun a τ ↦ rightCutVector A m a τ) * S = 1 := by
  classical
  let G : Matrix (Fin D × Fin D) (Fin m → Fin d) ℂ := rightCutVector A m
  have hcols : LinearIndependent ℂ Gᵀ.col := linearIndependent_rightCutVector hC1
  have hinj := Matrix.mulVec_injective_iff.mpr hcols
  obtain ⟨T, hT⟩ := Gᵀ.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hmatrix : LinearMap.toMatrix' T * Gᵀ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hT
  refine ⟨(LinearMap.toMatrix' T)ᵀ, ?_⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]
    using congrArg Matrix.transpose hmatrix

/-- When the suffix satisfies C1, the physical prefix column space is
exactly the span of the left virtual cut vectors. The reverse inclusion
is derived from an actual right inverse of the suffix factor.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
theorem span_cutMatrix_mpv_cols_eq {A : MPSTensor d D} (hk : k ≤ N)
    (hC1 : Kraus.IsNBlkInjective A (N - k)) :
    Submodule.span ℂ (Set.range (cutMatrix (mpv A (N := N)) k).col) =
      Submodule.span ℂ (Set.range (leftCutVector A k)) := by
  classical
  let F : Matrix (Fin k → Fin d) (Fin D × Fin D) ℂ :=
    fun σ a ↦ leftCutVector A k a σ
  let G : Matrix (Fin D × Fin D) (Fin (N - k) → Fin d) ℂ :=
    rightCutVector A (N - k)
  obtain ⟨S, hS⟩ := exists_rightInverse_rightCutVector hC1
  have hfactor : cutMatrix (mpv A (N := N)) k = F * G :=
    cutMatrix_mpv_eq_cutVector_mul A hk
  have hrecover : (F * G) * S = F := by rw [Matrix.mul_assoc, hS, Matrix.mul_one]
  change Submodule.span ℂ (Set.range (cutMatrix (mpv A (N := N)) k).col) =
    Submodule.span ℂ (Set.range F.col)
  simp only [← Matrix.range_mulVecLin]
  apply le_antisymm
  · rw [hfactor, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range G.mulVecLin F.mulVecLin
  · rw [← hrecover, Matrix.mulVecLin_mul, ← hfactor]
    exact LinearMap.range_comp_le_range S.mulVecLin
      (cutMatrix (mpv A (N := N)) k).mulVecLin

/-- The actual physical prefix column space has the virtual left cut
vectors as a basis. This basis is derived from the coefficient matrix,
not supplied as doubled-window data.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
noncomputable def periodicCutBasis {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k)) :
    Module.Basis (Fin D × Fin D) ℂ
      (Submodule.span ℂ (Set.range (cutMatrix (mpv A (N := N)) k).col)) :=
  (Module.Basis.span (linearIndependent_leftCutVector hleft)).map
    (LinearEquiv.ofEq _ _ (span_cutMatrix_mpv_cols_eq hk hright).symm)

/-- The derived physical cut basis retains the actual virtual coefficients.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
@[simp] theorem periodicCutBasis_apply {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k))
    (a : Fin D × Fin D) (σ : Fin k → Fin d) :
    (periodicCutBasis hk hleft hright a).val σ = leftCutVector A k a σ := rfl

/-- Condition C1 on both sides makes the actual physical Schmidt cut
rank exactly the squared virtual dimension.
Source: PGVWC07, proposition on C1, MPSarchive.tex lines 911--931. -/
theorem cutRank_mpv_eq_of_isNBlkInjective {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k)) :
    cutRank (mpv A (N := N)) k = D * D := by
  classical
  rw [cutRank, Matrix.rank_eq_finrank_span_cols, span_cutMatrix_mpv_cols_eq hk hright]
  have hrank := (linearIndependent_leftCutVector hleft).rank_matrix
  simpa only [Matrix.rank_eq_finrank_span_row, Fintype.card_prod, Fintype.card_fin]
    using hrank

/-- A canonical tensor satisfying C1 at one length satisfies it at all
longer lengths, including when its single canonical block has a positive
weight different from one. The weight is removed only inside the proof.
Source: PGVWC07, MPSarchive.tex lines 895--919. -/
theorem isNBlkInjective_of_le_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L m : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hLm : L ≤ m) : Kraus.IsNBlkInjective A m := by
  classical
  obtain ⟨C⟩ := hA
  obtain ⟨λ, hλ, _, hsum⟩ := C.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hλ0 : (λ : ℂ) ≠ 0 := by exact_mod_cast hλ.ne'
  let B : MPSTensor d D := fun i ↦ (λ : ℂ)⁻¹ • A i
  have hB : ∑ i, B i * (B i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hλ hsum
  have hBL : Kraus.IsNBlkInjective B L :=
    isNBlkInjective_smul _ (inv_ne_zero hλ0) hC1
  have hBm := isNBlkInjective_of_le_of_unital hB hBL hLm
  have hscaled := isNBlkInjective_smul (λ : ℂ) hλ0 hBm
  simpa only [B, smul_smul, mul_inv_cancel₀ hλ0, one_smul] using hscaled

/-- Every interior cut of a canonical C1 tensor has doubled virtual
rank once both its physical sides reach the C1 length. This derives the
window bond sizes used in the first clause of quadratic reconstruction.
Source: PGVWC07, MPSarchive.tex lines 911--931 and 1139--1169. -/
theorem cutRank_mpv_eq_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hk : k ≤ N) (hleft : L ≤ k) (hright : L ≤ N - k) :
    cutRank (mpv A (N := N)) k = D * D :=
  cutRank_mpv_eq_of_isNBlkInjective hk
    (isNBlkInjective_of_le_of_canonical hA hC1 hleft)
    (isNBlkInjective_of_le_of_canonical hA hC1 hright)

/-- The same exact rank in the actual-site cut-coordinate convention of
the minimal OBC construction. No OBC bond or rank equality is supplied.
Source: PGVWC07, MPSarchive.tex lines 911--931 and 1139--1169. -/
theorem cutCoefficientRank_mpv_eq_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hk : k ≤ N) (hleft : L ≤ k) (hright : L ≤ N - k) :
    cutCoefficientRank (mpv A (N := N)) k = D * D := by
  rw [cutCoefficientRank_eq_cutRank _ hk]
  exact cutRank_mpv_eq_of_canonical hA hC1 hk hleft hright

/-- Every one of the endpoint-inclusive cuts of the reconstruction window
has rank exactly the doubled virtual dimension, derived from the source
size regime and C1. In particular the two endpoint ranks are not assumed.
Source: PGVWC07, MPSarchive.tex lines 1002--1012 and 1139--1169. -/
theorem quadraticWindow_cutCoefficientRank_eq [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (j : Fin (D ^ 4 + 1)) :
    cutCoefficientRank (mpv A (N := N)) (L + j.val) = D * D := by
  have hj := j.isLt
  exact cutCoefficientRank_mpv_eq_of_canonical hA hC1 (by omega) (by omega) (by omega)

end MPSTensor
