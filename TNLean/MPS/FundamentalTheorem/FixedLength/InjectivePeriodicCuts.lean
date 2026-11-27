/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.FixedLength.TranslationInvariantUniqueness
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationCuts
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Exact physical cut ranks of injective periodic tensors

The actual coefficient matrix across a physical cut factors through the
left and right virtual cut vectors. When condition C1 holds on both sides,
the right factor has a right inverse, the physical column space equals
the span of the left cut vectors, and the cut rank is exactly the square
of the virtual dimension. For a canonical tensor, C1 at one length
propagates to every longer length after removing the positive block weight.
Thus every cut with sufficiently long prefix and suffix has the doubled
bond dimension used in the quadratic reconstruction window. Slicing one more physical letter
has, in these virtual cut bases, matrix equal to that letter tensored with the identity on the
spectator virtual index.

This supplies the physical rank and column-space step, rather than
assuming an invertible window gauge or a solution of system (S). The
comparison with a prescribed unique OBC canonical window remains separate.

Source: PGVWC07, arXiv:quant-ph/0608197, the proposition on condition C1,
MPSarchive.tex lines 911--931, the window gauges of lines 1080--1086, and Theorem 8,
lines 1139--1169.
-/

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

open MPTensor

open Matrix MPSPreparation
open ManyBody (interval mem_interval cutMatrix cutRank RegionConfig ComplConfig)
open scoped BigOperators Kronecker

namespace MPSTensor

variable {d D N k : ℕ}

/-- The actual physical cut matrix across the left block is the product of its left and right
virtual cut factors, read on the first `k` and the last `N - k` sites, with the column-first
virtual convention of the condition-C1 proof. No injectivity hypothesis is needed.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
theorem cutMatrix_mpv_eq_cutVector_mul (A : MPSTensor d D) (hk : k ≤ N) :
    cutMatrix (interval N 0 k) (mpv A (N := N)) =
      Matrix.of (fun σ a ↦
          leftCutVector A k a ((cutPrefixConfigEquiv hk).symm σ)) *
        Matrix.of fun a τ ↦ rightCutVector A (N - k) a
          ((cutSuffixConfigEquiv hk).symm τ) := by
  classical
  ext σ τ
  have heval := eval_cutEquiv_symm (fun _ : Fin N ↦ A) hk σ τ
  rw [MPSChainTensor.eval_const] at heval
  have hleft : (List.ofFn fun p : Fin k ↦
      A (σ ⟨Fin.castLE hk p, mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩⟩)).prod =
      Kraus.evalWord A (List.ofFn
        ((cutPrefixConfigEquiv hk).symm σ)) :=
    (MPSChainTensor.eval_eq_prod_ofFn (fun _ : Fin k ↦ A) _).symm.trans
      (MPSChainTensor.eval_const A _)
  have hright : (List.ofFn fun q : Fin (N - k) ↦ A (τ ⟨⟨k + q.val, by omega⟩,
      fun h ↦ by have := (mem_interval.mp h).2; simp at this⟩)).prod =
      Kraus.evalWord A (List.ofFn
        ((cutSuffixConfigEquiv hk).symm τ)) :=
    (MPSChainTensor.eval_eq_prod_ofFn (fun _ : Fin (N - k) ↦ A) _).symm.trans
      (MPSChainTensor.eval_const A _)
  rw [hleft, hright] at heval
  change Matrix.trace (Kraus.evalWord A
    (List.ofFn ((ManyBody.cutEquiv _ (interval N 0 k)).symm (σ, τ)))) = _
  rw [heval, ← Kraus.evalWord_append]
  exact coeff_append_eq_sum_cutVector A _ _

/-- Under C1 on the suffix, its actual virtual cut factor has a right
inverse. This reads the left virtual coefficient from the physical suffix.
Source: the independent right cut vectors in PGVWC07, lines 928--931. -/
theorem exists_rightInverse_rightCutVector {A : MPSTensor d D} {m : ℕ}
    (hC1 : Kraus.IsNBlkInjective A m) :
    ∃ S : Matrix (Fin m → Fin d) (Fin D × Fin D) ℂ,
      Matrix.of (rightCutVector A m) * S = 1 := by
  classical
  let G : Matrix (Fin D × Fin D) (Fin m → Fin d) ℂ := Matrix.of (rightCutVector A m)
  have hcols : LinearIndependent ℂ Gᵀ.col := linearIndependent_rightCutVector hC1
  have hinj := Matrix.mulVec_injective_iff.mpr hcols
  obtain ⟨T, hT⟩ := Gᵀ.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hmatrix : LinearMap.toMatrix' T * Gᵀ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hT
  refine ⟨(LinearMap.toMatrix' T)ᵀ, ?_⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]
    using congrArg Matrix.transpose hmatrix

/-- Under C1 on the prefix, the left virtual cut vectors read on the left block are linearly
independent. Source: PGVWC07, MPSarchive.tex lines 936--949. -/
theorem linearIndependent_leftCutVector_interval {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) :
    LinearIndependent ℂ fun a σ ↦
      leftCutVector A k a ((cutPrefixConfigEquiv hk).symm σ) :=
  (linearIndependent_leftCutVector hleft).map' (LinearEquiv.funCongrLeft ℂ ℂ
    (cutPrefixConfigEquiv hk).symm).toLinearMap
    (LinearEquiv.ker _)

/-- When the suffix satisfies C1, the physical column space of the cut matrix across the left
block is exactly the span of the left virtual cut vectors. The reverse inclusion is derived from
an actual right inverse of the suffix factor.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
theorem span_cutMatrix_mpv_cols_eq {A : MPSTensor d D} (hk : k ≤ N)
    (hC1 : Kraus.IsNBlkInjective A (N - k)) :
    Submodule.span ℂ (Set.range (cutMatrix (interval N 0 k) (mpv A (N := N))).col) =
      Submodule.span ℂ (Set.range fun a σ ↦
        leftCutVector A k a ((cutPrefixConfigEquiv hk).symm σ)) := by
  classical
  let e := (cutSuffixConfigEquiv (d := d) hk).symm
  let F : Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
      (Fin D × Fin D) ℂ := Matrix.of fun σ a ↦
    leftCutVector A k a ((cutPrefixConfigEquiv hk).symm σ)
  let G : Matrix (Fin D × Fin D) (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
      ℂ := (Matrix.of (rightCutVector A (N - k))).submatrix id e
  obtain ⟨S, hS⟩ := exists_rightInverse_rightCutVector hC1
  have hfactor : cutMatrix (interval N 0 k) (mpv A (N := N)) = F * G :=
    cutMatrix_mpv_eq_cutVector_mul A hk
  have hGS : G * S.submatrix e id = 1 := by
    change (Matrix.of (rightCutVector A (N - k))).submatrix id e * S.submatrix e id = 1
    rw [Matrix.submatrix_mul_equiv, hS, Matrix.submatrix_id_id]
  have hrecover : (F * G) * S.submatrix e id = F := by
    rw [Matrix.mul_assoc, hGS, Matrix.mul_one]
  change Submodule.span ℂ (Set.range (cutMatrix (interval N 0 k) (mpv A (N := N))).col) =
    Submodule.span ℂ (Set.range F.col)
  simp only [← Matrix.range_mulVecLin]
  apply le_antisymm
  · rw [hfactor, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range G.mulVecLin F.mulVecLin
  · rw [← hrecover, Matrix.mulVecLin_mul, ← hfactor]
    exact LinearMap.range_comp_le_range (S.submatrix e id).mulVecLin
      (cutMatrix (interval N 0 k) (mpv A (N := N))).mulVecLin

/-- The actual physical column space of the cut matrix across the left block has the virtual
left cut vectors as a basis. This basis is derived from the coefficient matrix, not supplied as
doubled-window data.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
noncomputable def periodicCutBasis {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k)) :
    Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace (mpv A (N := N)) k) :=
  (Module.Basis.span (linearIndependent_leftCutVector_interval hk hleft)).map
    (LinearEquiv.ofEq _ _ (span_cutMatrix_mpv_cols_eq hk hright).symm)

/-- The derived physical cut basis retains the actual virtual coefficients.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
@[simp] theorem periodicCutBasis_apply {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k))
    (a : Fin D × Fin D) (σ : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    (periodicCutBasis hk hleft hright a).val σ =
      leftCutVector A k a ((cutPrefixConfigEquiv hk).symm σ) := by
  simp only [periodicCutBasis, Module.Basis.map_apply]
  exact congrFun (congrArg Subtype.val
    (Module.Basis.span_apply (linearIndependent_leftCutVector_interval hk hleft) a)) σ

private theorem cutPrefixConfigEquiv_extend (hk : k + 1 ≤ N)
    (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (i : Fin d) :
    (cutPrefixConfigEquiv hk).symm (extendCutPrefix k u i) =
      Fin.append ((cutPrefixConfigEquiv (by omega : k ≤ N)).symm u)
        (fun _ : Fin 1 ↦ i) := by
  funext p
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
  · rw [Fin.append_left]
    change extendCutPrefix k u i (cutPrefixSiteEquiv hk (Fin.castAdd 1 j)) =
      u (cutPrefixSiteEquiv (by omega) j)
    unfold extendCutPrefix
    split_ifs with h
    · rfl
    · exact absurd j.isLt h
  · rw [Fin.append_right]
    change extendCutPrefix k u i (cutPrefixSiteEquiv hk (Fin.natAdd k j)) = i
    unfold extendCutPrefix
    split_ifs with h
    · exact absurd h (by simp [cutPrefixSiteEquiv])
    · rfl

/-- Actual coordinate slicing in the virtual cut bases has the
amplified letter matrix. This is the doubled-bond local relation from
which the quadratic window gauges are obtained by changing cut bases.
Source: PGVWC07, MPSarchive.tex lines 1080--1086 and 1139--1152. -/
theorem toMatrix_cutSlice_periodicCutBasis {A : MPSTensor d D}
    (hk : k + 1 ≤ N) (hleft : Kraus.IsNBlkInjective A k)
    (hright : Kraus.IsNBlkInjective A (N - k))
    (hleftNext : Kraus.IsNBlkInjective A (k + 1))
    (hrightNext : Kraus.IsNBlkInjective A (N - (k + 1))) (i : Fin d) :
    LinearMap.toMatrix (periodicCutBasis hk hleftNext hrightNext)
      (periodicCutBasis (by omega : k ≤ N) hleft hright)
      (cutSlice (mpv A (N := N)) k i) = A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  let C := periodicCutBasis (by omega : k ≤ N) hleft hright
  let C' := periodicCutBasis hk hleftNext hrightNext
  have hslice (a : Fin D × Fin D) :
      cutSlice (mpv A (N := N)) k i (C' a) =
        ∑ b : Fin D × Fin D, (A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) b a • C b := by
    apply Subtype.ext
    funext u
    change (C' a).val (extendCutPrefix k u i) = _
    simp only [C', C, periodicCutBasis_apply, cutPrefixConfigEquiv_extend hk,
      leftCutVector_append_single, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [Matrix.one_apply, Fintype.sum_prod_type, mul_comm]
  ext b a
  rw [LinearMap.toMatrix_apply, hslice]
  simp [C, Finsupp.single_apply]

/-- Condition C1 on both sides makes the actual physical Schmidt cut
rank exactly the squared virtual dimension.
Source: PGVWC07, proposition on C1, MPSarchive.tex lines 911--931. -/
theorem cutRank_mpv_eq_of_isNBlkInjective {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k)) :
    cutRank (interval N 0 k) (mpv A (N := N)) = D * D := by
  classical
  rw [ManyBody.cutRank, Matrix.rank_eq_finrank_span_cols, span_cutMatrix_mpv_cols_eq hk hright,
    finrank_span_eq_card (linearIndependent_leftCutVector_interval hk hleft)]
  simp only [Fintype.card_prod, Fintype.card_fin]

/-- A canonical tensor satisfying C1 at one length satisfies it at all
longer lengths, including when its single canonical block has a positive
weight different from one. The weight is removed only inside the proof.
Source: PGVWC07, MPSarchive.tex lines 895--919. -/
theorem isNBlkInjective_of_le_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L m : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hLm : L ≤ m) : Kraus.IsNBlkInjective A m := by
  classical
  obtain ⟨C⟩ := hA
  obtain ⟨lam, hlam, _, hsum⟩ := C.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  let B : MPSTensor d D := fun i ↦ (lam : ℂ)⁻¹ • A i
  have hB : ∑ i, B i * (B i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hlam hsum
  have hBL : Kraus.IsNBlkInjective B L :=
    (isNBlkInjective_smul_iff (inv_ne_zero hlam0) A L).2 hC1
  have hBm := Kraus.wordSpan_eq_top_of_ge_of_unital _ hB hBL hLm
  exact (isNBlkInjective_smul_iff (inv_ne_zero hlam0) A m).1 hBm

/-- Every interior cut of a canonical C1 tensor has doubled virtual
rank once both its physical sides reach the C1 length. This derives the
window bond sizes used in the first clause of quadratic reconstruction.
Source: PGVWC07, MPSarchive.tex lines 911--931 and 1139--1169. -/
theorem cutRank_mpv_eq_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hk : k ≤ N) (hleft : L ≤ k) (hright : L ≤ N - k) :
    cutRank (interval N 0 k) (mpv A (N := N)) = D * D :=
  cutRank_mpv_eq_of_isNBlkInjective hk
    (isNBlkInjective_of_le_of_canonical hA hC1 hleft)
    (isNBlkInjective_of_le_of_canonical hA hC1 hright)

/-- Every one of the endpoint-inclusive cuts of the reconstruction window
has rank exactly the doubled virtual dimension, derived from the source
size regime and C1. In particular the two endpoint ranks are not assumed.
Source: PGVWC07, MPSarchive.tex lines 1002--1012 and 1139--1169. -/
theorem quadraticWindow_cutRank_eq [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (j : Fin (D ^ 4 + 1)) :
    cutRank (interval N 0 (L + j.val)) (mpv A (N := N)) = D * D := by
  have hj := j.isLt
  exact cutRank_mpv_eq_of_canonical hA hC1 (by omega) (by omega) (by omega)

end MPSTensor
