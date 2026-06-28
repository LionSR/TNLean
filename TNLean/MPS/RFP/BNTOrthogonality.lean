/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.Core.MultiBlock
import TNLean.Spectral.TransferOperatorGapNT

/-!
# Cross-block orthogonality of the renormalization fixed-point isometry

This file proves the cross-block (`j ≠ j'`) vanishing of the mixed transfer
operator for a multi-block tensor whose direct sum is a renormalization fixed
point, the off-diagonal content of the isometry condition `eq:III_isometry`
(arXiv:1606.00608, line 551):
\[
  \sum_i (U_j^i)_{\alpha,\beta}\,\overline{(U_{j'}^i)_{\alpha',\beta'}}
    = \delta_{j,j'}\delta_{\alpha,\alpha'}\delta_{\beta,\beta'} .
\]
The diagonal `j = j'` case is `IsIsometryCanonicalForm`
(`TNLean/MPS/RFP/StructuralFull.lean`).

## Main results

* `blockDiagonal'_transferSum_toBlock` — block decomposition of the direct-sum
  transfer sum: its `(j, j')` bond block acts as
  `mixedTransferMap₂ (B j) (B j')`.  This is the reusable foundation, parallel
  to `evalWord_blockDiagonal'`.

## Route

The off-diagonal mixed transfer operator `F_{j,j'} = mixedTransferMap₂ (B j)
(B j')` is shown to be idempotent (whole-tensor RFP, via the block
decomposition), and then to have spectral radius `< 1` (distinct irreducible
left-canonical blocks, splitting on equal versus unequal bond dimension); an
idempotent operator with spectral radius `< 1` is `0`.  The diagonal lemma
`transferMap_eq_fixedPointProj_of_isRFP_injective` does *not* compose across
blocks and is not used here.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ## Block decomposition of a block-diagonal transfer sum -/

section BlockDecomposition

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The canonical inclusion of the `k`-th bond block into the direct-sum bond
space, `α ↦ ⟨k, α⟩`. -/
def blockIncl (k : Fin r) (dim : Fin r → ℕ) :
    Fin (dim k) → (k : Fin r) × Fin (dim k) :=
  fun a => ⟨k, a⟩

/-- Submatrices commute with finite sums. -/
private lemma submatrix_sum' {ι l m p q : Type*}
    (s : Finset ι) (M : ι → Matrix m p ℂ) (f : l → m) (g : q → p) :
    (∑ i ∈ s, M i).submatrix f g = ∑ i ∈ s, (M i).submatrix f g := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

/-- The `(j, j')` bond block of `(⊕_k L_k) X (⊕_k R_k)` is `L_j · X_{j,j'} · R_{j'}`. -/
private lemma blockDiagonal'_mul_mul_toBlock
    (L R : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (X : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ)
    (j j' : Fin r) :
    (Matrix.blockDiagonal' L * X * Matrix.blockDiagonal' R).submatrix
        (blockIncl j dim) (blockIncl j' dim) =
      L j * X.submatrix (blockIncl j dim) (blockIncl j' dim) * R j' := by
  classical
  ext a a'
  rw [Matrix.submatrix_apply]
  change (Matrix.blockDiagonal' L * X * Matrix.blockDiagonal' R) (⟨j, a⟩ :
      (k : Fin r) × Fin (dim k)) ⟨j', a'⟩ = _
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  -- reduce the outer (right block-diagonal) index to `j'`
  rw [Finset.sum_eq_single j'
    (fun k' _ hk' => Finset.sum_eq_zero fun b' _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk', mul_zero])
    (fun h => absurd (Finset.mem_univ j') h)]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Matrix.blockDiagonal'_apply_eq]
  congr 1
  -- now reduce the inner (left block-diagonal) index to `j`
  rw [Matrix.mul_apply, Fintype.sum_sigma, Matrix.mul_apply]
  rw [Finset.sum_eq_single j
    (fun k _ hk => Finset.sum_eq_zero fun b _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hk), zero_mul])
    (fun h => absurd (Finset.mem_univ j) h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.blockDiagonal'_apply_eq, Matrix.submatrix_apply, blockIncl, blockIncl]

/-- The `(j, j')` bond block of the block-diagonal
transfer sum `∑_i (⊕_k B_k^i) X (⊕_k B_k^i)^†` is the mixed transfer operator
`mixedTransferMap₂ (B j) (B j')` applied to the `(j, j')` bond block of `X`.

This is the transfer-operator analogue of `evalWord_blockDiagonal'`, and the
reusable foundation for the cross-block content of `eq:III_isometry`
(arXiv:1606.00608, line 551). -/
theorem blockDiagonal'_transferSum_toBlock
    (B : (k : Fin r) → MPSTensor d (dim k))
    (X : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ)
    (j j' : Fin r) :
    (∑ i : Fin d, Matrix.blockDiagonal' (fun k => B k i) * X *
        (Matrix.blockDiagonal' (fun k => B k i))ᴴ).submatrix
        (blockIncl j dim) (blockIncl j' dim) =
      mixedTransferMap₂ (B j) (B j')
        (X.submatrix (blockIncl j dim) (blockIncl j' dim)) := by
  classical
  rw [mixedTransferMap₂_apply, submatrix_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.blockDiagonal'_conjTranspose, blockDiagonal'_mul_mul_toBlock]

/-- The block-diagonal transfer sum `∑_i (⊕_k B_k^i) Y (⊕_k B_k^i)^†` on the
direct-sum bond space (`Σ`-indexed). -/
noncomputable def blockTransferSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ :=
  ∑ i : Fin d, Matrix.blockDiagonal' (fun k => B k i) * Y *
    (Matrix.blockDiagonal' (fun k => B k i))ᴴ

/-- The direct sum of a finite family of MPS tensors, as a single tensor on the
total bond space `Fin (∑ k, dim k)`.

This coincides with `CanonicalForm.toTensor` of the canonical form with block
tensors `B`, all scalar weights `μ_k = 1`, mirroring its `blockDiagonal'`/`Σ`-reindex
construction (`TNLean/MPS/Core/MultiBlock.lean`). -/
noncomputable def directSumTensor (B : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) := fun i =>
  Matrix.reindex (finSigmaFinEquiv (n := dim)) (finSigmaFinEquiv (n := dim))
    (Matrix.blockDiagonal' (fun k => B k i))

/-- The transfer map of the direct-sum tensor equals the block-diagonal transfer
sum conjugated by the `Σ ≃ Fin` reindexing. -/
theorem transferMap_directSumTensor_reindex
    (B : (k : Fin r) → MPSTensor d (dim k))
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    transferMap (directSumTensor B)
        (Matrix.reindex (finSigmaFinEquiv (n := dim)) (finSigmaFinEquiv (n := dim)) Y) =
      Matrix.reindex (finSigmaFinEquiv (n := dim)) (finSigmaFinEquiv (n := dim))
        (blockTransferSum B Y) := by
  classical
  set e := finSigmaFinEquiv (m := r) (n := dim) with he
  rw [transferMap_apply, blockTransferSum]
  simp only [Matrix.reindex_apply]
  rw [submatrix_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [directSumTensor, Matrix.reindex_apply]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ _ e.symm _,
    Matrix.submatrix_mul_equiv _ _ _ e.symm _]

/-- Whole-tensor RFP of the direct sum makes
the block-diagonal transfer sum idempotent. -/
theorem blockTransferSum_blockTransferSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hRFP : IsRFP (directSumTensor B))
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    blockTransferSum B (blockTransferSum B Y) = blockTransferSum B Y := by
  classical
  set e := finSigmaFinEquiv (m := r) (n := dim) with he
  apply (Matrix.reindex e e).injective
  calc
    Matrix.reindex e e (blockTransferSum B (blockTransferSum B Y))
        = transferMap (directSumTensor B) (Matrix.reindex e e (blockTransferSum B Y)) :=
          (transferMap_directSumTensor_reindex B (blockTransferSum B Y)).symm
    _ = transferMap (directSumTensor B)
          (transferMap (directSumTensor B) (Matrix.reindex e e Y)) := by
            rw [transferMap_directSumTensor_reindex B Y]
    _ = transferMap (directSumTensor B) (Matrix.reindex e e Y) := by
          have h := LinearMap.congr_fun hRFP (Matrix.reindex e e Y)
          simpa only [LinearMap.comp_apply] using h
    _ = Matrix.reindex e e (blockTransferSum B Y) :=
          transferMap_directSumTensor_reindex B Y

/-- The `(j, j')` bond-block restriction is surjective: every block matrix is the
restriction of a direct-sum bond matrix. -/
private lemma exists_toBlock_eq (j j' : Fin r) [NeZero (dim j)] [NeZero (dim j')]
    (Z : Matrix (Fin (dim j)) (Fin (dim j')) ℂ) :
    ∃ Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ,
      Y.submatrix (blockIncl j dim) (blockIncl j' dim) = Z := by
  classical
  have hinj_j : Function.Injective (blockIncl j dim) := by
    intro a b h; simpa [blockIncl] using h
  have hinj_j' : Function.Injective (blockIncl j' dim) := by
    intro a b h; simpa [blockIncl] using h
  refine ⟨Z.submatrix (Function.invFun (blockIncl j dim))
      (Function.invFun (blockIncl j' dim)), ?_⟩
  have hj : Function.invFun (blockIncl j dim) ∘ blockIncl j dim = id :=
    funext (Function.leftInverse_invFun hinj_j)
  have hj' : Function.invFun (blockIncl j' dim) ∘ blockIncl j' dim = id :=
    funext (Function.leftInverse_invFun hinj_j')
  rw [Matrix.submatrix_submatrix, hj, hj', Matrix.submatrix_id_id]

/-- Whole-tensor RFP of the direct sum
makes every (in particular off-diagonal) mixed transfer operator idempotent. -/
theorem mixedTransferMap₂_isIdempotentElem_of_isRFP_directSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hRFP : IsRFP (directSumTensor B)) (j j' : Fin r)
    [NeZero (dim j)] [NeZero (dim j')] :
    IsIdempotentElem (mixedTransferMap₂ (B j) (B j')) := by
  classical
  have hStage1 : ∀ Y, (blockTransferSum B Y).submatrix (blockIncl j dim) (blockIncl j' dim) =
      mixedTransferMap₂ (B j) (B j') (Y.submatrix (blockIncl j dim) (blockIncl j' dim)) := by
    intro Y
    simpa only [blockTransferSum] using blockDiagonal'_transferSum_toBlock B Y j j'
  change mixedTransferMap₂ (B j) (B j') * mixedTransferMap₂ (B j) (B j') =
    mixedTransferMap₂ (B j) (B j')
  refine LinearMap.ext fun Z => ?_
  rw [Module.End.mul_apply]
  obtain ⟨Y, hY⟩ := exists_toBlock_eq j j' Z
  have e1 : mixedTransferMap₂ (B j) (B j') Z =
      (blockTransferSum B Y).submatrix (blockIncl j dim) (blockIncl j' dim) := by
    rw [hStage1, hY]
  calc
    mixedTransferMap₂ (B j) (B j') (mixedTransferMap₂ (B j) (B j') Z)
        = mixedTransferMap₂ (B j) (B j')
            ((blockTransferSum B Y).submatrix (blockIncl j dim) (blockIncl j' dim)) := by rw [e1]
    _ = (blockTransferSum B (blockTransferSum B Y)).submatrix
          (blockIncl j dim) (blockIncl j' dim) := (hStage1 (blockTransferSum B Y)).symm
    _ = (blockTransferSum B Y).submatrix (blockIncl j dim) (blockIncl j' dim) := by
          rw [blockTransferSum_blockTransferSum B hRFP]
    _ = mixedTransferMap₂ (B j) (B j') Z := e1.symm

end BlockDecomposition

/-! ## Spectral gap forces the off-diagonal operator to vanish -/

section Spectral

variable {D₁ D₂ : ℕ}

attribute [local instance]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toSeminormedRing
  ContinuousLinearMap.toNormedAlgebra

local notation "V" => Matrix (Fin D₁) (Fin D₂) ℂ

/-- An idempotent rectangular mixed transfer operator with spectral radius `< 1`
is the zero map. -/
private lemma mixedTransferMap₂_eq_zero_of_isIdempotentElem
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hidem : IsIdempotentElem (mixedTransferMap₂ A B))
    (hsr : mixedTransferSpectralRadius₂ A B < 1) :
    mixedTransferMap₂ A B = 0 := by
  classical
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap₂ A B)
  letI : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : SeminormedRing (V →L[ℂ] V) := ContinuousLinearMap.toSeminormedRing
  letI : NormedRing (V →L[ℂ] V) := ContinuousLinearMap.toNormedRing
  letI : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  letI : NormedAlgebra ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedAlgebra
  haveI : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  haveI hComplete : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.complete ℂ _
  have hSpectF : spectralRadius ℂ F' < 1 := by
    change spectralRadius ℂ
      (((Module.End.toContinuousLinearMap V)
        (mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B)) : V →L[ℂ] V) < 1
    rw [mixedTransferSpectralRadius₂_eq] at hsr
    simpa only [] using hsr
  have hpow : Tendsto (fun n => F' ^ n) atTop (nhds 0) :=
    @pow_tendsto_zero_of_spectralRadius_lt_one (V →L[ℂ] V)
      (ContinuousLinearMap.toNormedRing : NormedRing (V →L[ℂ] V)) hComplete
      (ContinuousLinearMap.toNormedAlgebra : NormedAlgebra ℂ (V →L[ℂ] V)) F' hSpectF
  have hFpow : ∀ n, F' ^ (n + 1) = F' := by
    intro n
    change (Φ (mixedTransferMap₂ A B)) ^ (n + 1) = Φ (mixedTransferMap₂ A B)
    rw [← map_pow, hidem.pow_succ_eq n]
  have hshift : Tendsto (fun n => F' ^ (n + 1)) atTop (nhds 0) :=
    hpow.comp (tendsto_add_atTop_nat 1)
  have hconst : Tendsto (fun n => F' ^ (n + 1)) atTop (nhds F') := by
    simp only [hFpow]; exact tendsto_const_nhds
  have hF'0 : F' = 0 := tendsto_nhds_unique hconst hshift
  have hF0 : Φ (mixedTransferMap₂ A B) = Φ 0 := by rw [map_zero]; exact hF'0
  exact Φ.injective hF0

/-- **Same-dimension spectral gap (cast form).** For distinct irreducible
left-canonical blocks of equal bond dimension that are not gauge-phase
equivalent, the rectangular mixed transfer spectral radius is `< 1`. -/
private lemma mixedTransferSpectralRadius₂_lt_one_of_dim_eq
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ = D₂)
    (hgpe : ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) hD) A) B) :
    mixedTransferSpectralRadius₂ A B < 1 := by
  subst hD
  simp only [cast_eq] at hgpe
  have hagree : mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₁) A B =
      mixedTransferMap A B := by
    ext X; simp
  rw [mixedTransferSpectralRadius₂_eq, hagree, ← mixedTransferSpectralRadius_eq]
  exact spectralRadius_mixedTransfer_lt_one_of_irreducible_TP A B hA_irr hB_irr
    hA_left hB_left hgpe

end Spectral

/-! ## Cross-block orthogonality of the blocks -/

section Main

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **Cross-block orthogonality of the RFP isometry (mixed-transfer form).**

For a family of distinct irreducible left-canonical blocks `B`, if the
whole direct-sum tensor `⊕_k B_k` is a renormalization fixed point, then every
off-diagonal mixed transfer operator vanishes:
`mixedTransferMap₂ (B j) (B j') = 0` for `j ≠ j'`.

This is the `δ_{j,j'}` (cross-block) content of the isometry condition
`eq:III_isometry` (arXiv:1606.00608, line 551), towards Corollary III.cor3
(line 584).

The load-bearing hypothesis is whole-tensor RFP of the direct sum (the source's
"`A` in CF is RFP"), strictly stronger than per-block RFP.  The diagonal
`j = j'` case is `IsIsometryCanonicalForm`. -/
theorem isBNTLocallyOrthogonal_of_isRFP_directSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    [∀ k, NeZero (dim k)]
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k))
    (hRFP : IsRFP (directSumTensor B)) :
    IsBNTLocallyOrthogonal B := by
  intro j j' hjj'
  have hidem := mixedTransferMap₂_isIdempotentElem_of_isRFP_directSum B hRFP j j'
  have hsr : mixedTransferSpectralRadius₂ (B j) (B j') < 1 := by
    by_cases hdim : dim j = dim j'
    · exact mixedTransferSpectralRadius₂_lt_one_of_dim_eq (B j) (B j')
        (hirr j) (hirr j') (hleft j) (hleft j') hdim (hdist j j' hjj' hdim)
    · exact mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP (B j) (B j')
        (hirr j) (hirr j') (hleft j) (hleft j') hdim
  exact mixedTransferMap₂_eq_zero_of_isIdempotentElem (B j) (B j') hidem hsr

end Main

end MPSTensor
