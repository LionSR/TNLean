/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.Core.MultiBlock
import TNLean.Spectral.TransferOperatorGapNT

/-!
# Cross-block orthogonality of the renormalization fixed-point isometry

This file proves the cross-block (`j ≠ j'`) vanishing of the mixed transfer
operator for a multi-block tensor whose direct sum is a renormalization fixed
point, the off-diagonal content of the isometry condition
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
* `isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem`
  — exact reduction of whole-tensor transfer idempotence to every mixed block
  pair.

## Route

The off-diagonal mixed transfer operator $\mathcal E_{j,j'}$ is shown to be
idempotent (whole-tensor RFP, via the block
decomposition), and then to have spectral radius `< 1` (distinct irreducible
left-canonical blocks, splitting on equal versus unequal bond dimension); an
idempotent operator with spectral radius `< 1` is `0`.  The diagonal lemma
`transferMap_eq_fixedPointProj_of_isTransferIdempotent_injective` does *not* compose across
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

/-- Left block-diagonal action on a bond block: the `(j, j')` bond block of
$(\bigoplus_k L_k)\, X$ is $L_j X_{j,j'}$ (arXiv:1606.00608, line 551). -/
private lemma blockDiagonal'_mul_toBlock
    (L : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (X : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ)
    (j j' : Fin r) :
    (Matrix.blockDiagonal' L * X).submatrix (blockIncl j dim) (blockIncl j' dim) =
      L j * X.submatrix (blockIncl j dim) (blockIncl j' dim) := by
  classical
  ext a a'
  rw [Matrix.submatrix_apply]
  change (Matrix.blockDiagonal' L * X) (⟨j, a⟩ :
      (k : Fin r) × Fin (dim k)) ⟨j', a'⟩ = _
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  -- kill the off-diagonal blocks of the left factor
  rw [Finset.sum_eq_single j
    (fun k _ hk => Finset.sum_eq_zero fun b _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hk), zero_mul])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.blockDiagonal'_apply_eq, Matrix.submatrix_apply, blockIncl, blockIncl]

/-- Right block-diagonal action on a bond block: the `(j, j')` bond block of
$X\, (\bigoplus_k R_k)$ is $X_{j,j'} R_{j'}$ (arXiv:1606.00608, line 551). -/
private lemma mul_blockDiagonal'_toBlock
    (R : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (X : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ)
    (j j' : Fin r) :
    (X * Matrix.blockDiagonal' R).submatrix (blockIncl j dim) (blockIncl j' dim) =
      X.submatrix (blockIncl j dim) (blockIncl j' dim) * R j' := by
  classical
  ext a a'
  rw [Matrix.submatrix_apply]
  change (X * Matrix.blockDiagonal' R) (⟨j, a⟩ :
      (k : Fin r) × Fin (dim k)) ⟨j', a'⟩ = _
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  -- kill the off-diagonal blocks of the right factor
  rw [Finset.sum_eq_single j'
    (fun k' _ hk' => Finset.sum_eq_zero fun b' _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk', mul_zero])
    (fun h => absurd (Finset.mem_univ j') h)]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Matrix.blockDiagonal'_apply_eq, Matrix.submatrix_apply, blockIncl, blockIncl]

/-- The `(j, j')` bond block of $(\bigoplus_k L_k)\, X\, (\bigoplus_k R_k)$ is
$L_j X_{j,j'} R_{j'}$. -/
private lemma blockDiagonal'_mul_mul_toBlock
    (L R : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (X : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ)
    (j j' : Fin r) :
    (Matrix.blockDiagonal' L * X * Matrix.blockDiagonal' R).submatrix
        (blockIncl j dim) (blockIncl j' dim) =
      L j * X.submatrix (blockIncl j dim) (blockIncl j' dim) * R j' := by
  rw [mul_blockDiagonal'_toBlock, blockDiagonal'_mul_toBlock]

/-- The `(j, j')` bond block of the block-diagonal transfer sum
$\sum_i (\bigoplus_k B_k^i)\, X\, (\bigoplus_k B_k^i)^{\dagger}$ is the mixed
transfer operator `mixedTransferMap₂ (B j) (B j')` applied to the `(j, j')`
bond block of `X`.

This is the transfer-operator analogue of `evalWord_blockDiagonal'`, and the
reusable foundation for the cross-block content of the isometry condition
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

/-- The block-diagonal transfer sum
$\sum_i (\bigoplus_k B_k^i)\, Y\, (\bigoplus_k B_k^i)^{\dagger}$ on the
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
tensors `B`, all scalar weights $\mu_k = 1$, mirroring its `blockDiagonal'`/`Σ`-reindex
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
    (hRFP : IsTransferIdempotent (directSumTensor B))
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
theorem mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) (j j' : Fin r)
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

/-- If every mixed transfer operator of a block family is idempotent, then the
block-diagonal transfer sum is idempotent.

The transfer sum acts independently on each $(j,j')$ bond block through
`mixedTransferMap₂ (B j) (B j')`. Thus its idempotence is checked one block pair
at a time. This is the exact direct-sum algebra needed when interpreting the
repeated-block display in arXiv:1606.00608, Theorem charact-MPS, lines 543--555. -/
theorem blockTransferSum_idempotent_of_pairwise_mixedTransferMap₂
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hidem : ∀ j j', IsIdempotentElem (mixedTransferMap₂ (B j) (B j')))
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    blockTransferSum B (blockTransferSum B Y) = blockTransferSum B Y := by
  classical
  have hStage1 : ∀ (W : Matrix ((k : Fin r) × Fin (dim k))
        ((k : Fin r) × Fin (dim k)) ℂ) (j j' : Fin r),
      (blockTransferSum B W).submatrix (blockIncl j dim) (blockIncl j' dim) =
        mixedTransferMap₂ (B j) (B j')
          (W.submatrix (blockIncl j dim) (blockIncl j' dim)) := by
    intro W j j'
    simpa only [blockTransferSum] using blockDiagonal'_transferSum_toBlock B W j j'
  have blockEq : ∀ j j' : Fin r,
      (blockTransferSum B (blockTransferSum B Y)).submatrix
          (blockIncl j dim) (blockIncl j' dim) =
        (blockTransferSum B Y).submatrix (blockIncl j dim) (blockIncl j' dim) := by
    intro j j'
    rw [hStage1 (blockTransferSum B Y) j j', hStage1 Y j j']
    simpa only [Module.End.mul_apply] using
      LinearMap.congr_fun (hidem j j')
        (Y.submatrix (blockIncl j dim) (blockIncl j' dim))
  ext jx jy
  obtain ⟨j, a⟩ := jx
  obtain ⟨j', a'⟩ := jy
  simpa only [Matrix.submatrix_apply, blockIncl] using
    congrFun (congrFun (blockEq j j') a) a'

/-- Transfer idempotence of a direct-sum tensor is equivalent to idempotence of
every mixed transfer operator between its blocks.

This statement includes both diagonal and off-diagonal block pairs. In
particular, repeated virtual copies cannot be checked only one block at a time:
their mixed transfer operators also enter the whole-tensor idempotence equation.
See arXiv:1606.00608, Theorem charact-MPS, lines 543--555. -/
theorem isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem
    [∀ k, NeZero (dim k)] (B : (k : Fin r) → MPSTensor d (dim k)) :
    IsTransferIdempotent (directSumTensor B) ↔
      ∀ j j', IsIdempotentElem (mixedTransferMap₂ (B j) (B j')) := by
  constructor
  · intro hRFP j j'
    exact mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum
      B hRFP j j'
  · intro hidem
    classical
    set e := finSigmaFinEquiv (m := r) (n := dim)
    change transferMap (directSumTensor B) ∘ₗ transferMap (directSumTensor B) =
      transferMap (directSumTensor B)
    refine LinearMap.ext fun Z => ?_
    rw [LinearMap.comp_apply]
    obtain ⟨Y, rfl⟩ : ∃ Y, Matrix.reindex e e Y = Z :=
      ⟨(Matrix.reindex e e).symm Z, (Matrix.reindex e e).apply_symm_apply Z⟩
    calc
      transferMap (directSumTensor B)
            (transferMap (directSumTensor B) (Matrix.reindex e e Y)) =
          transferMap (directSumTensor B)
            (Matrix.reindex e e (blockTransferSum B Y)) := by
              rw [transferMap_directSumTensor_reindex B Y]
      _ = Matrix.reindex e e (blockTransferSum B (blockTransferSum B Y)) :=
            transferMap_directSumTensor_reindex B (blockTransferSum B Y)
      _ = Matrix.reindex e e (blockTransferSum B Y) := by
            rw [blockTransferSum_idempotent_of_pairwise_mixedTransferMap₂ B hidem Y]
      _ = transferMap (directSumTensor B) (Matrix.reindex e e Y) :=
            (transferMap_directSumTensor_reindex B Y).symm

/-- A nonzero idempotent linear map cannot remain idempotent after multiplication
by a nonzero scalar other than one. -/
private lemma scalar_eq_one_of_smul_idempotent
    {D₁ D₂ : ℕ}
    (F : Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ]
      Matrix (Fin D₁) (Fin D₂) ℂ)
    (hF : IsIdempotentElem F) (hF_ne : F ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (hcF : IsIdempotentElem (c • F)) : c = 1 := by
  change F * F = F at hF
  change (c • F) * (c • F) = c • F at hcF
  have hcF' : (c * c) • F = c • F := by
    calc
      (c * c) • F = (c • F) * (c • F) := by rw [smul_mul_smul, hF]
      _ = c • F := hcF
  have hzero : (c * c - c) • F = 0 := by
    calc
      (c * c - c) • F = (c * c) • F - c • F := sub_smul (c * c) c F
      _ = c • F - c • F := by rw [hcF']
      _ = 0 := sub_self (c • F)
  have hscalar : c * c - c = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hF_ne
  have hmul : c * c = c * 1 := by
    simpa only [mul_one] using sub_eq_zero.mp hscalar
  exact mul_left_cancel₀ hc hmul

/-- If a nonzero transfer-idempotent tensor is repeated with unit-modulus scalar
coefficients and the literal bond direct sum is transfer-idempotent, then all
coefficients are equal.

**Local fix (see `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`):** This is the
corrected literal-block consequence of CPSV16, Theorem charact-MPS, lines
543--563. The printed independent-phase statement does not specify the additional
physical-space construction needed to avoid these mixed copy equations. -/
theorem phases_eq_of_isTransferIdempotent_directSum_scaled_self
    {D : ℕ} [NeZero D] (A : MPSTensor d D) (hA : IsTransferIdempotent A)
    (hA_ne : transferMap A ≠ 0) (μ : Fin r → ℂ) (hμ : ∀ q, ‖μ q‖ = 1)
    (hRFP : IsTransferIdempotent
      (directSumTensor (fun q : Fin r ↦ (fun i ↦ μ q • A i : MPSTensor d D))))
    (q q' : Fin r) : μ q = μ q' := by
  have hμ_ne : ∀ q, μ q ≠ 0 := by
    intro q hq
    simpa [hq] using hμ q
  have hphase : μ q * starRingEnd ℂ (μ q') = 1 := by
    have hidem :=
      (isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem
        (B := fun s : Fin r ↦ (fun i ↦ μ s • A i : MPSTensor d D))).mp hRFP q q'
    rw [mixedTransferMap₂_smul, mixedTransferMap₂_self] at hidem
    apply scalar_eq_one_of_smul_idempotent (transferMap A) hA hA_ne
      (μ q * starRingEnd ℂ (μ q'))
      (mul_ne_zero (hμ_ne q) ((map_ne_zero (starRingEnd ℂ)).2 (hμ_ne q'))) hidem
  have hnormSq : Complex.normSq (μ q') = 1 := by
    rw [Complex.normSq_eq_norm_sq, hμ q']
    norm_num
  calc
    μ q = μ q * 1 := (mul_one (μ q)).symm
    _ = μ q * (starRingEnd ℂ (μ q') * μ q') := by
      rw [← Complex.normSq_eq_conj_mul_self, hnormSq]
      norm_num
    _ = (μ q * starRingEnd ℂ (μ q')) * μ q' :=
      (mul_assoc (μ q) (starRingEnd ℂ (μ q')) (μ q')).symm
    _ = 1 * μ q' := by rw [hphase]
    _ = μ q' := one_mul (μ q')

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
    exact hsr
  have hidem' : IsIdempotentElem F' := hidem.map Φ
  have hF'0 : F' = 0 :=
    @IsIdempotentElem.eq_zero_of_spectralRadius_lt_one (V →L[ℂ] V)
      (ContinuousLinearMap.toNormedRing : NormedRing (V →L[ℂ] V)) hComplete
      (ContinuousLinearMap.toNormedAlgebra : NormedAlgebra ℂ (V →L[ℂ] V)) F' hidem' hSpectF
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
  rw [mixedTransferSpectralRadius₂_eq, mixedTransferMap₂_same_dim,
    ← mixedTransferSpectralRadius_eq]
  exact spectralRadius_mixedTransfer_lt_one_of_irreducible_TP A B hA_irr hB_irr
    hA_left hB_left hgpe

end Spectral

/-! ## Cross-block orthogonality of the blocks -/

section Main

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **Cross-block orthogonality of the RFP isometry (mixed-transfer form).**

For a family of distinct irreducible left-canonical blocks `B`, if the
whole direct-sum tensor $\bigoplus_k B_k$ is a renormalization fixed point,
then every
off-diagonal mixed transfer operator vanishes:
`mixedTransferMap₂ (B j) (B j') = 0` for `j ≠ j'`.

This is the $\delta_{j,j'}$ (cross-block) content of the isometry condition
at arXiv:1606.00608, line 551, used toward the local-orthogonality conclusion
at line 584.

The load-bearing hypothesis is whole-tensor RFP of the direct sum (the source's
"`A` in CF is RFP"), strictly stronger than per-block RFP.  The diagonal
`j = j'` case is `IsIsometryCanonicalForm`. -/
theorem isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    [∀ k, NeZero (dim k)]
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) :
    IsBNTLocallyOrthogonal B := by
  intro j j' hjj'
  have hidem := mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum B hRFP j j'
  have hsr : mixedTransferSpectralRadius₂ (B j) (B j') < 1 := by
    by_cases hdim : dim j = dim j'
    · exact mixedTransferSpectralRadius₂_lt_one_of_dim_eq (B j) (B j')
        (hirr j) (hirr j') (hleft j) (hleft j') hdim (hdist j j' hjj' hdim)
    · exact mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP (B j) (B j')
        (hirr j) (hirr j') (hleft j) (hleft j') hdim
  exact mixedTransferMap₂_eq_zero_of_isIdempotentElem (B j) (B j') hidem hsr

/-- **Canonical direct-sum RFP tensors have positive-gap BNT zero correlation
length.**

Let `B` be a basis of normal tensors consisting of nonzero-dimensional,
irreducible, left-canonical, pairwise gauge-phase-distinct blocks.  If its
direct-sum tensor has idempotent transfer map, then it has positive-gap
physical CID and, for all distinct BNT components $j \ne j'$,
\[
  \mathcal E_{j,j'}=0.
\]

This is the positive-gap part of the forward implication at
arXiv:1606.00608, lines 498--502 and 1248--1250, for the explicit unweighted
direct-sum representative. The physical CID part follows from
$\mathcal E_A^n=\mathcal E_A$ for $n\geq 1$ in the two-observable transfer
formula at lines 490--496; the local-orthogonality part is
`isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum`.

**Scope restriction (positive gaps and explicit direct sum):** the source CID
definition includes adjacent regions, whereas the predicate below assumes both
complementary gaps are positive.  The source also allows scalar multiplicities
and a possible bond gauge.  Both restrictions are recorded in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isPositiveGapBNTZCL_of_isTransferIdempotent_directSum
    (B : (k : Fin r) → MPSTensor d (dim k))
    [∀ k, NeZero (dim k)]
    (hBNT : IsCPSVBasisOfNormalTensors (directSumTensor B)
      (fun k => ⟨dim k, B k⟩))
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) :
    IsPositiveGapBNTZCL (directSumTensor B) B := by
  refine ⟨hBNT, isPositiveGapPhysicalCID_of_isTransferIdempotent (directSumTensor B) hRFP, ?_⟩
  exact isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum B hirr hleft hdist hRFP

end Main

end MPSTensor
