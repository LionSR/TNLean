/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Channel.KrausMap.KrausSupportAbsorption
import QICLean.Kraus.Word
import TNLean.MPS.Operator.Periodic.OperatorFromWordTrace
import TNLean.MPS.Operator.PairAlphabet
import TNLean.MPS.MPU.Index.FactorFreeSandwich
import TNLean.MPS.MPU.Index.IndexContinuity
import TNLean.MPS.MPU.Index.IndexOfCanonicalForm
import TNLean.MPS.MPU.Index.ReducedToHatTransport
import TNLean.MPS.MPU.Simple.RectangularSourceRanks
import TNLean.MPS.MPU.CanonicalForm.ReducedRepresentative
import TNLean.MPS.MPU.CanonicalForm.TransferStabilizationConverse
import QICLean.Kraus.Transfer

/-!
# Constancy of the MPU index along arbitrary continuous paths

This file proves Proposition IV.5 of Cirac--Pérez-García--Schuch--Verstraete
without assuming that the path is in canonical form. Let `x ↦ W(x)` be a
continuous path of tensors generating matrix product unitaries.

1. After blocking `k ≥ D²` sites, the normalized transfer matrix of `W(x)_k` is
   a rank-one projector `|ρ)(Φ|`. The transfer map is therefore
   `X ↦ tr(L X) R`, with the explicit positive semidefinite factors
   `R = ∑ₐ Aₐ Aₐ†` and `L = tr(R)⁻¹ ∑ₐ Aₐ† Aₐ`. Every letter is absorbed by the
   support projections: `Aₐ P = Aₐ = Q Aₐ`.
2. Let `T` be the reduced projection of `P` and `Q`. The reduced tensor
   `T W T`, restricted to the range of `T` and gauged by a congruence that
   brings the compressed pair `(T L T, T R T)` to `(1, Λ)` with `Λ` diagonal, is in
   canonical form II and generates the same MPU. Its source ranks are those of
   `L W R`.
3. By the fundamental theorem, every canonical-form-II tensor generating the
   same MPU has these ranks after blocking. The tensor `L W R` is the
   factor-free contraction of `W` with its own normalized transfer matrix, which
   is continuous in `W` with no choice of `L` and `R`.
4. Rank is lower semicontinuous and the product of the two ranks is the fixed
   number `d^{2k}`, so both ranks, and the index, are constant on `[0,1]`.

## Main results

* `MPOTensor.IsMPU.sourceRanks_canonicalFormII_blockTensor_const` and
  `MPOTensor.IsMPU.sourceRanks_canonicalFormII_blockTensor_pow_four_const`:
  the source ranks of the canonical-form-II representatives along the path,
  blocked at any length `k ≥ D²` or at `D⁴`, are constant.
* `MPOTensor.IsMPU.sourceRanks_canonicalForm_blockTensor_const`: the same for
  representatives in canonical form.
* `MPOTensor.IsMPU.index_const_of_continuous`: the index is constant along the
  path.
* `MPOTensor.IsMPU.sourceRanks_blockTensor_eq_factorFreeSandwich`: the
  pointwise identification of the canonical source ranks with the ranks of
  `L W R`.

## References

Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188,
Proposition `prop:continuity-index`, lines 733--818.
-/

open scoped Matrix ComplexOrder BigOperators MatrixOrder

namespace MPOTensor

variable {n d D : ℕ}

/-- A rectangular compression `Lf Mᵢⱼ Rt` has the periodic operators of `M` at
every positive length when every letter absorbs the corner `Rt Lf` on the
right.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--783 (restriction of the
reduced tensor to the range of the reduced projection). -/
theorem mpo_rectangularSandwich_of_absorb {m : ℕ}
    (M : MPOTensor n D) (Lf : Matrix (Fin m) (Fin D) ℂ) (Rt : Matrix (Fin D) (Fin m) ℂ)
    (hright : ∀ i j, M (i, j) * (Rt * Lf) = M (i, j)) {N : ℕ} (hN : 0 < N) :
    mpo (fun ij => Lf * M ij * Rt) N = mpo M N := by
  exact mpo_eq_of_forall_trace_evalWord (fun w hw ↦
    Kraus.trace_evalWord_compress_of_right_absorb M Lf Rt (fun ij => hright ij.1 ij.2) w hw) hN

/-- **Canonical form II of a tensor with a rank-one transfer map.** Let `V`
generate MPU and let its normalized transfer map be `X ↦ tr(L X) R` with
positive semidefinite `L`, `R`. Restricting the reduced tensor
`T V T` to the range of the reduced projection `T` of the supports of `L` and
`R`, and gauging by `(T L T)^{1/2}` followed by a unitary, gives a tensor in
canonical form II with the same periodic operators at every positive length.
Both of its source ranks are those of the sandwich `L V R`.

Source: arXiv:1703.09188, Proposition IV.5, lines 756--804. -/
theorem exists_isMPUCanonicalFormII_of_transferMap_eq_trace_smul [NeZero n]
    {V : MPOTensor n D} (hV : IsMPU V) {L R : Matrix (Fin D) (Fin D) ℂ}
    (hL : L.PosSemidef) (hR : R.PosSemidef)
    (hT : ∀ X, Kraus.transferMap V.normalizedFlattening X = Matrix.trace (L * X) • R) :
    ∃ (m : ℕ) (B : MPOTensor n m), Nonempty (IsMPUCanonicalFormII B) ∧
      (∀ N, 0 < N → mpo B N = mpo V N) ∧
      r[B] = r[virtualSandwich L V R] ∧ ℓ[B] = ℓ[virtualSandwich L V R] := by
  classical
  set P := hL.supportProj with hPdef
  set Q := hR.supportProj with hQdef
  have hP : IsOrthogonalProjection P := hL.isOrthogonalProjection_supportProj
  have hc : ((Real.sqrt n : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)).ne')
  have hflat : ∀ i j, V.normalizedFlattening (i, j) = ((Real.sqrt n : ℂ)⁻¹) • V (i, j) :=
    fun _ _ ↦ rfl
  -- The support-absorption lemmas are stated on a `Fin` alphabet: relabel along
  -- `finProdFinEquiv`.
  have hT' : ∀ X,
      Kraus.map (Kraus.reindexPhysical finProdFinEquiv.symm V.normalizedFlattening) X =
        Matrix.trace (L * X) • R := fun X ↦
    (congrArg (fun f ↦ f X) (Kraus.transferMap_reindexPhysical_equiv finProdFinEquiv.symm
      V.normalizedFlattening)).trans (hT X)
  have hVP : ∀ i j, V (i, j) * P = V (i, j) := by
    intro i j
    have h := Kraus.mul_supportProj_of_map_eq_trace_smul _ hL hT' (finProdFinEquiv (i, j))
    simp only [Kraus.reindexPhysical, Equiv.symm_apply_apply] at h
    rw [hflat, Matrix.smul_mul] at h
    exact smul_right_injective _ hc h
  have hQV : ∀ i j, Q * V (i, j) = V (i, j) := by
    intro i j
    have h := Kraus.supportProj_mul_of_map_eq_trace_smul _ hR hT' (finProdFinEquiv (i, j))
    simp only [Kraus.reindexPhysical, Equiv.symm_apply_apply] at h
    rw [hflat, Matrix.mul_smul] at h
    exact smul_right_injective _ hc h
  set T := Matrix.reducedProjection P Q with hTdef
  have hTproj : IsOrthogonalProjection T := Matrix.reducedProjection_isOrthogonalProjection P Q
  obtain ⟨m, J, -, hJ, hJJ⟩ := hTproj.exists_support_isometry
  obtain ⟨hL', hR'⟩ :=
    compressed_fixed_pair_posDef_reducedProjection L R P Q hL hR rfl rfl J hJ hJJ
  obtain ⟨S, hSu, hSS, hΛpd, hΛdiag⟩ := hL'.exists_congruence_isDiag hR'
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSu
  set Λ := S * (Jᴴ * R * J) * Sᴴ with hΛdef
  set Lf : Matrix (Fin m) (Fin D) ℂ := S * Jᴴ with hLfdef
  set Rt : Matrix (Fin D) (Fin m) ℂ := J * S⁻¹ with hRtdef
  have hRtLf : Rt * Lf = T := by
    rw [hRtdef, hLfdef, Matrix.mul_assoc, ← Matrix.mul_assoc S⁻¹,
      Matrix.nonsing_inv_mul _ hSdet, Matrix.one_mul, hJJ]
  have hLfT : Lf * T = Lf := by
    rw [hLfdef, ← hJJ, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  have hTRt : T * Rt = Rt := by
    rw [hRtdef, ← hJJ, ← Matrix.mul_assoc, Matrix.mul_assoc J, hJ, Matrix.mul_one]
  have hTT : T * T = T := hTproj.2
  set M := virtualSandwich T V T with hMdef
  have hMr : ∀ i j, M (i, j) * (Rt * Lf) = M (i, j) := by
    intro i j
    rw [hRtLf, hMdef, virtualSandwich_apply, Matrix.mul_assoc, hTT]
  set B : MPOTensor n m := fun ij => Lf * V ij * Rt with hBdef
  have hBM : B = fun ij => Lf * M ij * Rt := by
    funext ⟨i, j⟩
    rw [hMdef, virtualSandwich_apply]
    calc Lf * V (i, j) * Rt = (Lf * T) * V (i, j) * (T * Rt) := by rw [hLfT, hTRt]
      _ = Lf * (T * V (i, j) * T) * Rt := by simp only [Matrix.mul_assoc]
  have hMB : M = fun (i, j) => Rt * B (i, j) * Lf := by
    funext ⟨i, j⟩
    rw [hBdef, hMdef, virtualSandwich_apply]
    calc T * V (i, j) * T = (Rt * Lf) * V (i, j) * (Rt * Lf) := by rw [hRtLf]
      _ = Rt * (Lf * V (i, j) * Rt) * Lf := by simp only [Matrix.mul_assoc]
  have hmpo : ∀ N, 0 < N → mpo B N = mpo V N := by
    intro N hN
    rw [hBM, mpo_rectangularSandwich_of_absorb M Lf Rt hMr hN, hMdef,
      mpo_virtualSandwich_reducedProjection_eq V P Q hP hVP hQV N]
  have hBmpu : IsMPU B := fun N hN => by
    rw [hmpo N (by omega)]
    exact hV N hN
  obtain ⟨X, Z, Y, hX, hZ, hY, hXL, hRZ, hPQY⟩ :=
    Matrix.exists_units_supportInvExtension_reducedProjection_rightFactor hL hR
  have hrM : r[M] = r[virtualSandwich L V R] :=
    (rightRank_hat_eq_reducedProjection V L R P Q X Z Y hP hXL hRZ hPQY hVP hQV
      hX hZ hY).symm
  have hℓM : ℓ[M] = ℓ[virtualSandwich L V R] :=
    (leftRank_hat_eq_reducedProjection V L R P Q X Z Y hP hXL hRZ hPQY hVP hQV
      hX hZ hY).symm
  have hrB : r[B] = r[M] := by
    apply le_antisymm
    · rw [hBM]
      exact rightRank_rectangularSandwich_le Lf M Rt
    · rw [hMB]
      exact rightRank_rectangularSandwich_le Rt B Lf
  have hℓB : ℓ[B] = ℓ[M] := by
    apply le_antisymm
    · rw [hBM]
      exact leftRank_rectangularSandwich_le Lf M Rt
    · rw [hMB]
      exact leftRank_rectangularSandwich_le Rt B Lf
  -- the normalized transfer map of `B` is `X ↦ tr(X) Λ`
  have hBflat : B.normalizedFlattening = fun ij => Lf * V.normalizedFlattening ij * Rt := by
    funext ij
    simp only [normalizedFlattening, hBdef, Matrix.mul_smul, Matrix.smul_mul]
  have hRtLRt : Rtᴴ * L * Rt = 1 := by
    rw [hRtdef, Matrix.conjTranspose_mul,
      show (S⁻¹)ᴴ * Jᴴ * L * (J * S⁻¹) = (S⁻¹)ᴴ * (Jᴴ * L * J) * S⁻¹ by
        simp only [Matrix.mul_assoc],
      ← hSS, show (S⁻¹)ᴴ * (Sᴴ * S) * S⁻¹ = (S * S⁻¹)ᴴ * (S * S⁻¹) by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hSdet, Matrix.conjTranspose_one, Matrix.one_mul]
  have hTB : ∀ X, Kraus.transferMap B.normalizedFlattening X = Matrix.trace X • Λ := by
    intro X
    have hconj : Kraus.transferMap B.normalizedFlattening X =
        Lf * Kraus.transferMap V.normalizedFlattening (Rt * X * Rtᴴ) * Lfᴴ := by
      rw [hBflat]
      simp only [Kraus.transferMap_apply, Matrix.conjTranspose_mul, Matrix.mul_sum,
        Matrix.sum_mul, Matrix.mul_assoc]
    rw [hconj, hT, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    · rw [show L * (Rt * X * Rtᴴ) = (L * Rt * X) * Rtᴴ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hRtLRt,
        Matrix.one_mul]
    · rw [hΛdef, hLfdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
  have hE : transferMatrix (Kraus.transferMap B.normalizedFlattening) ^ 1 =
      Matrix.vecMulVec Λ.vec (1 : Matrix (Fin m) (Fin m) ℂ).vec := by
    rw [pow_one]
    ext ⟨j, i⟩ ⟨l, k⟩
    rw [transferMatrix_apply, hTB]
    by_cases hkl : k = l
    · subst hkl
      simp [Matrix.vecMulVec_apply, Matrix.vec, Matrix.trace_single_eq_same]
    · simp [Matrix.vecMulVec_apply, Matrix.vec, Matrix.trace_single_eq_of_ne _ _ _ hkl,
        Matrix.one_apply_ne hkl]
  exact ⟨m, B, ⟨hBmpu.canonicalFormIIOfSuppliedTransferPower Λ hΛpd hΛdiag 1 hE⟩,
    hmpo, hrB.trans hrM, hℓB.trans hℓM⟩

/-! ### Blocking to a rank-one transfer map -/

/-- The normalized transfer matrix of a physical blocking of length `k` is the
`k`-th power of the normalized transfer matrix.

Source: arXiv:1703.09188, lines 397--405. -/
theorem transferMatrix_normalizedFlattening_blockTensor [NeZero d]
    (W : MPOTensor d D) (k : ℕ) :
    transferMatrix (Kraus.transferMap (MPOTensor.blockTensor W k).normalizedFlattening) =
      transferMatrix (Kraus.transferMap W.normalizedFlattening) ^ k := by
  have h := (normalizedDiagonal_doubleLayerTensor (MPOTensor.blockTensor W k)).symm.trans
    (normalizedDiagonal_doubleLayerTensor_blockTensor W k)
  simpa [Matrix.submatrix_submatrix] using
    congrArg (fun A => A.submatrix finProdFinEquiv finProdFinEquiv) h

/-- After blocking at least `D²` sites, the normalized transfer matrix of an
MPU is a rank-one matrix `|ρ)(Φ|` with `(Φ|ρ) = 1`.

Source: arXiv:1703.09188, lines 397--409, and Proposition IV.5,
lines 747--752. -/
theorem IsMPU.exists_transferMatrix_blockTensor_eq_vecMulVec [NeZero d]
    {W : MPOTensor d D} (hW : IsMPU W) {k : ℕ} (hk : D * D ≤ k) :
    ∃ ρ Φ : Fin D × Fin D → ℂ, Φ ⬝ᵥ ρ = 1 ∧
      transferMatrix (Kraus.transferMap (MPOTensor.blockTensor W k).normalizedFlattening) =
        Matrix.vecMulVec ρ Φ := by
  have : NeZero D := hW.neZero_bond
  rw [transferMatrix_normalizedFlattening_blockTensor]
  rcases lt_or_ge 1 D with hD | hD
  · obtain ⟨J, -, hJ, ρ, Φ, hpair, -, -, hpow, hstab⟩ :=
      hW.exists_normalized_transfer_stabilizes_to_rank_one hD
    exact ⟨ρ, Φ, hpair, (hstab k ((hJ.trans (Nat.sub_le _ _)).trans hk)).trans hpow⟩
  · obtain rfl : D = 1 := le_antisymm hD (NeZero.pos D)
    refine ⟨fun _ => 1, fun _ => 1, by simp [dotProduct], ?_⟩
    rw [hW.normalized_transfer_matrix_eq_one_fin_one, one_pow]
    ext ⟨a, b⟩ ⟨c, e⟩
    fin_cases a; fin_cases b; fin_cases c; fin_cases e
    simp [Matrix.vecMulVec_apply]

/-! ### Source ranks of the canonical representative -/

/-- The bond dimension of a canonical-form-II tensor generating the same MPU as
`W` is at most that of `W`.

Source: arXiv:1703.09188, lines 319--356, and Theorem `FundamentalMPU`,
lines 624--652. -/
theorem IsMPUCanonicalFormII.bondDim_le_of_mpo_eq [NeZero d]
    {W : MPOTensor d D} (hW : IsMPU W) {D' : ℕ} {U : MPOTensor d D'}
    (hU : IsMPUCanonicalFormII U) (hmpo : ∀ N, 0 < N → mpo U N = mpo W N) :
    D' ≤ D := by
  have : NeZero D := hW.neZero_bond
  obtain ⟨Dred, -, Ured, hred, hle, hmpoRed⟩ := hW.exists_reduced_cfii_representative
  obtain ⟨rfl, -⟩ := hU.exists_unitary_virtual_gauge_of_mpo_eq hred
    (fun N hN => by rw [hmpo N (by omega), hmpoRed N (by omega)])
  exact hle

/-- If a canonical-form-II tensor `U` generates the same MPU as `W`, then its
blocking of any length `k ≥ D²` is simple, with `r ℓ = d^{2k}`.

Source: arXiv:1703.09188, Proposition IV.2, lines 690--704, and the
`D⁴` blocking of Proposition IV.5, lines 747--752. -/
theorem IsMPUCanonicalFormII.rightRank_mul_leftRank_blockTensor_of_mpo_eq [NeZero d]
    {W : MPOTensor d D} (hW : IsMPU W) {D' : ℕ} {U : MPOTensor d D'}
    (hU : IsMPUCanonicalFormII U) (hmpo : ∀ N, 0 < N → mpo U N = mpo W N)
    {k : ℕ} (hk : D * D ≤ k) :
    r[MPOTensor.blockTensor U k] * ℓ[MPOTensor.blockTensor U k] = d ^ (2 * k) := by
  have : NeZero D := hW.neZero_bond
  have : NeZero D' := hU.neZero_bond
  have hle := hU.bondDim_le_of_mpo_eq hW hmpo
  exact hU.rightRank_mul_leftRank_blockTensor
    (lt_of_lt_of_le (Nat.mul_pos (NeZero.pos D) (NeZero.pos D)) hk)
    (hU.isMPU.blockTensor_isMPUSimple_of_sq_le ((Nat.mul_le_mul hle hle).trans hk))

/-- **The source ranks of the canonical form are those of `L W R`.** Let `W`
generate MPU and block `k ≥ D²` sites, so that the normalized transfer map of
the block is `X ↦ tr(L X) R`. For every canonical-form-II tensor `U`
generating the same MPU, the two source ranks of the block `U_k` are those of
the factor-free contraction of `W_k` with its own transfer matrix, which is
`L W_k R`. No choice of `L` and `R` enters the statement.

Source: arXiv:1703.09188, Proposition IV.5, lines 747--812. -/
theorem IsMPU.sourceRanks_blockTensor_eq_factorFreeSandwich [NeZero d]
    {W : MPOTensor d D} (hW : IsMPU W) {k : ℕ} (hk : D * D ≤ k)
    {D' : ℕ} {U : MPOTensor d D'} (hU : IsMPUCanonicalFormII U)
    (hmpo : ∀ N, 0 < N → mpo U N = mpo W N) :
    r[MPOTensor.blockTensor U k] = r[factorFreeSandwich (MPOTensor.blockTensor W k)] ∧
      ℓ[MPOTensor.blockTensor U k] = ℓ[factorFreeSandwich (MPOTensor.blockTensor W k)] := by
  have : NeZero D := hW.neZero_bond
  have hk0 : 0 < k := lt_of_lt_of_le (Nat.mul_pos (NeZero.pos D) (NeZero.pos D)) hk
  obtain ⟨ρ, Φ, hpair, hE⟩ := hW.exists_transferMatrix_blockTensor_eq_vecMulVec hk
  obtain ⟨L, R, hL, hR, hT⟩ :=
    Kraus.exists_posSemidef_trace_pair_of_transferMatrix_eq_vecMulVec
      (Kraus.reindexPhysical finProdFinEquiv.symm (MPOTensor.blockTensor W k).normalizedFlattening)
      ρ Φ (by rwa [Kraus.transferMap_reindexPhysical_equiv]) hpair
  rw [Kraus.transferMap_reindexPhysical_equiv] at hT
  obtain ⟨m, B, ⟨hB⟩, hmpoB, hr, hℓ⟩ :=
    exists_isMPUCanonicalFormII_of_transferMap_eq_trace_smul (hW.blockTensor k hk0) hL hR hT
  have hEq : ∀ N, 1 < N → mpo (MPOTensor.blockTensor U k) N = mpo B N := by
    intro N hN
    rw [hmpoB N (by omega), mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex,
      hmpo (N * k) (Nat.mul_pos (by omega) hk0)]
  obtain ⟨hr', hℓ'⟩ := (hU.blockTensor k hk0).sourceRanks_eq_of_mpo_eq hB hEq
  rw [factorFreeSandwich_eq_of_trace_pair _ L R hT]
  exact ⟨hr'.symm.trans hr, hℓ'.symm.trans hℓ⟩

/-! ### Constancy along continuous paths -/

/-- **Constancy of the source ranks** (CPSV17, Proposition IV.5). Let
`x ↦ W(x)` be a continuous path of tensors generating MPU, not necessarily in
canonical form, and let `k ≥ D²`. For any two points `x`, `y` and any
canonical-form-II tensors `Uₓ`, `U_y` generating the same MPU as `W(x)` and
`W(y)`, the blocks of length `k` of `Uₓ` and `U_y` have equal right ranks and
equal left ranks.

Source: arXiv:1703.09188, Proposition `prop:continuity-index`, lines 733--818. -/
theorem IsMPU.sourceRanks_canonicalFormII_blockTensor_const [NeZero d]
    {W : unitInterval → MPOTensor d D} (hW : Continuous W) (hMPU : ∀ x, IsMPU (W x))
    {k : ℕ} (hk : D * D ≤ k) {x y : unitInterval} {Dx Dy : ℕ}
    {Ux : MPOTensor d Dx} {Uy : MPOTensor d Dy}
    (hUx : IsMPUCanonicalFormII Ux) (hUy : IsMPUCanonicalFormII Uy)
    (hx : ∀ N, 0 < N → mpo Ux N = mpo (W x) N)
    (hy : ∀ N, 0 < N → mpo Uy N = mpo (W y) N) :
    r[MPOTensor.blockTensor Ux k] = r[MPOTensor.blockTensor Uy k] ∧
      ℓ[MPOTensor.blockTensor Ux k] = ℓ[MPOTensor.blockTensor Uy k] := by
  have : NeZero D := (hMPU x).neZero_bond
  have hprod : ∀ z, r[factorFreeSandwich (MPOTensor.blockTensor (W z) k)] *
      ℓ[factorFreeSandwich (MPOTensor.blockTensor (W z) k)] = d ^ (2 * k) := by
    intro z
    obtain ⟨Dr, -, Ur, hUr, -, hmpoR⟩ := (hMPU z).exists_reduced_cfii_representative
    obtain ⟨hr, hℓ⟩ := (hMPU z).sourceRanks_blockTensor_eq_factorFreeSandwich hk hUr hmpoR
    rw [← hr, ← hℓ]
    exact hUr.rightRank_mul_leftRank_blockTensor_of_mpo_eq (hMPU z) hmpoR hk
  obtain ⟨hr, hℓ⟩ := sourceRanks_const_of_fixed_product
    (hW.blockTensor k).factorFreeSandwich (d ^ (2 * k)) (Nat.pow_pos (NeZero.pos d))
    hprod x y
  obtain ⟨hrx, hℓx⟩ := (hMPU x).sourceRanks_blockTensor_eq_factorFreeSandwich hk hUx hx
  obtain ⟨hry, hℓy⟩ := (hMPU y).sourceRanks_blockTensor_eq_factorFreeSandwich hk hUy hy
  exact ⟨hrx.trans (hr.trans hry.symm), hℓx.trans (hℓ.trans hℓy.symm)⟩

/-- **Constancy of the source ranks at the `D⁴` blocking** (CPSV17,
Proposition IV.5). Along a continuous path of tensors generating MPU, the
source ranks of the `D⁴`-site blocks of the canonical-form-II tensors
generating the same MPUs are constant.

Source: arXiv:1703.09188, Proposition `prop:continuity-index`, lines 733--818. -/
theorem IsMPU.sourceRanks_canonicalFormII_blockTensor_pow_four_const [NeZero d]
    {W : unitInterval → MPOTensor d D} (hW : Continuous W) (hMPU : ∀ x, IsMPU (W x))
    {x y : unitInterval} {Dx Dy : ℕ}
    {Ux : MPOTensor d Dx} {Uy : MPOTensor d Dy}
    (hUx : IsMPUCanonicalFormII Ux) (hUy : IsMPUCanonicalFormII Uy)
    (hx : ∀ N, 0 < N → mpo Ux N = mpo (W x) N)
    (hy : ∀ N, 0 < N → mpo Uy N = mpo (W y) N) :
    r[MPOTensor.blockTensor Ux (D ^ 4)] = r[MPOTensor.blockTensor Uy (D ^ 4)] ∧
      ℓ[MPOTensor.blockTensor Ux (D ^ 4)] = ℓ[MPOTensor.blockTensor Uy (D ^ 4)] := by
  have : NeZero D := (hMPU x).neZero_bond
  refine IsMPU.sourceRanks_canonicalFormII_blockTensor_const hW hMPU ?_ hUx hUy hx hy
  rw [show D ^ 4 = (D * D) * (D * D) by ring]
  exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (NeZero.pos D) (NeZero.pos D))

/-- **Constancy of the source ranks for tensors in canonical form** (CPSV17,
Proposition IV.5). The same conclusion holds for tensors in the canonical form
of lines 259--267, not only canonical form II, since a tensor in canonical
form is similar to one in canonical form II.

Source: arXiv:1703.09188, Proposition `prop:continuity-index`, lines 733--818,
and the gauge to canonical form II, lines 294 and 356. -/
theorem IsMPU.sourceRanks_canonicalForm_blockTensor_const [NeZero d]
    {W : unitInterval → MPOTensor d D} (hW : Continuous W) (hMPU : ∀ x, IsMPU (W x))
    {k : ℕ} (hk : D * D ≤ k) {x y : unitInterval} {Dx Dy : ℕ}
    {Ux : MPOTensor d Dx} {Uy : MPOTensor d Dy}
    (hUx : IsMPU Ux) (hcfx : MPTensor.IsMPUCanonicalForm Ux)
    (hUy : IsMPU Uy) (hcfy : MPTensor.IsMPUCanonicalForm Uy)
    (hx : ∀ N, 0 < N → mpo Ux N = mpo (W x) N)
    (hy : ∀ N, 0 < N → mpo Uy N = mpo (W y) N) :
    r[MPOTensor.blockTensor Ux k] = r[MPOTensor.blockTensor Uy k] ∧
      ℓ[MPOTensor.blockTensor Ux k] = ℓ[MPOTensor.blockTensor Uy k] := by
  have : NeZero Dx := hUx.neZero_bond
  have : NeZero Dy := hUy.neZero_bond
  obtain ⟨X, ⟨hVx⟩⟩ := hUx.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm hcfx
  obtain ⟨Y, ⟨hVy⟩⟩ := hUy.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm hcfy
  rw [← rightRank_blockTensor_virtualSandwich_gl X Ux k,
    ← leftRank_blockTensor_virtualSandwich_gl X Ux k,
    ← rightRank_blockTensor_virtualSandwich_gl Y Uy k,
    ← leftRank_blockTensor_virtualSandwich_gl Y Uy k]
  exact IsMPU.sourceRanks_canonicalFormII_blockTensor_const hW hMPU hk hVx hVy
    (fun N hN => (mpo_virtualSandwich _ Ux _ (Units.inv_mul X) N).trans (hx N hN))
    (fun N hN => (mpo_virtualSandwich _ Uy _ (Units.inv_mul Y) N).trans (hy N hN))

/-- **The MPU index is constant along continuous paths** (CPSV17,
Proposition IV.5). Along a continuous path of tensors of fixed physical and
bond dimensions generating MPU, not necessarily in canonical form, the index
is constant.

Source: arXiv:1703.09188, Proposition `prop:continuity-index`, lines 733--818,
and Definition `def:index`, lines 681--688. -/
theorem IsMPU.index_const_of_continuous [NeZero d] [NeZero D]
    {W : unitInterval → MPOTensor d D} (hW : Continuous W) (hMPU : ∀ x, IsMPU (W x))
    (x y : unitInterval) : (hMPU x).index = (hMPU y).index := by
  obtain ⟨Dx, -, Ux, hUx, hlex, hx⟩ := (hMPU x).exists_reduced_cfii_representative
  obtain ⟨Dy, -, Uy, hUy, hley, hy⟩ := (hMPU y).exists_reduced_cfii_representative
  have : NeZero Dx := hUx.neZero_bond
  have : NeZero Dy := hUy.neZero_bond
  have hk0 : 0 < D * D := Nat.mul_pos (NeZero.pos D) (NeZero.pos D)
  rw [(hMPU x).index_eq_canonical_representative hUx hx,
    (hMPU y).index_eq_canonical_representative hUy hy,
    hUx.index_eq_logb_of_isMPUSimple_blockTensor hk0
      (hUx.isMPU.blockTensor_isMPUSimple_of_sq_le (Nat.mul_le_mul hlex hlex)),
    hUy.index_eq_logb_of_isMPUSimple_blockTensor hk0
      (hUy.isMPU.blockTensor_isMPUSimple_of_sq_le (Nat.mul_le_mul hley hley))]
  obtain ⟨hr, hℓ⟩ :=
    IsMPU.sourceRanks_canonicalFormII_blockTensor_const hW hMPU le_rfl hUx hUy hx hy
  rw [hr, hℓ]

end MPOTensor
