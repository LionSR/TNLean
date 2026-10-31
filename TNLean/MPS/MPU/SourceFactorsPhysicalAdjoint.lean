/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceYOneNormalization
import TNLean.MPS.MPU.SourceYTwoNormalization
import TNLean.MPS.MPU.SimpleTensorEquivalence
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Physical-adjoint factors for the actual supplied source decompositions

The source Y Gram normalizations hold for every normalized source-factor
record at the recorded canonical boundary. This follows by cancellation of
two factorizations of the same cut, not by choosing new singular vectors.
At zero index these Gram matrices are identities. Swapping the two cuts
and taking adjoints of their factors therefore constructs source factors
for the physical adjoint, retaining the same canonical boundary.

**Scope restriction (canonical source factors):** The constructions use a
simple reduced canonical-form-II tensor; adjoint simplicity is derived. The
zero-index adjoint record additionally uses its actual source ranks equal
to physical dimension. These are explicit mathematical prerequisites here;
the global local-characterization argument must derive them, as recorded in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, `PropChiral`, lines 1237–1252, with source
normalizations `Y1Y1X1X1` and `YZ=1`, lines 487–506; the Y Gram formulas are
arXiv:2502.20257, `eq:MPUnice3`, lines 1326–1398.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPOTensor

/-- Bijective physical relabeling preserves the actual reduced canonical
presentation and its recorded boundary. Source: arXiv:1703.09188,
canonical-form conventions, lines 269–305, and the coordinate regrouping
in `eq:block-twosites`, lines 1237–1244. -/
noncomputable def IsMPUCanonicalFormII.reindexPhysical
    {d d' D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (e : Fin d' ≃ Fin d) : IsMPUCanonicalFormII (MPOTensor.reindexPhysical e U) := by
  let ep : Fin (d' * d') ≃ Fin (d * d) :=
    finProdFinEquiv.symm.trans ((Equiv.prodCongr e e).trans finProdFinEquiv)
  have heq : (MPOTensor.reindexPhysical e U).normalizedFlattening =
      Kraus.reindexPhysical ep U.normalizedFlattening := by
    have hd : d' = d := by simpa only [Fintype.card_fin] using Fintype.card_congr e
    subst d'
    ext i α β
    simp [normalizedFlattening, MPOTensor.reindexPhysical, Kraus.reindexPhysical,
      ep, toMPSTensor, Matrix.smul_apply]
  let data := hU.cfii.reindexPhysical ep
  have hfull : data.toCPSVCanonicalFormData.HasFullSupport := by
    change ∑ k, hU.cfii.toCPSVCanonicalFormData.dim k = D
    exact hU.fullSupport_eq
  refine {
    isMPU := ?_
    cfii := heq.symm ▸ data
    fullSupport_eq := MPSTensor.CPSVCanonicalFormIIData.hasFullSupport_cast data hfull heq
    ρ := hU.ρ
    ρ_posDef := hU.ρ_posDef
    ρ_isDiag := hU.ρ_isDiag
    ρ_trace := hU.ρ_trace
    ρ_fixed := ?_ }
  · intro N hN
    rw [mpo_reindexPhysical]
    exact Matrix.reindex_mem_unitaryGroup _ _ (hU.isMPU N hN)
  · rw [heq, MPSTensor.transferMap_reindexPhysical_equiv]
    exact hU.ρ_fixed

/-- Physical adjunction preserves simplicity for the actual reduced
canonical tensor: its two source ranks are exchanged, so their product
is unchanged. Source: arXiv:1703.09188, `ThmFund1`, lines 563–601,
and the cut exchange preceding `PropChiral`, lines 1196–1207. -/
theorem IsMPUCanonicalFormII.isMPUSimple_physicalAdjointTensor
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) : IsMPUSimple (MPOTensor.physicalAdjointTensor U) := by
  have hrank : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  apply (hU.physicalAdjointTensor.isMPUSimple_tfae.out 1 2).mpr
  rw [rightRank_physicalAdjointTensor, leftRank_physicalAdjointTensor, mul_comm]
  exact hrank

/-- Every supplied normalized source record of a simple canonical tensor
has unitary unshifted gate. Its isometry is the standing source-gate theorem;
simplicity makes the actual source and target dimensions equal. Source:
arXiv:1703.09188, `lemuisometry` and `ThmFund1`, lines 545–601. -/
theorem IsMPUCanonicalFormII.sourceFactors_sourceU_isUnitaryBetween
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ) :
    (SourceFactors.sourceU U S).IsUnitaryBetween := by
  let : NeZero d := hU.neZero_phys
  have hu := SourceFactors.sourceU_isIsometry_of_isMPU U hU.isMPU S hU.ρ_isDiag _
    hU.normalizedDiagonal_pow_eq_vecMulVec
  have hprod := (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  exact hu.isUnitaryBetween_of_card_eq _ (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_comm _ _).trans hprod)

private theorem normalized_cut_gram_transport
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]
    (X Xt : Matrix a b ℂ) (Y Yt : Matrix b c ℂ) (Zt : Matrix c b ℂ)
    (L : Matrix a a ℂ) (K : Matrix c c ℂ) (δ : ℂ)
    (hL : L.IsHermitian) (hfac : X * Y = Xt * Yt)
    (hX : Xᴴ * L * X = 1) (hXt : Xtᴴ * L * Xt = 1)
    (hZt : Yt * Zt = 1) (hY : Y * K * Yᴴ = δ • 1) :
    Yt * K * Ytᴴ = δ • 1 := by
  let A := Xtᴴ * L * X
  have hYt : Yt = A * Y := by
    calc
      Yt = (Xtᴴ * L * Xt) * Yt := by rw [hXt, Matrix.one_mul]
      _ = (Xtᴴ * L) * (Xt * Yt) := by simp only [Matrix.mul_assoc]
      _ = (Xtᴴ * L) * (X * Y) := by rw [hfac]
      _ = A * Y := by simp only [A, Matrix.mul_assoc]
  have hXt_range : Xt = X * (Y * Zt) := by
    calc
      Xt = Xt * (Yt * Zt) := by rw [hZt, Matrix.mul_one]
      _ = (Xt * Yt) * Zt := by simp only [Matrix.mul_assoc]
      _ = (X * Y) * Zt := by rw [hfac]
      _ = X * (Y * Zt) := by simp only [Matrix.mul_assoc]
  have hproj : X * Xᴴ * L * Xt = Xt := by
    calc
      X * Xᴴ * L * Xt = X * (Xᴴ * L * X) * (Y * Zt) := by
        rw [hXt_range]
        simp only [Matrix.mul_assoc]
      _ = X * (Y * Zt) := by rw [hX, Matrix.mul_one]
      _ = Xt := hXt_range.symm
  have hA : A * Aᴴ = 1 := by
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq]
    calc
      (Xtᴴ * L * X) * (Xᴴ * (L * Xt)) = Xtᴴ * L * (X * Xᴴ * L * Xt) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hproj, hXt]
  rw [hYt, Matrix.conjTranspose_mul]
  calc
    (A * Y) * K * (Yᴴ * Aᴴ) = A * (Y * K * Yᴴ) * Aᴴ := by
      simp only [Matrix.mul_assoc]
    _ = δ • 1 := by
      rw [hY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hA]

/-- The first Y Gram formula for every supplied normalized source record at
the actual canonical boundary. No change-of-gates witness is assumed.
Source: arXiv:2502.20257, `eq:MPUnice3`, lines 1326–1398. -/
theorem IsMPUCanonicalFormII.sourceFactors_Y₁_mul_conjTranspose
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (T : SourceFactors U hU.ρ) :
    T.Y₁ * T.Y₁ᴴ = ((d : ℂ) / (r[U] : ℂ)) • 1 := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have h := normalized_cut_gram_transport S.X₁ T.X₁ S.Y₁ T.Y₁ T.Z₁
    (sourceWeight (d := d) hU.ρ) 1 ((d : ℂ) / (r[U] : ℂ))
    (sourceWeight_posDef (d := d) hU.ρ_posDef).isHermitian
    (S.sourceCutM₁_eq.symm.trans T.sourceCutM₁_eq)
    S.X₁_weighted_isometry T.X₁_weighted_isometry T.Y₁_mul_Z₁
    (by simpa only [Matrix.mul_one] using
      (hU.sourceY₁_mul_conjTranspose hsimple
        (hU.isMPUSimple_physicalAdjointTensor hsimple)))
  simpa only [Matrix.mul_one] using h

/-- The weighted second Y Gram formula for every supplied normalized record
at the actual canonical boundary. Source: arXiv:2502.20257,
`eq:MPUnice3`, lines 1326–1398. -/
theorem IsMPUCanonicalFormII.sourceFactors_Y₂_weighted_mul_conjTranspose
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (T : SourceFactors U hU.ρ) :
    T.Y₂ * sourceWeight (d := d) hU.ρ * T.Y₂ᴴ =
      ((d : ℂ) / (ℓ[U] : ℂ)) • 1 := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  exact normalized_cut_gram_transport S.X₂ T.X₂ S.Y₂ T.Y₂ T.Z₂
    1 (sourceWeight (d := d) hU.ρ) ((d : ℂ) / (ℓ[U] : ℂ))
    Matrix.isHermitian_one
    (S.sourceCutM₂_eq.symm.trans T.sourceCutM₂_eq)
    (by simpa only [Matrix.IsIsometry, Matrix.mul_one] using S.X₂_isometry)
    (by simpa only [Matrix.IsIsometry, Matrix.mul_one] using T.X₂_isometry) T.Y₂_mul_Z₂
    (hU.sourceY₂_weighted_mul_conjTranspose hsimple
      (hU.isMPUSimple_physicalAdjointTensor hsimple))

/-- Swap the two cuts and take adjoints of their actual supplied factors.
The zero-index Y normalizations supply the new left isometries; the old
left isometries supply the new right inverses. Source: arXiv:1703.09188,
proof of `PropChiral`, lines 1237–1252. -/
noncomputable def SourceFactors.physicalAdjoint
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    SourceFactors (MPOTensor.physicalAdjointTensor U) hU.ρ := by
  classical
  let er : Fin ℓ[U] ≃ Fin r[MPOTensor.physicalAdjointTensor U] :=
    finCongr (rightRank_physicalAdjointTensor U).symm
  let el : Fin r[U] ≃ Fin ℓ[MPOTensor.physicalAdjointTensor U] :=
    finCongr (leftRank_physicalAdjointTensor U).symm
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hU.neZero_phys.out
  have hY₁ := hU.sourceFactors_Y₁_mul_conjTranspose hsimple S
  have hY₂ := hU.sourceFactors_Y₂_weighted_mul_conjTranspose hsimple S
  have hscalar₁ : (d : ℂ) / (r[U] : ℂ) = 1 := by rw [hr, div_self hd]
  have hscalar₂ : (d : ℂ) / (ℓ[U] : ℂ) = 1 := by rw [hl, div_self hd]
  rw [hscalar₁, one_smul] at hY₁
  rw [hscalar₂, one_smul] at hY₂
  refine {
    X₁ := Matrix.reindex (Equiv.refl _) er S.Y₂ᴴ
    Y₁ := Matrix.reindex er (Equiv.refl _) S.X₂ᴴ
    Z₁ := Matrix.reindex (Equiv.refl _) er S.X₂
    X₂ := Matrix.reindex (Equiv.refl _) el S.Y₁ᴴ
    Y₂ := Matrix.reindex el (Equiv.refl _) S.X₁ᴴ
    Z₂ := Matrix.reindex (Equiv.refl _) el (sourceWeight (d := d) hU.ρ * S.X₁)
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := ?_
    X₁_weighted_isometry := ?_
    X₂_isometry := ?_
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := ?_ }
  · rw [sourceCutM₁_physicalAdjointTensor, S.sourceCutM₂_eq, Matrix.conjTranspose_mul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) er (Equiv.refl _) _ _).symm
  · rw [sourceCutM₂_physicalAdjointTensor, S.sourceCutM₁_eq, Matrix.conjTranspose_mul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) el (Equiv.refl _) _ _).symm
  · rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_conjTranspose]
    change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) S.Y₂ *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
          (sourceWeight (d := d) hU.ρ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er S.Y₂ᴴ = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul, hY₂,
      Matrix.reindexLinearEquiv_one]
  · change (Matrix.reindex (Equiv.refl _) el S.Y₁ᴴ)ᴴ *
      Matrix.reindex (Equiv.refl _) el S.Y₁ᴴ = 1
    rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_conjTranspose]
    change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl _) S.Y₁ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) el S.Y₁ᴴ = 1
    rw [Matrix.reindexLinearEquiv_mul, hY₁, Matrix.reindexLinearEquiv_one]
  · change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl (Fin D × Fin d)) S.X₂ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin D × Fin d)) er S.X₂ = 1
    rw [Matrix.reindexLinearEquiv_mul, S.X₂_isometry, Matrix.reindexLinearEquiv_one]
  · change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl (Fin d × Fin D)) S.X₁ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin d × Fin D)) el
        (sourceWeight (d := d) hU.ρ * S.X₁) = 1
    rw [Matrix.reindexLinearEquiv_mul, ← Matrix.mul_assoc,
      S.X₁_weighted_isometry, Matrix.reindexLinearEquiv_one]

/-- The adjoint record's unshifted gate is the adjoint of the actual
supplied shifted gate, in the canonical swapped-rank coordinates. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1249. -/
theorem SourceFactors.sourceU_physicalAdjoint
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    let er := finCongr (rightRank_physicalAdjointTensor U).symm
    let el := finCongr (leftRank_physicalAdjointTensor U).symm
    SourceFactors.sourceU (MPOTensor.physicalAdjointTensor U)
        (SourceFactors.physicalAdjoint hU hsimple S hr hl) =
      Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (SourceFactors.sourceV U S)ᴴ := by
  dsimp only
  ext ⟨l, r⟩ ⟨i, j⟩
  simp [SourceFactors.sourceU, SourceFactors.sourceV, SourceFactors.physicalAdjoint,
    Matrix.reindex_apply, Matrix.conjTranspose_apply]

/-- The adjoint record's shifted gate is the adjoint of the actual supplied
unshifted gate, in the canonical swapped-rank coordinates. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1249. -/
theorem SourceFactors.sourceV_physicalAdjoint
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    let er := finCongr (rightRank_physicalAdjointTensor U).symm
    let el := finCongr (leftRank_physicalAdjointTensor U).symm
    SourceFactors.sourceV (MPOTensor.physicalAdjointTensor U)
        (SourceFactors.physicalAdjoint hU hsimple S hr hl) =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (SourceFactors.sourceU U S)ᴴ := by
  dsimp only
  ext ⟨i, j⟩ ⟨r, l⟩
  simp [SourceFactors.sourceU, SourceFactors.sourceV, SourceFactors.physicalAdjoint,
    Matrix.reindex_apply, Matrix.conjTranspose_apply]

end MPOTensor
