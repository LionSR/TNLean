/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.MPS.MPU.StaircaseGates
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.RepresentativeIndex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Source cuts of an actual supplied two-site standard form

The two cuts of the supplied tensor itself have explicit factors. Their
intermediate spaces pair a physical spin with an original source leg. Contracting
the right factors gives exactly `v₂₃ (u₁₂ ⊗ u₃₄)`; contracting the left
factors gives exactly `v₂₃`. These act on four original spins. The tensor
has not been blocked again before taking its cuts.

These identities isolate the source-factor construction needed in the
forward local time-reversal argument. They assert actual cut equalities,
not the existence of comparison gauges or a local symmetry certificate.
For the standard form constructed from simple canonical source data, the
coarse left normalizations are proved by Kronecker products. Existing
blocking-rank saturation identifies the actual cut dimensions. Full row
rank then supplies the right inverses, yielding an actual normalized
source-factor record at the original canonical boundary.

**Scope restriction (canonical source construction):** The normalization
and record constructions use the actual standard form constructed from a
reduced canonical-form-II tensor. They do not normalize arbitrary supplied
half factors. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, proof of `PropChiral`, `eq:block-twosites`,
lines 1237–1252; cut conventions are `eq:sf-svd`, lines 479–506.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor.TwoSiteStandardFormData

variable {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
  {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- Left factor of the first cut of the supplied tensor: retain its first
output spin and the original right half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutX₁ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin (d * d) × Fin D) (Fin d × Fin r) ℂ :=
  fun (i, γ) (a, s) ↦
    (1 : Matrix (Fin d) (Fin d) ℂ) (finProdFinEquiv.symm i).1 a *
      S.X₁ ((finProdFinEquiv.symm i).2, γ) s

/-- Right factor of the first cut, obtained by joining the unshifted gate
to the original left half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutY₁ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin d × Fin r) (Fin D × Fin (d * d)) ℂ :=
  fun (a, s) (α, j) ↦ ∑ t : Fin ℓ,
    S.X₂ (α, a) t * u (t, s) (finProdFinEquiv.symm j)

/-- Left factor of the second cut: retain its second output spin and the
original left half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutX₂ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin D × Fin (d * d)) (Fin ℓ × Fin d) ℂ :=
  fun (α, i) (t, b) ↦ S.X₂ (α, (finProdFinEquiv.symm i).1) t *
    (1 : Matrix (Fin d) (Fin d) ℂ) (finProdFinEquiv.symm i).2 b

/-- Right factor of the second cut, joining the unshifted gate to the
original right half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutY₂ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin ℓ × Fin d) (Fin (d * d) × Fin D) ℂ :=
  fun (t, b) (j, γ) ↦ ∑ s : Fin r,
    u (t, s) (finProdFinEquiv.symm j) * S.X₁ (b, γ) s

/-- The first actual cut factors through the displayed pair space. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244. -/
theorem sourceCutM₁_eq_cutX₁_mul_cutY₁ (S : TwoSiteStandardFormData W u v) :
    sourceCutM₁ W = S.cutX₁ * S.cutY₁ := by
  classical
  ext ⟨i, γ⟩ ⟨α, j⟩
  rw [sourceCutM₁_apply, S.W_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, cutX₁, cutY₁,
    Matrix.one_apply, ite_mul, zero_mul, Finset.mul_sum,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ s _
  ring

/-- The second actual cut factors through the displayed pair space. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244. -/
theorem sourceCutM₂_eq_cutX₂_mul_cutY₂ (S : TwoSiteStandardFormData W u v) :
    sourceCutM₂ W = S.cutX₂ * S.cutY₂ := by
  classical
  ext ⟨α, i⟩ ⟨j, γ⟩
  rw [sourceCutM₂_apply, S.W_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, cutX₂, cutY₂,
    Matrix.one_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, mul_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Contracting the two right cut factors gives the literal four-spin
three-gate expression, with no additional blocking. Source:
arXiv:1703.09188, `eq:block-twosites` and `UUdaggertrick`, lines 1237–1252. -/
theorem cutY₂_cutY₁_eq_staircaseMiddle_mul_kronecker
    (S : TwoSiteStandardFormData W u v) :
    (fun (l : (Fin ℓ × Fin d) × (Fin d × Fin r))
      (r : (Fin d × Fin d) × (Fin d × Fin d)) ↦
      ∑ β : Fin D, S.cutY₂ l.1 (finProdFinEquiv r.1, β) *
        S.cutY₁ l.2 (β, finProdFinEquiv r.2)) =
      staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u) := by
  classical
  ext ⟨⟨a, b⟩, c, e⟩ ⟨i, j⟩
  simp only [cutY₁, cutY₂, Equiv.symm_apply_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type, staircaseMiddle, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, one_mul, mul_one]
  simp_rw [S.v_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ β _
  ring

/-- Contracting the two left cut factors gives the middle gate on four
original spins. Source: arXiv:1703.09188, `eq:block-twosites` and
`UUdaggertrick`, lines 1237–1252. -/
theorem cutX₁_cutX₂_eq_staircaseMiddle
    (S : TwoSiteStandardFormData W u v) :
    (fun (l : (Fin d × Fin d) × (Fin d × Fin d))
      (r : (Fin d × Fin r) × (Fin ℓ × Fin d)) ↦
      ∑ β : Fin D, S.cutX₁ (finProdFinEquiv l.1, β) r.1 *
        S.cutX₂ (β, finProdFinEquiv l.2) r.2) =
      staircaseMiddle (A := Fin d) (E := Fin d) v := by
  classical
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp only [cutX₁, cutX₂, Equiv.symm_apply_apply, staircaseMiddle,
    Matrix.kroneckerMap_apply, S.v_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

private theorem cutX₂_isIsometry_of_normalized_half_factor
    (S : TwoSiteStandardFormData W u v) (hX : S.X₂.IsIsometry) :
    S.cutX₂.IsIsometry := by
  classical
  let e : ((Fin D × Fin d) × Fin d) ≃ (Fin D × Fin (d * d)) :=
    (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)
  have hI : (1 : Matrix (Fin d) (Fin d) ℂ).IsIsometry := by
    simp [Matrix.IsIsometry]
  have h := Matrix.IsIsometry.kronecker S.X₂ (1 : Matrix (Fin d) (Fin d) ℂ) hX hI
  have h' := Matrix.IsIsometry.reindex _ h e (Equiv.refl _)
  have hfactor : S.cutX₂ = Matrix.reindex e (Equiv.refl _)
      (S.X₂ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    ext ⟨α, i⟩ ⟨t, b⟩
    simp [cutX₂, e, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  rw [hfactor]
  exact h'

private theorem cutX₁_weighted_isometry_of_normalized_half_factor
    (S : TwoSiteStandardFormData W u v) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hX : S.X₁ᴴ * sourceWeight (d := d) ρ * S.X₁ = 1) :
    S.cutX₁ᴴ * sourceWeight (d := d * d) ρ * S.cutX₁ = 1 := by
  classical
  let e : (Fin d × (Fin d × Fin D)) ≃ (Fin (d * d) × Fin D) :=
    (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))
  let I : Matrix (Fin d) (Fin d) ℂ := 1
  have hfactor : S.cutX₁ = Matrix.reindex e (Equiv.refl _) (I ⊗ₖ S.X₁) := by
    ext ⟨i, γ⟩ ⟨a, s⟩
    simp [cutX₁, e, I, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  have hweight : sourceWeight (d := d * d) ρ =
      Matrix.reindex e e (I ⊗ₖ sourceWeight (d := d) ρ) := by
    ext ⟨i, α⟩ ⟨j, β⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective j
    simp [sourceWeight, e, I, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, ite_and, mul_ite, ite_mul]
  have hprod : (I ⊗ₖ S.X₁)ᴴ * (I ⊗ₖ sourceWeight (d := d) ρ) * (I ⊗ₖ S.X₁) = 1 := by
    rw [Matrix.conjTranspose_kronecker]
    change ((1 : Matrix (Fin d) (Fin d) ℂ)ᴴ ⊗ₖ S.X₁ᴴ) *
        (1 ⊗ₖ sourceWeight (d := d) ρ) * (1 ⊗ₖ S.X₁) = 1
    rw [Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, hX, Matrix.one_kronecker_one]
  rw [hfactor, hweight, Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e (I ⊗ₖ S.X₁)ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ e e (I ⊗ₖ sourceWeight (d := d) ρ) *
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) (I ⊗ₖ S.X₁) = 1
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul, hprod,
    Matrix.reindexLinearEquiv_one]

end MPOTensor.TwoSiteStandardFormData

namespace MPOTensor

/-- The coarse first cut factor of the actual canonical source standard form
has its required weighted normalization, at the original canonical boundary.
The normalization is derived from the source-factor construction, not supplied
as a new witness. Source: arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244,
and `Y1Y1X1X1`, lines 487–494. -/
theorem IsMPUCanonicalFormII.twoSite_cutX₁_weighted_isometry
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (hU.twoSiteStandardFormData hsimple).cutX₁ᴴ *
        sourceWeight (d := d * d) hU.ρ * (hU.twoSiteStandardFormData hsimple).cutX₁ = 1 :=
  TwoSiteStandardFormData.cutX₁_weighted_isometry_of_normalized_half_factor
    (hU.twoSiteStandardFormData hsimple) hU.ρ
    (sourceFactors U hU.ρ hU.ρ_posDef).X₁_weighted_isometry

/-- The coarse second cut factor of the actual canonical source standard form
is an isometry. No extra normalization witness is assumed. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244, and
`Y1Y1X1X1`, lines 487–494. -/
theorem IsMPUCanonicalFormII.twoSite_cutX₂_isIsometry
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (hU.twoSiteStandardFormData hsimple).cutX₂.IsIsometry :=
  TwoSiteStandardFormData.cutX₂_isIsometry_of_normalized_half_factor
    (hU.twoSiteStandardFormData hsimple)
    (sourceFactors U hU.ρ hU.ρ_posDef).X₂_isometry

/-- The actual cut ranks of the two-site standard-form tensor are the
cardinalities of its coarse pair spaces. They follow from simplicity and
blocking rank saturation; no endpoint-rank identity is assumed. Source:
arXiv:1703.09188, `index-well-defined`, lines 697–704, and
`eq:block-twosites`, lines 1237–1244. -/
theorem IsMPUCanonicalFormII.twoSite_sourceRanks
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    r[blockTwo U] = d * r[U] ∧ ℓ[blockTwo U] = ℓ[U] * d := by
  have hone : blockTensor U 1 = reindexPhysical (MPSTensor.singleBlockEquiv d) U := by
    funext i j
    simp [blockTensor, MPSTensor.wordOfBlock, Kraus.wordOfBlock_one,
      reindexPhysical, evalWord]
  have hSone : IsMPUSimple (blockTensor U 1) := by
    rw [hone]
    exact hsimple.reindexPhysical _
  have hStwo : IsMPUSimple (blockTensor U 2) :=
    hU.isMPU.blockTensor_isMPUSimple_of_le (by decide) (by decide) hSone
  have hranks := blockingRanks_eq_pow_mul_of_products U (by decide : 1 ≤ 2)
    (Nat.pos_of_ne_zero hU.neZero_phys.out)
    (hU.rightRank_mul_leftRank_blockTensor (by decide) hSone)
    (hU.rightRank_mul_leftRank_blockTensor (by decide) hStwo)
  simp only [hone, rightRank_reindexPhysical, leftRank_reindexPhysical] at hranks
  simpa only [blockTwo_eq_blockTensor_reindex, rightRank_reindexPhysical,
    leftRank_reindexPhysical, Nat.reduceSub, pow_one, Nat.mul_comm] using hranks

private theorem exists_right_inverse_of_rank_eq_card
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (M : Matrix a b ℂ) (hM : M.rank = Fintype.card a) :
    ∃ Z : Matrix b a ℂ, M * Z = 1 := by
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Matrix.rank, Module.finrank_pi] using hM
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (LinearMap.range_eq_top.mp hrange)

/-- Normalized coarse source factors of the actual two-site canonical source
standard form. Both cut-rank identifications and both right inverses are
derived; the original recorded canonical boundary is retained. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244, using the
normalizations `Y1Y1X1X1` and right inverses `YZ=1`, lines 487–506. -/
noncomputable def IsMPUCanonicalFormII.twoSiteSourceFactors
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) : SourceFactors (blockTwo U) hU.ρ := by
  classical
  let S := hU.twoSiteStandardFormData hsimple
  obtain ⟨hr, hl⟩ := hU.twoSite_sourceRanks hsimple
  let er : (Fin d × Fin r[U]) ≃ Fin r[blockTwo U] :=
    finProdFinEquiv.trans (finCongr hr.symm)
  let el : (Fin ℓ[U] × Fin d) ≃ Fin ℓ[blockTwo U] :=
    finProdFinEquiv.trans (finCongr hl.symm)
  have hY₁ : S.cutY₁.rank = Fintype.card (Fin d × Fin r[U]) := by
    apply le_antisymm S.cutY₁.rank_le_card_height
    calc
      Fintype.card (Fin d × Fin r[U]) = (sourceCutM₁ (blockTwo U)).rank := by
        simpa only [Fintype.card_prod, Fintype.card_fin, rightRank_eq] using hr.symm
      _ = (S.cutX₁ * S.cutY₁).rank := congrArg Matrix.rank S.sourceCutM₁_eq_cutX₁_mul_cutY₁
      _ ≤ S.cutY₁.rank := Matrix.rank_mul_le_right _ _
  have hY₂ : S.cutY₂.rank = Fintype.card (Fin ℓ[U] × Fin d) := by
    apply le_antisymm S.cutY₂.rank_le_card_height
    calc
      Fintype.card (Fin ℓ[U] × Fin d) = (sourceCutM₂ (blockTwo U)).rank := by
        simpa only [Fintype.card_prod, Fintype.card_fin, leftRank_eq] using hl.symm
      _ = (S.cutX₂ * S.cutY₂).rank := congrArg Matrix.rank S.sourceCutM₂_eq_cutX₂_mul_cutY₂
      _ ≤ S.cutY₂.rank := Matrix.rank_mul_le_right _ _
  obtain ⟨Z₁, hZ₁⟩ := exists_right_inverse_of_rank_eq_card S.cutY₁ hY₁
  obtain ⟨Z₂, hZ₂⟩ := exists_right_inverse_of_rank_eq_card S.cutY₂ hY₂
  refine {
    X₁ := Matrix.reindex (Equiv.refl _) er S.cutX₁
    Y₁ := Matrix.reindex er (Equiv.refl _) S.cutY₁
    Z₁ := Matrix.reindex (Equiv.refl _) er Z₁
    X₂ := Matrix.reindex (Equiv.refl _) el S.cutX₂
    Y₂ := Matrix.reindex el (Equiv.refl _) S.cutY₂
    Z₂ := Matrix.reindex (Equiv.refl _) el Z₂
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := ?_
    X₁_weighted_isometry := ?_
    X₂_isometry := ?_
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := ?_ }
  · change sourceCutM₁ (blockTwo U) =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er S.cutX₁ *
        Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) S.cutY₁
    rw [Matrix.reindexLinearEquiv_mul]
    exact S.sourceCutM₁_eq_cutX₁_mul_cutY₁
  · change sourceCutM₂ (blockTwo U) =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) el S.cutX₂ *
        Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl _) S.cutY₂
    rw [Matrix.reindexLinearEquiv_mul]
    exact S.sourceCutM₂_eq_cutX₂_mul_cutY₂
  · rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) S.cutX₁ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
          (sourceWeight (d := d * d) hU.ρ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er S.cutX₁ = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul,
      hU.twoSite_cutX₁_weighted_isometry hsimple, Matrix.reindexLinearEquiv_one]
  · exact Matrix.IsIsometry.reindex S.cutX₂
      (hU.twoSite_cutX₂_isIsometry hsimple) (Equiv.refl _) el
  · change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) S.cutY₁ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er Z₁ = 1
    rw [Matrix.reindexLinearEquiv_mul, hZ₁, Matrix.reindexLinearEquiv_one]
  · change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl _) S.cutY₂ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) el Z₂ = 1
    rw [Matrix.reindexLinearEquiv_mul, hZ₂, Matrix.reindexLinearEquiv_one]

/-- Actual adjoint invariance at the even original chain lengths forces
both source ranks of the original simple canonical tensor to equal its
physical dimension. Only a single two-site blocking is used. Source:
arXiv:1703.09188, `PropChiral`, lines 1201–1252, including the zero-index
observation preceding the proposition. The hypothesis is on original
lengths, not on a further blocking of the supplied standard form. -/
theorem IsMPUCanonicalFormII.sourceRanks_eq_phys_of_even_mpo_eq_adjoint
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ) :
    r[U] = d ∧ ℓ[U] = d := by
  have hEq : ∀ N : ℕ, 1 < N →
      mpo (blockTensor U 2) N =
        mpo (physicalAdjointTensor (blockTensor U 2)) N := by
    intro N hN
    ext σ τ
    rw [mpo_physicalAdjointTensor]
    have h := congrArg (fun M ↦ M
        ((MPSTensor.blockedConfigEquiv d N 2) σ)
        ((MPSTensor.blockedConfigEquiv d N 2) τ))
      (hTR (N * 2) (by omega) ⟨N, by omega⟩)
    simpa only [mpo_blockTensor_eq_reindex, Matrix.reindex_apply,
      Equiv.symm_symm, Matrix.conjTranspose_apply] using h
  let hB := hU.blockTensor 2 (by decide)
  have hsame := hB.sourceRanks_eq_of_mpo_eq hB.physicalAdjointTensor hEq
  have hbalanced : ℓ[blockTensor U 2] = r[blockTensor U 2] := by
    simpa only [rightRank_physicalAdjointTensor] using hsame.1
  obtain ⟨hr, hl⟩ := hU.twoSite_sourceRanks hsimple
  simp only [blockTwo_eq_blockTensor_reindex, rightRank_reindexPhysical,
    leftRank_reindexPhysical] at hr hl
  have hrℓ : r[U] = ℓ[U] := by
    apply mul_left_cancel₀ hU.neZero_phys.out
    calc
      d * r[U] = r[blockTensor U 2] := hr.symm
      _ = ℓ[blockTensor U 2] := hbalanced.symm
      _ = d * ℓ[U] := hl.trans (Nat.mul_comm _ _)
  have hprod := (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  rw [hrℓ] at hprod
  have hℓ : ℓ[U] = d :=
    (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hprod
  exact ⟨hrℓ.trans hℓ, hℓ⟩

end MPOTensor
