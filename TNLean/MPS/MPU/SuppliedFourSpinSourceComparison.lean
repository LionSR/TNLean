/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SuppliedHalfFactorMinimality
import TNLean.MPS.MPU.SourceDecompositionUniqueness
import TNLean.MPS.MPU.SourceFactorsPhysicalAdjoint

/-!
# Supplied four-spin gates and actual normalized source gates

The minimal cut factorizations of any supplied standard form can be compared
with normalized source factors of the same ambient tensor. The raw
reciprocal-unitary comparison suffices: its positive scalar and reciprocal
cancel in both gate contractions. No normalization of the supplied half
factors is assumed or inferred.

Source: CPSV17, arXiv:1703.09188, `eq:block-twosites` and `FundamentalMPU`,
lines 624–648 and 1237–1252; raw decomposition uniqueness is FBC25,
arXiv:2502.20257, `lem:deco`, lines 1052–1066.

**Scope restriction (canonical ambient presentation):** The canonical
corollary takes an ambient canonical presentation explicitly. The supplied
standard form and its minimal cut ranks do not
imply minimality or canonicality of the ambient virtual space. This is
not the unrestricted local symmetry criterion; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPOTensor

private theorem sourceV_contraction_transport
    {d D : ℕ} {U : MPOTensor d D}
    {X₁ Xt₁ : Matrix (Fin d × Fin D) (Fin r[U]) ℂ}
    {X₂ Xt₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ}
    {K₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    {K₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ}
    (hX₁ : Xt₁ = X₁ * K₁) (hX₂ : Xt₂ = X₂ * K₂) :
    (fun ((p, q) : Fin d × Fin d) ((r, l) : Fin r[U] × Fin ℓ[U]) ↦
      ∑ β : Fin D, Xt₁ (p, β) r * Xt₂ (β, q) l) =
      (fun ((p, q) : Fin d × Fin d) ((r, l) : Fin r[U] × Fin ℓ[U]) ↦
        ∑ β : Fin D, X₁ (p, β) r * X₂ (β, q) l) * (K₁ ⊗ₖ K₂) := by
  classical
  subst Xt₁ Xt₂
  ext ⟨p, q⟩ ⟨r, l⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ β _
  ring

namespace TwoSiteStandardFormData

variable {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
  {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- For an explicitly given canonical ambient presentation, the actual
supplied standard form proves simplicity by its cut ranks. Canonicality
itself remains an input. Source: CPSV17, `ThmFund1` and `StandardForm`,
lines 563–622. -/
theorem isMPUSimple (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W) :
    IsMPUSimple W := by
  have hcard : ℓ * r = d * d := S.left_mul_right
  apply (hW.isMPUSimple_tfae.out 1 2).mpr
  rw [S.sourceRanks_eq.1, S.sourceRanks_eq.2]
  calc
    (d * r) * (ℓ * d) = (ℓ * r) * (d * d) := by ring
    _ = (d * d) * (d * d) := by rw [hcard]

/-- The literal four-spin gates of an arbitrary supplied standard form are
unitary-gauge related to any actual normalized source factors of the same
ambient tensor whose unshifted gate is unitary. Reciprocal positive scalars
cancel in both contractions. Source: CPSV17, `eq:block-twosites`, lines
1237–1252, and FBC25, `lem:deco`, lines 1052–1066. -/
theorem exists_fourSpin_source_gate_gauges
    (S : TwoSiteStandardFormData W u v)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (T : SourceFactors W ρ)
    (huT : (SourceFactors.sourceU W T).IsUnitaryBetween) :
    let eR := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.1.symm)
    let eL := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.2.symm)
    let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
      (finProdFinEquiv (m := d) (n := d))
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[W]) ℂ) (y : Matrix.unitaryGroup (Fin r[W]) ℂ),
      SourceFactors.sourceU W T =
        ((x : Matrix _ _ ℂ) ⊗ₖ (y : Matrix _ _ ℂ)) *
          Matrix.reindex (Equiv.prodCongr eL eR) p
            (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)) ∧
      SourceFactors.sourceV W T =
        Matrix.reindex p (Equiv.prodCongr eR eL)
            (staircaseMiddle (A := Fin d) (E := Fin d) v) *
          (star (y : Matrix _ _ ℂ) ⊗ₖ star (x : Matrix _ _ ℂ)) := by
  classical
  let eR := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.1.symm)
  let eL := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.2.symm)
  let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
    (finProdFinEquiv (m := d) (n := d))
  let X₁ := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eR S.cutX₁
  let Y₁ := Matrix.reindexLinearEquiv ℂ ℂ eR (Equiv.refl _) S.cutY₁
  let X₂ := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eL S.cutX₂
  let Y₂ := Matrix.reindexLinearEquiv ℂ ℂ eL (Equiv.refl _) S.cutY₂
  let C : Matrix (Fin ℓ[W] × Fin r[W]) (Fin (d * d) × Fin (d * d)) ℂ :=
    fun lr ij ↦ ∑ β : Fin D, Y₂ lr.1 (ij.1, β) * Y₁ lr.2 (β, ij.2)
  let B : Matrix (Fin (d * d) × Fin (d * d)) (Fin r[W] × Fin ℓ[W]) ℂ :=
    fun ij rl ↦ ∑ β : Fin D, X₁ (ij.1, β) rl.1 * X₂ (β, ij.2) rl.2
  have hC : C = Matrix.reindex (Equiv.prodCongr eL eR) p
      (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)) := by
    ext ⟨l, r⟩ ⟨i, j⟩
    change (∑ β : Fin D,
      S.cutY₂ (eL.symm l) (i, β) * S.cutY₁ (eR.symm r) (β, j)) =
      (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u))
        (eL.symm l, eR.symm r) (finProdFinEquiv.symm i, finProdFinEquiv.symm j)
    have h := congrArg (fun M ↦ M (eL.symm l, eR.symm r)
      (finProdFinEquiv.symm i, finProdFinEquiv.symm j))
      S.cutY₂_cutY₁_eq_staircaseMiddle_mul_kronecker
    simpa only [Equiv.apply_symm_apply] using h
  have hB : B = Matrix.reindex p (Equiv.prodCongr eR eL)
      (staircaseMiddle (A := Fin d) (E := Fin d) v) := by
    ext ⟨i, j⟩ ⟨r, l⟩
    change (∑ β : Fin D,
      S.cutX₁ (i, β) (eR.symm r) * S.cutX₂ (β, j) (eL.symm l)) =
      (staircaseMiddle (A := Fin d) (E := Fin d) v)
        (finProdFinEquiv.symm i, finProdFinEquiv.symm j) (eR.symm r, eL.symm l)
    have h := congrArg (fun M ↦ M (finProdFinEquiv.symm i, finProdFinEquiv.symm j)
      (eR.symm r, eL.symm l)) S.cutX₁_cutX₂_eq_staircaseMiddle
    simpa only [Equiv.apply_symm_apply] using h
  have huC : C.IsUnitaryBetween := by
    rw [hC]
    exact S.fourSpinGate_isUnitaryBetween.reindex _ (Equiv.prodCongr eL eR) p
  have hfac₁ : X₁ * Y₁ = sourceCutM₁ W := by
    dsimp only [X₁, Y₁]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl]
    exact S.sourceCutM₁_eq_cutX₁_mul_cutY₁.symm
  have hfac₂ : X₂ * Y₂ = sourceCutM₂ W := by
    dsimp only [X₂, Y₂]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl]
    exact S.sourceCutM₂_eq_cutX₂_mul_cutY₂.symm
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂⟩ := S.exists_cutY_right_inverses
  let R₁ := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eR Z₁
  let R₂ := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eL Z₂
  have hright₁ : Y₁ * R₁ = 1 := by
    dsimp only [Y₁, R₁]
    rw [Matrix.reindexLinearEquiv_mul, hZ₁, Matrix.reindexLinearEquiv_one]
  have hright₂ : Y₂ * R₂ = 1 := by
    dsimp only [Y₂, R₂]
    rw [Matrix.reindexLinearEquiv_mul, hZ₂, Matrix.reindexLinearEquiv_one]
  obtain ⟨δ, _, W₁, W₂, hXt₁, hYt₁, hXt₂, hYt₂, hδ⟩ :=
    exists_reciprocal_unitary_source_gauges
      hfac₁ T.sourceCutM₁_eq.symm hfac₂ T.sourceCutM₂_eq.symm
      T.X₁_weighted_isometry hright₁ T.X₂_isometry hright₂ huC huT
  have hY₁ : T.Y₁ = ((δ : ℂ) • star (W₁ : Matrix _ _ ℂ)) * Y₁ := by
    rw [Matrix.smul_mul]
    exact hYt₁
  have hY₂ : T.Y₂ = ((δ : ℂ)⁻¹ • star (W₂ : Matrix _ _ ℂ)) * Y₂ := by
    rw [Matrix.smul_mul]
    exact hYt₂
  have hU := sourceU_contraction_transport hY₁ hY₂
  change SourceFactors.sourceU W T =
    (((δ : ℂ)⁻¹ • star (W₂ : Matrix _ _ ℂ)) ⊗ₖ
      ((δ : ℂ) • star (W₁ : Matrix _ _ ℂ))) * C at hU
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, hδ, one_smul, hC] at hU
  have hX₁ : T.X₁ = X₁ * ((δ : ℂ)⁻¹ • (W₁ : Matrix _ _ ℂ)) := by
    rw [Matrix.mul_smul]
    exact hXt₁
  have hX₂ : T.X₂ = X₂ * ((δ : ℂ) • (W₂ : Matrix _ _ ℂ)) := by
    rw [Matrix.mul_smul]
    exact hXt₂
  have hV := sourceV_contraction_transport hX₁ hX₂
  change SourceFactors.sourceV W T = B *
    (((δ : ℂ)⁻¹ • (W₁ : Matrix _ _ ℂ)) ⊗ₖ ((δ : ℂ) • (W₂ : Matrix _ _ ℂ))) at hV
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, hδ, one_smul, hB] at hV
  refine ⟨star W₂, star W₁, ?_, ?_⟩
  · simpa only [Unitary.coe_star] using hU
  · simpa only [Unitary.coe_star, star_star] using hV

/-- For any supplied standard form in an explicitly canonical ambient
presentation, the actual selected source gates have the displayed four-spin
unitary comparison. The normalized factors and their gate unitarity are
constructed internally. Source: CPSV17, `eq:block-twosites` and
`FundamentalMPU`, lines 624–648 and 1237–1252. -/
theorem exists_fourSpin_selected_source_gate_gauges
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W) :
    let T := sourceFactors W hW.ρ hW.ρ_posDef
    let eR := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.1.symm)
    let eL := finProdFinEquiv.trans (finCongr S.sourceRanks_eq.2.symm)
    let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
      (finProdFinEquiv (m := d) (n := d))
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[W]) ℂ) (y : Matrix.unitaryGroup (Fin r[W]) ℂ),
      SourceFactors.sourceU W T =
        ((x : Matrix _ _ ℂ) ⊗ₖ (y : Matrix _ _ ℂ)) *
          Matrix.reindex (Equiv.prodCongr eL eR) p
            (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)) ∧
      SourceFactors.sourceV W T =
        Matrix.reindex p (Equiv.prodCongr eR eL)
            (staircaseMiddle (A := Fin d) (E := Fin d) v) *
          (star (y : Matrix _ _ ℂ) ⊗ₖ star (x : Matrix _ _ ℂ)) := by
  let T := sourceFactors W hW.ρ hW.ρ_posDef
  exact S.exists_fourSpin_source_gate_gauges T
    (hW.sourceFactors_sourceU_isUnitaryBetween (S.isMPUSimple hW) T)

/-- The selected normalized source gates and the literal four-spin gates
of a supplied square standard form in common physical-pair coordinates.
Source: CPSV17, `eq:block-twosites`, lines 1237–1252, and FBC25,
`lem:deco`, lines 1052–1066. -/
theorem exists_fourSpin_selected_source_gate_gauges_of_square_ranks
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W) :
    let T := sourceFactors W hW.ρ hW.ρ_posDef
    let L := finCongr S.sourceRanks_eq.2
    let R := finCongr S.sourceRanks_eq.1
    let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
      (finProdFinEquiv (m := d) (n := d))
    ∃ X Y : Matrix.unitaryGroup (Fin (d * d)) ℂ,
      Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU W T) =
        ((X : Matrix _ _ ℂ) ⊗ₖ (Y : Matrix _ _ ℂ)) * Matrix.reindex p p
          (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) ∧
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV W T) =
        Matrix.reindex p p (staircaseMiddle (A := Fin d) (E := Fin d) v) *
          ((Y : Matrix _ _ ℂ)ᴴ ⊗ₖ (X : Matrix _ _ ℂ)ᴴ) := by
  classical
  let T := sourceFactors W hW.ρ hW.ρ_posDef
  have hr : r[W] = d * d := S.sourceRanks_eq.1
  have hl : ℓ[W] = d * d := S.sourceRanks_eq.2
  obtain ⟨X, Y, hu, hv⟩ := S.exists_fourSpin_selected_source_gate_gauges hW
  let L := finCongr hl
  let R := finCongr hr
  let X' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex L L X, Matrix.reindex_mem_unitaryGroup _ _ X.property⟩
  let Y' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex R R Y, Matrix.reindex_mem_unitaryGroup _ _ Y.property⟩
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let A := staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)
  let B := staircaseMiddle (A := Fin d) (E := Fin d) v
  have hu' : Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _)
      (SourceFactors.sourceU W T) =
      ((X' : Matrix _ _ ℂ) ⊗ₖ (Y' : Matrix _ _ ℂ)) * Matrix.reindex p p A := by
    have h := congrArg (Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _)) hu
    rw [Matrix.reindex_kronecker_mul] at h
    have hA : Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _)
        (Matrix.reindex
          (Equiv.prodCongr
            (finProdFinEquiv.trans (finCongr S.sourceRanks_eq.2.symm))
            (finProdFinEquiv.trans (finCongr S.sourceRanks_eq.1.symm))) p A) =
        Matrix.reindex p p A := by
      ext ⟨i, j⟩ ⟨k, l⟩
      rfl
    rw [hA] at h
    exact h
  have hv' : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L)
      (SourceFactors.sourceV W T) = Matrix.reindex p p B *
      ((Y' : Matrix _ _ ℂ)ᴴ ⊗ₖ (X' : Matrix _ _ ℂ)ᴴ) := by
    have h := congrArg (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L)) hv
    rw [Matrix.reindex_mul_kronecker] at h
    have hB : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L)
        (Matrix.reindex p
          (Equiv.prodCongr
            (finProdFinEquiv.trans (finCongr S.sourceRanks_eq.1.symm))
            (finProdFinEquiv.trans (finCongr S.sourceRanks_eq.2.symm))) B) =
        Matrix.reindex p p B := by
      ext ⟨i, j⟩ ⟨k, l⟩
      rfl
    rw [hB] at h
    simpa only [X', Y', Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex] using h
  exact ⟨X', Y', hu', hv'⟩

/-- Even-family adjoint symmetry forces the intermediate dimensions of any
supplied standard form to equal its original physical dimension. The
ambient canonical presentation remains explicit. Source: CPSV17,
`PropChiral`, zero-index observation and proof, lines 1201–1252. -/
theorem intermediateRanks_eq_phys_of_even_mpo_eq_adjoint
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    r = d ∧ ℓ = d := by
  have hEq : ∀ N : ℕ, 1 < N → Even N →
      mpo W N = mpo (physicalAdjointTensor W) N := by
    intro N hN heven
    rw [mpo_physicalAdjointTensor_eq_conjTranspose]
    exact hTR N hN heven
  have hsame := hW.source_ranks_eq_of_mpo_eq_even hW.physicalAdjointTensor hEq
  have hbalanced : ℓ[W] = r[W] := by
    simpa only [rightRank_physicalAdjointTensor] using hsame.1
  have hℓr : ℓ = r := by
    apply mul_right_cancel₀ S.phys_pos.ne'
    calc
      ℓ * d = ℓ[W] := S.sourceRanks_eq.2.symm
      _ = r[W] := hbalanced
      _ = d * r := S.sourceRanks_eq.1
      _ = r * d := Nat.mul_comm _ _
  have hprod : ℓ * r = d * d := S.left_mul_right
  rw [← hℓr] at hprod
  have hℓ : ℓ = d := (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hprod
  exact ⟨hℓr.symm.trans hℓ, hℓ⟩

end TwoSiteStandardFormData

end MPOTensor
