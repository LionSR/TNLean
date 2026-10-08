/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowRightSectorSum
import TNLean.MPS.ParentHamiltonian.ResidualWindowRightGroundSpace

/-!
# Sector projections for the full residual window

The full three-window boundary map is the residual boundary map at prefix
length \(K+M\), transported to the physical triple configuration space.
Since \(M\) tending to infinity forces \(K+M\) to tend to infinity, the
residual-sector projection sum approximates the joint full-window projection
while both the preceding prefix \(K\) and the original tail \(r\) vary arbitrarily.

A virtual resolution and its blocked cointertwining identify the joint range
exactly with the original ground space in these coordinates. This identity
requires neither primitivity nor injectivity. The projection-sum limit uses
inequivalent primitive sectors but imposes no normalization or intertwining
on the original tensor or the sector embeddings.

The statements concern a single full-window projection sum, not the product
of the two overlapping window projections or a finite-chain gap.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (i),
lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D L : ℕ}

/-- The full-window sector projection-sum error tends to zero as the common
blocked interval grows, while the prefix and tail may vary arbitrarily.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (i),
lines 2442--2531, with the residual blocking coordinates of DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem tendsto_norm_residualWindow_sector_projection_sum_sub_iSup_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ} (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(∑ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range.starProjection) -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection‖)
      f (nhds 0) := by
  have hKM : Filter.Tendsto (fun n => K n + M n) f Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_add_left (M n) (K n)) hM
  let U := fun n => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residualWindowConfigEquiv d L (K n) (M n) (r n)).symm
  have hBase := tendsto_norm_isometric_residual_sector_projection_sum_sub_iSup_zero
    A B V ρ hP hρ hDistinct U hKM
  simpa only [residualWindowMapES_eq_reindex_blockedResidualBoundaryMapES, U] using hBase

/-- A virtual resolution and blocked cointertwining identify the joint
full-window range with the original ground space after physical reindexing.
This includes all zero lengths and requires no primitivity or injectivity.
Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
theorem iSup_range_residualWindowMapES_eq_reindex_groundSpaceES
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) (K M r : ℕ) :
    (⨆ j, (residualWindowMapES A (B j) (V j) K M r).range) =
      (groundSpaceES A ((K + M) * L + r)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualWindowConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  simp only [residualWindowMapES_eq_reindex_blockedResidualBoundaryMapES,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp]
  rw [← Submodule.map_iSup,
    ← groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES A B V hSum hInt (K + M) r]

/-- The full residual-sector joint range is the original ground space in
physical cover coordinates of length \(KL+ML+r\).
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (i), lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451. Only the virtual resolution
and blocked cointertwining are required. -/
theorem iSup_range_residualWindowMapES_eq_reindex_groundSpaceES_cover
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) (K M r : ℕ) :
    (⨆ j, (residualWindowMapES A (B j) (V j) K M r).range) =
      (groundSpaceES A (K * L + M * L + r)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualCoverConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  have hCast {n n' : ℕ} (h : n = n')
      (e : Cfg (blockPhysDim d L) K × (Cfg (blockPhysDim d L) M × Cfg d r) ≃ Cfg d n) :
      (groundSpaceES A n).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearEquiv.toLinearMap =
      (groundSpaceES A n').map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (e.trans (Equiv.arrowCongr (finCongr h)
            (Equiv.refl (Fin d)))).symm).toLinearEquiv.toLinearMap := by
    subst n'
    simp only [finCongr_refl, Equiv.arrowCongr_refl, Equiv.trans_refl]
  exact (iSup_range_residualWindowMapES_eq_reindex_groundSpaceES A B V hSum hInt K M r).trans
    (hCast (by rw [Nat.add_mul]) (residualWindowConfigEquiv d L K M r))


end MPSTensor

