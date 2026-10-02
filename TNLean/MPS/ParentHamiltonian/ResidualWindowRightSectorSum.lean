/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EuclideanFiberwiseProjection
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryOverlap
import TNLean.MPS.ParentHamiltonian.ResidualWindowCoordinates

/-!
# Sector projections for the right residual window

The right window is a finite family of residual boundary maps, indexed by
the preceding blocked configurations. Physical reindexing preserves the
relative angles between sectors, and finite direct sums preserve the
projection-sum error bound. Thus inequivalent primitive sectors approximate
the joint right-window projection as their common blocked interval grows,
uniformly over arbitrary prefix and original-tail lengths.

The statements concern the right window and its sector sum. They assert
neither the product of the two window projections nor a finite-chain gap.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i),
lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D E L : ℕ}
/-- Decode the blocked common interval and append its original tail.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451. -/
noncomputable def residualBoundaryConfigEquiv (d L M r : ℕ) :
    Cfg (blockPhysDim d L) M × Cfg d r ≃ Cfg d (M * L + r) :=
  (Equiv.prodCongr (blockedConfigEquiv d M L) (Equiv.refl (Cfg d r))).trans
    (Fin.appendEquiv (M * L) r)

/-- The right window is a finite direct sum of the residual boundary map,
after decoding each common-interval configuration. This includes zero lengths.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, Lemma `commutation` (i), lines 2442--2531. -/
theorem residualWindowRightMapES_eq_fiberwise
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    residualWindowRightMapES A B V K M r =
      EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualBoundaryConfigEquiv d L M r).symm).toContinuousLinearMap.comp
            (blockedResidualBoundaryMapES A L B V M r)) := by
  ext x ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
    Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u x) =
    blockedResidualBoundaryMap A L B V M r
      ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm
        (EuclideanSpace.fiberₗ u x))
      (Fin.append (blockedConfigEquiv d M L v) τ)
  simp [blockedResidualBoundaryMap, Function.comp_def]
  rfl

/-- Residual-sector projection-sum decay is preserved by a varying physical
configuration isometry. The residual tail can vary arbitrarily along the filter.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i),
lines 2442--2531. -/
theorem tendsto_norm_isometric_residual_sector_projection_sum_sub_iSup_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    {κ : Type*} {f : Filter κ} {M r : κ → ℕ}
    {J : κ → Type} [∀ n, Fintype (J n)]
    (U : ∀ n, EuclideanSpace ℂ (Cfg d (M n * L + r n)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (J n))
    (hM : Filter.Tendsto M f Filter.atTop) :
    let T := fun n j => (U n).toContinuousLinearMap.comp
      (blockedResidualBoundaryMapES A L (B j) (V j) (M n) (r n))
    Filter.Tendsto (fun n =>
      ‖(∑ j, (T n j).range.starProjection) -
        (⨆ j, (T n j).range).starProjection‖) f (nhds 0) := by
  dsimp only
  apply Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero
  intro ε hε
  filter_upwards [hM.eventually (Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun hij =>
      (hP i).eventually_norm_inner_blockedResidualBoundaryMapES_le_of_inequivalent
        A A (V i) (V j) (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε)] with n hn
  intro i j hij x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  change ‖inner ℂ (U n (blockedResidualBoundaryMapES A L (B i) (V i) (M n) (r n) a))
      (U n (blockedResidualBoundaryMapES A L (B j) (V j) (M n) (r n) b))‖ ≤
    ε * ‖U n (blockedResidualBoundaryMapES A L (B i) (V i) (M n) (r n) a)‖ *
      ‖U n (blockedResidualBoundaryMapES A L (B j) (V j) (M n) (r n) b)‖
  rw [(U n).inner_map_map, (U n).norm_map, (U n).norm_map]
  convert hn i j hij (r n) _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ using 1

/-- The projection-sum error for the right window tends to zero as the common
blocked interval grows. Neither the preceding prefix nor the original tail is
bounded or required to grow. No normalization or intertwiner is supplied for
the original tensor or the sector embeddings.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i),
lines 2442--2531, with the residual coordinates of DCCSP17,
Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem tendsto_norm_residualWindowRight_sector_projection_sum_sub_iSup_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ} (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(∑ j, (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range.starProjection) -
        (⨆ j, (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection‖)
      f (nhds 0) := by
  let U := fun n => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residualBoundaryConfigEquiv d L (M n) (r n)).symm
  have hBase := tendsto_norm_isometric_residual_sector_projection_sum_sub_iSup_zero
    A B V ρ hP hρ hDistinct U hM
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hBase
  simp_rw [residualWindowRightMapES_eq_fiberwise]
  exact EuclideanSpace.norm_sum_fiberwiseMap_range_starProjection_sub_iSup_le
    (Cfg (blockPhysDim d L) (K n))
    (fun j => (U n).toContinuousLinearMap.comp
      (blockedResidualBoundaryMapES A L (B j) (V j) (M n) (r n)))

end MPSTensor
