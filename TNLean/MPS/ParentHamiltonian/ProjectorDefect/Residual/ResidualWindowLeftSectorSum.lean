/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowCoordinates
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockProjectorSum
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap

/-!
# Sector projection sums for the aligned left residual window

The left window on two adjacent blocked intervals of lengths \(K,M\)
with an original tail of length \(r\) is the ordinary boundary map
\(\Gamma_B(K+M)\) applied independently at each tail configuration,
followed by a physical coordinate permutation. Orthogonal projection
onto its range is consequently the transported fiberwise ground projection.

Adding these spectator coordinates does not increase the error between
the finite sum of sector projections and their joint projection. For
primitive inequivalent sectors with faithful invariant matrices, this
error therefore tends to zero as \(M\) diverges, uniformly in every
\(K,r\geq0\). All coordinate identities and finite comparisons include
zero lengths and empty sector families. This is the aligned left-window
part of Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (i),
lines 2442--2531; the remaining within-sector projector defect is separate.
-/

open MPTensor

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder InnerProductSpace
open Kraus (blockPhysDim)
namespace MPSTensor
variable {d E L : ℕ}
/-- Split the concatenated blocked interval, keeping the original tail as the spectator
coordinate. The coordinate bijection includes all zero lengths. -/
noncomputable def residualWindowLeftConfigEquiv (d L K M r : ℕ) :
    Cfg (blockPhysDim d L) (K + M) × Cfg d r ≃
      Cfg (blockPhysDim d L) K × (Cfg (blockPhysDim d L) M × Cfg d r) :=
  (Equiv.prodCongr (Fin.appendEquiv K M).symm (Equiv.refl (Cfg d r))).trans
    (Equiv.prodAssoc _ _ _)

/-- The aligned left window is a physical reindexing of the ordinary full-prefix boundary map
applied independently to each tail configuration. -/
theorem residualWindowLeftMapES_eq_fiberwise
    (B : MPSTensor (blockPhysDim d L) E) (K M r : ℕ) :
    residualWindowLeftMapES B K M r =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualWindowLeftConfigEquiv d L K M r)).toContinuousLinearMap.comp
          ((ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
            (groundSpaceMapES B (K + M))).comp
            (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (Equiv.prodComm (Cfg d r) (Fin E × Fin E))).toContinuousLinearMap) := by
  ext x ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v)) *
    boundaryFamilyEquiv (D := E) (Cfg d r) x τ) = _
  change Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v)) *
    boundaryFamilyEquiv (D := E) (Cfg d r) x τ) =
    groundSpaceMap B (K + M) (boundaryFamilyEquiv (D := E) (Cfg d r) x τ) (Fin.append u v)
  rw [groundSpaceMap_apply, List.ofFn_fin_append, Kraus.evalWord_append]

/-- The aligned left-window sector projection-sum error is at most the ordinary sector
projection-sum error on the combined blocked prefix. The estimate is independent of the
original-tail length. -/
theorem norm_residualWindowLeft_sector_projection_sum_sub_iSup_le
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (B : (j : ι) → MPSTensor (blockPhysDim d L) (dim j)) (K M r : ℕ) :
    ‖(∑ j, (residualWindowLeftMapES (B j) K M r).range.starProjection) -
      (⨆ j, (residualWindowLeftMapES (B j) K M r).range).starProjection‖ ≤
      ‖(∑ j, (groundSpaceES (B j) (K + M)).starProjection) -
        (⨆ j, groundSpaceES (B j) (K + M)).starProjection‖ := by
  simp only [residualWindowLeftMapES_eq_fiberwise]
  have hFiber := ContinuousLinearMap.norm_sum_rightFiberwiseMap_range_starProjection_sub_iSup_le
    (S := Cfg d r) (fun j : ι => groundSpaceMapES (B j) (K + M))
  have hR (j : ι) : ((ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
      (groundSpaceMapES (B j) (K + M))).comp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodComm (Cfg d r) (Fin (dim j) × Fin (dim j)))).toContinuousLinearMap).range =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (groundSpaceMapES (B j) (K + M))).range :=
    LinearMap.range_comp_of_range_eq_top
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (groundSpaceMapES (B j) (K + M))).toLinearMap
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodComm (Cfg d r) (Fin (dim j) × Fin (dim j)))).toLinearEquiv.range
  refine (norm_sum_isometric_range_projection_sub_iSup_le
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (residualWindowLeftConfigEquiv d L K M r)) _).trans ?_
  simp only [hR]
  simpa only [range_groundSpaceMapES] using hFiber

/-- For primitive inequivalent sectors with faithful invariant matrices, the aligned left-window
projection-sum error is uniformly small for all outer-prefix and original-tail lengths once
the middle interval is sufficiently long. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (i), lines 2442--2531. -/
theorem eventually_norm_residualWindowLeft_sector_projection_sum_sub_iSup_le
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (B : (j : ι) → MPSTensor (blockPhysDim d L) (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in Filter.atTop, ∀ K r : ℕ,
      ‖(∑ j, (residualWindowLeftMapES (B j) K M r).range.starProjection) -
        (⨆ j, (residualWindowLeftMapES (B j) K M r).range).starProjection‖ ≤ ε := by
  have hPrefix : Filter.Tendsto (fun N =>
      ‖(∑ j, (groundSpaceES (B j) N).starProjection) -
        (⨆ j, groundSpaceES (B j) N).starProjection‖) Filter.atTop (nhds 0) := by
    apply Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero
    intro η hη
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun hij =>
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hη] with N hN
    exact hN
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hPrefix).2 ε hε)
  filter_upwards [Filter.eventually_ge_atTop N₀] with M hM
  intro K r
  exact (norm_residualWindowLeft_sector_projection_sum_sub_iSup_le B K M r).trans
    (hN₀ (K + M) (hM.trans (Nat.le_add_left M K))).le

/-- The aligned left-window projection-sum error tends to zero along every diverging middle
interval, with arbitrary outer-prefix and original-tail lengths. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (i), lines 2442--2531. -/
theorem tendsto_norm_residualWindowLeft_sector_projection_sum_sub_iSup_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (B : (j : ι) → MPSTensor (blockPhysDim d L) (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ}
    (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(∑ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range.starProjection) -
        (⨆ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range).starProjection‖)
      f (nhds 0) := by
  apply tendsto_order.2
  constructor
  · exact fun a ha => Filter.Eventually.of_forall fun _ => ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [hM.eventually
      (eventually_norm_residualWindowLeft_sector_projection_sum_sub_iSup_le
        B ρ hP hρ hDistinct (half_pos hε))] with n hn
    exact (hn (K n) (r n)).trans_lt (half_lt_self hε)
end MPSTensor



