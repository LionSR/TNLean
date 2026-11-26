/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockSubspaceOverlap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGram
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryOverlap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGramInverse
import TNLean.MPS.CanonicalForm.BNT.Separation
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GroundSpaceIndependence
import QICLean.Analysis.Projection.SupportedRangeProjector
import Mathlib.LinearAlgebra.Matrix.Bilinear
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PrimitiveSectorRepresentatives
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockedGroundSpaceTransport

/-!
# Bounded lifts from finitely many subspaces

Suppose a linear map has bounded preimages on each member of a finite family
of subspaces. A lower Gram estimate controls the components of a vector in
their joint space, and hence gives bounded preimages on that joint space.
The bound is independent of the dimensions of the subspaces.

This is a finite-sum consequence of the lower Gram estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma overlapestimate, lines 2109--2175.

## Independence of periodic tensor boundary spaces

For a normalized periodic tensor, primitive cyclic sectors supply bounded
virtual preimages of every original-chain boundary vector. The supported
residual Gram inverses are uniform over all tails, and a finite lower Gram
estimate combines the sectors. Thus the preimage bound holds at every
sufficiently large original length, rather than only at blocked lengths.

For two inequivalent periodic tensors, the original mixed-transfer operator
has spectral radius below one. Its powers therefore tend to zero; the
preimage bounds convert this into uniform decay of the boundary-space angle.
A finite family consequently has independent boundary spaces eventually.

This follows the boundary normalization and mixed-transfer argument in
Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint, equations C1C2 and limP12,
using the cyclic decomposition of arXiv:1708.00029, Lemma bdcf. The conclusions
concern normalized periodic generating tensors; no purity classification is
asserted here.

It also contains the following results.

* `MPSTensor.groundSpaceES_le_of_isometric_cointertwiner`,
  `MPSTensor.IsPeriodic.not_gaugePhaseEquiv_of_primitive_corners`: separation of corners belonging
  to distinct periodic tensors.
-/

section PeriodicGroundSpaceIndependence

section

open scoped BigOperators InnerProductSpace
namespace Submodule

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

/-- Bounded preimages on finitely many subspaces and a lower Gram estimate
give bounded preimages on their joint space. The factor two is a convenient
relaxation of the lower Gram bound. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma overlapestimate, lines 2109--2175. -/
theorem exists_norm_le_preimage_of_mem_iSup_of_lower_gram
    (T : E →ₗ[ℂ] F) (W : ι → Submodule ℂ F)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hLower : ∀ v : ∀ i, W i,
      (1 / 2 : ℝ) * (∑ i, ‖(v i : F)‖ ^ 2) ≤ ‖∑ i, (v i : F)‖ ^ 2)
    (hLift : ∀ i, ∀ x ∈ W i, ∃ u, T u = x ∧ ‖u‖ ≤ C i * ‖x‖)
    {x : F} (hx : x ∈ ⨆ i, W i) :
    ∃ u, T u = x ∧ ‖u‖ ≤ 2 * (∑ i, C i) * ‖x‖ := by
  classical
  obtain ⟨v, hv⟩ := exists_sum_eq_of_mem_iSup W hx
  have hGram := hLower v
  rw [hv] at hGram
  have hSumBound : ∑ i, ‖(v i : F)‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    linarith
  have hvNorm (i : ι) : ‖(v i : F)‖ ≤ 2 * ‖x‖ := by
    have hi : ‖(v i : F)‖ ^ 2 ≤ ∑ j, ‖(v j : F)‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖(v j : F)‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i : F), norm_nonneg x]
  choose u hu hNorm using fun i => hLift i (v i) (v i).property
  refine ⟨∑ i, u i, ?_, ?_⟩
  · simpa only [map_sum, hu] using hv
  · calc
      ‖∑ i, u i‖ ≤ ∑ i, ‖u i‖ := norm_sum_le _ _
      _ ≤ ∑ i, C i * (2 * ‖x‖) := Finset.sum_le_sum fun i _ =>
        (hNorm i).trans (mul_le_mul_of_nonneg_left (hvNorm i) (hC i))
      _ = 2 * (∑ i, C i) * ‖x‖ := by rw [← Finset.sum_mul]; ring

end Submodule

end

section

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter
open Kraus (blockPhysDim blockTensor)
namespace MPSTensor
variable {d D E L : ℕ}

section
open scoped Matrix.Norms.Frobenius

/-- Embed a rectangular sector boundary in the original bond algebra by
\(Y\mapsto YV^\dagger\). This preserves the literal order of the boundary trace.
Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag. -/
noncomputable def residualBoundaryEmbeddingES (V : Matrix (Fin D) (Fin E) ℂ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  LinearMap.toContinuousLinearMap <|
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv.toLinearMap.comp
      ((mulRightLinearMap (Fin D) ℂ Vᴴ).comp
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm.toLinearEquiv.toLinearMap)

/-- The rectangular boundary embedding acts by right multiplication by the
adjoint sector isometry. Source: arXiv:1708.00029, equation Aoffdiag. -/
@[simp] theorem residualBoundaryEmbeddingES_apply
    (V : Matrix (Fin D) (Fin E) ℂ) (Y : Matrix (Fin D) (Fin E) ℂ) :
    residualBoundaryEmbeddingES V (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (Y * Vᴴ) := by
  change Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
    ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) * Vᴴ) = _
  rw [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm_apply_apply]

/-- The correlated residual map is an original-chain boundary map at the
boundary \(YV^\dagger\); neither the original site order nor the boundary trace is
reversed. Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag. -/
theorem blockedResidualBoundaryMapES_eq_groundSpaceMapES_comp
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, Vᴴ * blockTensor A L i = B i * Vᴴ) (N r : ℕ) :
    blockedResidualBoundaryMapES A L B V N r =
      (groundSpaceMapES A (N * L + r)).comp (residualBoundaryEmbeddingES V) := by
  ext1 x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  rw [ContinuousLinearMap.comp_apply, residualBoundaryEmbeddingES_apply,
    blockedResidualBoundaryMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply,
    blockedResidualBoundaryMap_eq_groundSpaceMap_mul_conjTranspose A B V hInt]
end

private theorem exists_boundary_lift_of_sector_lower_bound
    {ι : Type*} [Fintype ι] {U F : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {W : ι → Type*} [∀ j, NormedAddCommGroup (W j)]
    [∀ j, InnerProductSpace ℂ (W j)] [∀ j, CompleteSpace (W j)]
    (T : U →L[ℂ] F) (S : ∀ j, W j →L[ℂ] F) (J : ∀ j, W j →L[ℂ] U)
    (H : ∀ j, W j →L[ℂ] W j) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hFactor : ∀ j, T.comp (J j) = S j)
    (hProj : ∀ j, (S j).comp ((H j).comp (S j).adjoint) = (S j).range.starProjection)
    (hBound : ∀ j, ‖J j‖ * ‖H j‖ * ‖S j‖ ≤ c j)
    (hLower : ∀ v : ∀ j, (S j).range,
      (1 / 2 : ℝ) * (∑ j, ‖(v j : F)‖ ^ 2) ≤ ‖∑ j, (v j : F)‖ ^ 2)
    {x : F} (hx : x ∈ ⨆ j, (S j).range) :
    ∃ u : U, T u = x ∧ ‖u‖ ≤ (2 * ∑ j, c j) * ‖x‖ := by
  apply Submodule.exists_norm_le_preimage_of_mem_iSup_of_lower_gram
    T.toLinearMap (fun j => (S j).range) c hc hLower ?_ hx
  intro j y hy
  let w := H j ((S j).adjoint y)
  have hw : S j w = y := by
    simpa only [ContinuousLinearMap.comp_apply, w,
      Submodule.starProjection_eq_self_iff.mpr hy] using
      congrArg (fun P : F →L[ℂ] F => P y) (hProj j)
  refine ⟨J j w, ?_, ?_⟩
  · change T (J j w) = y
    rw [← ContinuousLinearMap.comp_apply, hFactor]
    exact hw
  · calc
      _ ≤ ‖J j‖ * (‖H j‖ * (‖S j‖ * ‖y‖)) := by
        dsimp only [w]
        exact ((J j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (((H j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (by simpa only [ContinuousLinearMap.adjoint.norm_map] using
              (S j).adjoint.le_opNorm y) (norm_nonneg _))) (norm_nonneg _))
      _ = (‖J j‖ * ‖H j‖ * ‖S j‖) * ‖y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hBound j) (norm_nonneg _)

open scoped Matrix.Norms.L2Operator

private theorem exists_eventually_boundary_lift_of_residual_resolution
    [NeZero D] {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ)
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) = Q j r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, ∀ r,
      ∀ x ∈ groundSpaceES A (N * L + r), ∃ u,
        groundSpaceMapES A (N * L + r) u = x ∧ ‖u‖ ≤ C * ‖x‖ := by
  classical
  let c (j : ι) := ‖residualBoundaryEmbeddingES (V j)‖ *
    (2 * ‖Ring.inverse (rectangularRightGramMetric D (ρ j))‖) *
    (‖rectangularRightGramMetric D (ρ j)‖ + 2)
  have hc (j : ι) : 0 ≤ c j := by dsimp only [c]; positivity
  let C₀ : Matrix ι ι ℝ := fun i j => if i = j then 0 else 1
  let ε : ℝ := 1 / (2 * (‖C₀‖ + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hSmall : ‖ε • C₀‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    dsimp only [ε]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [norm_nonneg C₀]
  refine ⟨(2 * (∑ j, c j)) + 1, by positivity, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun j =>
    (hP j).eventually_residualBoundaryGramInverse_properties (hρ j) A (V j)
      (Q j) (hQ j) (hGram j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun hij =>
        (hP i).eventually_norm_inner_blockedResidualBoundaryMapES_le_of_inequivalent
          A A (V i) (V j) (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε] with N hI hO
  intro r x hx
  let S (j : ι) := blockedResidualBoundaryMapES A L (B j) (V j) N r
  let H (j : ι) := residualBoundaryGramInverse A (B j) (V j) (ρ j) (Q j r) N r
  have hLower (v : ∀ j, (S j).range) :
      (1 / 2 : ℝ) * (∑ j, ‖(v j : EuclideanSpace ℂ (Cfg d (N * L + r)))‖ ^ 2) ≤
        ‖∑ j, (v j : EuclideanSpace ℂ (Cfg d (N * L + r)))‖ ^ 2 := by
    have h := Submodule.norm_sum_sq_ge_of_overlapMatrix
      (fun j => (v j : EuclideanSpace ℂ (Cfg d (N * L + r)))) (ε • C₀)
      (fun i => by change ε * (if i = i then 0 else 1) = 0; simp)
      (fun i j hij => by
        change ‖⟪(v i : EuclideanSpace ℂ (Cfg d (N * L + r))),
          (v j : EuclideanSpace ℂ (Cfg d (N * L + r)))⟫_ℂ‖ ≤
          (ε * (if i = j then 0 else 1)) *
            ‖(v i : EuclideanSpace ℂ (Cfg d (N * L + r)))‖ *
            ‖(v j : EuclideanSpace ℂ (Cfg d (N * L + r)))‖
        simpa only [ite_eq_right hij, mul_one] using hO i j hij r _ (v i).property _ (v j).property)
    exact (mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - ‖ε • C₀‖)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans h
  have hProj (j : ι) : (S j).comp ((H j).comp (S j).adjoint) = (S j).range.starProjection := by
    apply ContinuousLinearMap.comp_supportedGramInverse_adjoint_eq_starProjection
      (S j) (H j) (rectangularRowProjection (dim j) (Q j r))
    · rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (rectangularRowProjection_isStarProjection (E := dim j) (hQ j r)).isSelfAdjoint.star_eq
    · exact (hI j r).2.2.1
    · exact (hI j r).2.2.2.1
  have hBound (j : ι) : ‖residualBoundaryEmbeddingES (V j)‖ * ‖H j‖ * ‖S j‖ ≤ c j :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hI j r).2.2.2.2.1 (norm_nonneg _))
      (hI j r).2.2.2.2.2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by positivity))
  have hx' : x ∈ ⨆ j, (S j).range := by
    simpa only [S,
      ← groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES A B V hSum hInt N r] using hx
  obtain ⟨u, hu, hnorm⟩ := exists_boundary_lift_of_sector_lower_bound
    (groundSpaceMapES A (N * L + r)) S (fun j => residualBoundaryEmbeddingES (V j)) H c hc
    (fun j => (blockedResidualBoundaryMapES_eq_groundSpaceMapES_comp
      A (B j) (V j) (hInt j) N r).symm)
    hProj hBound hLower hx'
  exact ⟨u, hu, hnorm.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))⟩

/-- Every sufficiently long original-chain boundary vector of a normalized
periodic tensor has a uniformly bounded virtual preimage. This holds at all
residue lengths, without injectivity of the full boundary map.
Source: the boundary normalization argument in Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma disjoint, equations C1C2 and limP12,
combined with arXiv:1708.00029, Lemma bdcf. -/
theorem IsPeriodic.exists_eventually_groundSpaceMapES_preimage_norm_le
    {m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ groundSpaceES A n, ∃ u, groundSpaceMapES A n u = x ∧ ‖u‖ ≤ C * ‖x‖ := by
  classical
  let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  let _ : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, hdim, B, P, V, ρ, hP, hρ, hDistinct, hProj, hSum,
    hShift, hIso, hV, hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let Q (j : Fin m) (r : ℕ) := P (j - r • (1 : Fin m))
  have hQ : ∀ j r, IsOrthogonalProjection (Q j r) :=
    fun j r => hProj (j - r • (1 : Fin m))
  have hGram (j : Fin m) (r : ℕ) :
      (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V j * (V j)ᴴ) *
        Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r := by
    simpa only [Q, hV] using
      sum_word_conjTranspose_inverseCyclic_projection_mul_word A P hA.leftCanonical hShift j r
  obtain ⟨C, hC, hLift⟩ := exists_eventually_boundary_lift_of_residual_resolution
    A B V ρ hP hρ hDistinct.forall_ne_transport
    (by simpa only [hV] using hSum) hCoInt Q hQ hGram
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hLift
  filter_upwards [Filter.eventually_ge_atTop (N₀ * m)] with n hn
  have hq : N₀ ≤ n / m := (Nat.le_div_iff_mul_le hA.period_pos).2 hn
  have heq : n / m * m + n % m = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n m
  rw [← heq]
  exact hN₀ (n / m) hq (n % m)

/-- Gauge-phase inequivalent normalized periodic tensors have uniformly
vanishing overlaps between their original local boundary spaces. Their
periods may differ. No inequivalence of blocked corners is assumed.
Source: the mixed-transfer and boundary normalization argument in
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma disjoint,
equations C1C2 and limP12. This is a statement about periodic generating
tensors and does not assert purity of their associated states. -/
theorem IsPeriodic.eventually_norm_inner_groundSpaceES_le_of_inequivalent
    {D₂ m m₂ : ℕ} {A : MPSTensor d D} {B : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hB : IsPeriodic m₂ B)
    (hDistinct : ∀ e : D₂ = D, ¬ GaugePhaseEquiv (e ▸ B) A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ groundSpaceES A n, ∀ y ∈ groundSpaceES B n,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  let _ : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let _ : NeZero D₂ := ⟨hB.bondDim_ne_zero⟩
  have hgap : Kraus.mixedMapSpectralRadius B A < 1 := by
    by_cases hD : D₂ = D
    · subst D₂
      exact Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP B A
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB.irreducible)
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible)
        hB.leftCanonical hA.leftCanonical
        (fun h => hDistinct rfl (gaugePhaseEquiv_of_krausGaugePhaseEquiv h))
    · exact Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP B A
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB.irreducible)
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible)
        hB.leftCanonical hA.leftCanonical hD
  obtain ⟨C, hC, hLiftA⟩ := hA.exists_eventually_groundSpaceMapES_preimage_norm_le
  obtain ⟨C₂, hC₂, hLiftB⟩ := hB.exists_eventually_groundSpaceMapES_preimage_norm_le
  have hDecay : Tendsto (fun n => C *
      ‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ * C₂)
      atTop (nhds 0) := by
    simpa only [norm_zero, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul
        (adjoint_groundSpaceMapES_comp_tendsto_zero_of_spectralRadius_lt_one A B hgap).norm).mul
        tendsto_const_nhds
  filter_upwards [hLiftA, hLiftB, (tendsto_order.1 hDecay).2 ε hε] with n hAn hBn hn
  intro x hx y hy
  obtain ⟨u, hu, hUnorm⟩ := hAn x hx
  obtain ⟨v, hv, hVnorm⟩ := hBn y hy
  rw [← hu, ← hv, ← ContinuousLinearMap.adjoint_inner_right]
  have h := (norm_inner_le_norm (𝕜 := ℂ) u
    (((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)) v)).trans
    (mul_le_mul_of_nonneg_left
      (((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)).le_opNorm v)
      (norm_nonneg u))
  have hbound : ‖u‖ *
      (‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ * ‖v‖) ≤
      (C * ‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ * C₂) *
        ‖x‖ * ‖y‖ := by
    calc
      _ ≤ (C * ‖x‖) *
          (‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ * (C₂ * ‖y‖)) :=
        mul_le_mul hUnorm (mul_le_mul_of_nonneg_left hVnorm (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hC.le (norm_nonneg _))
      _ = _ := by ring
  simpa only [ContinuousLinearMap.comp_apply, hu, hv] using
    h.trans (hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hn.le (norm_nonneg x)) (norm_nonneg y)))

/-- A finite family of pairwise gauge-phase inequivalent normalized periodic
tensors has independent original-chain boundary spaces at every sufficiently
large length. No common period or additional dimension hypothesis is needed.
Source: the mixed-transfer argument of Nachtergaele,
arXiv:cond-mat/9410110, Lemma disjoint, followed by the lower Gram estimate
of Lemma overlapestimate, lines 2109--2175. -/
theorem eventually_groundSpaceES_iSupIndep_of_isPeriodic
    {ι : Type*} [Finite ι] {dim : ι → ℕ}
    (A : ∀ j, MPSTensor d (dim j)) (m : ι → ℕ)
    (hA : ∀ j, IsPeriodic (m j) (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∀ᶠ n in atTop, iSupIndep (fun j => groundSpaceES (A j) n) := by
  apply Submodule.eventually_iSupIndep_of_pairwise_overlap
  intro ε hε
  filter_upwards [Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun hij =>
      (hA i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
        (hA j) (hDistinct i j hij) hε] with n hn
  exact fun i j hij => hn i j hij

end MPSTensor

end

end PeriodicGroundSpaceIndependence

section PeriodicCornerSeparation

/-!
## Separation of corners belonging to distinct periodic tensors

An isometric corner with a letter intertwiner has its boundary spaces
contained in those of the original tensor. If two primitive blocked corners
were equivalent up to gauge and phase, their boundary spaces would agree.
A nonzero vector in this common space, reindexed into the original site
coordinates, would then belong to both original boundary spaces. The
vanishing original-chain angle for inequivalent periodic tensors excludes
this possibility.

The result concerns arbitrary common positive blocking lengths and literal
isometric corners. It does not infer corner separation from the names of the
blocks or from inequivalence at a single finite volume.

Sources: arXiv:1708.00029, Lemma bdcf;
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma disjoint, equations
C1C2 and limP12.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
open Filter
open Kraus (blockPhysDim blockTensor)
namespace MPSTensor
variable {d D E D₂ F L : ℕ}

/-- An isometric virtual embedding with the adjoint letter intertwiner
places every sector boundary vector in the original boundary space.
Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag. -/
theorem groundSpaceES_le_of_isometric_cointertwiner
    (A : MPSTensor d D) (B : MPSTensor d E) (V : Matrix (Fin D) (Fin E) ℂ)
    (hV : Vᴴ * V = 1) (hInt : ∀ i, Vᴴ * A i = B i * Vᴴ) (N : ℕ) :
    groundSpaceES B N ≤ groundSpaceES A N := by
  have hEmbed (Y : Matrix (Fin E) (Fin E) ℂ) :
      groundSpaceMap A N (V * Y * Vᴴ) = groundSpaceMap B N Y := by
    ext σ
    simp only [groundSpaceMap_apply]
    have hWord := Kraus.evalWord_intertwine B A Vᴴ (fun i => (hInt i).symm) (List.ofFn σ)
    calc
      _ = Matrix.trace (Vᴴ * (Kraus.evalWord A (List.ofFn σ) * V * Y)) := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (Kraus.evalWord A (List.ofFn σ) * V * Y) Vᴴ
      _ = _ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hWord, Matrix.mul_assoc,
          Matrix.mul_assoc (Kraus.evalWord B (List.ofFn σ)) Vᴴ (V * Y),
          ← Matrix.mul_assoc Vᴴ V Y, hV, Matrix.one_mul]
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  rintro _ ⟨u, rfl⟩
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)).surjective u
  refine ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (V * Y * Vᴴ), ?_⟩
  change groundSpaceMapES A N (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
    (V * Y * Vᴴ)) = groundSpaceMapES B N (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E) Y)
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply, hEmbed]

/-- Primitive corners of gauge-phase inequivalent normalized periodic
original tensors cannot be gauge-phase equivalent at a common positive
blocking length. Only one corner requires a primitive faithful witness.
Source: arXiv:1708.00029, Lemma bdcf;
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma disjoint, equations
C1C2 and limP12. The proof uses original-chain boundary-space separation,
not an unproved separation assumption on compressed sectors. -/
theorem IsPeriodic.not_gaugePhaseEquiv_of_primitive_corners
    [NeZero E] {m m₂ : ℕ} {A : MPSTensor d D} {A' : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hA' : IsPeriodic m₂ A')
    (hDistinct : ∀ e : D₂ = D, ¬ GaugePhaseEquiv (e ▸ A') A)
    (hL : 0 < L) (B : MPSTensor (blockPhysDim d L) E)
    (C : MPSTensor (blockPhysDim d L) F)
    (V : Matrix (Fin D) (Fin E) ℂ) (W : Matrix (Fin D₂) (Fin F) ℂ)
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hB : Kraus.HasComplementaryFixedPointGap B ρ)
    (hρ : ρ.PosDef)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hInt : ∀ i, Vᴴ * blockTensor A L i = B i * Vᴴ)
    (hInt' : ∀ i, Wᴴ * blockTensor A' L i = C i * Wᴴ) :
    ∀ e : F = E, ¬ GaugePhaseEquiv (e ▸ C) B := by
  intro e hGauge
  subst F
  have hCLength : Tendsto (fun n : ℕ => n * L) atTop atTop :=
    tendsto_id.atTop_mul_one_le (fun _ => hL)
  have hAngle := hCLength.eventually
    (hA.eventually_norm_inner_groundSpaceES_le_of_inequivalent hA' hDistinct
      (show (0 : ℝ) < 1 / 2 by norm_num))
  have hInject := hB.eventually_groundSpaceMapES_injective_and_inverseGram_bound hρ
    (a := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨N, hN, hInj, hInverse⟩ := (hAngle.and hInject).exists
  let u : EuclideanSpace ℂ (Fin E × Fin E) :=
    Matrix.frobeniusEquivEuclidean (Fin E) (Fin E) 1
  let x := groundSpaceMapES B N u
  have hx : x ∈ groundSpaceES B N := by
    rw [← range_groundSpaceMapES]
    exact ⟨u, rfl⟩
  have hxne : x ≠ 0 := by
    intro hz
    have hu : u = 0 := hInj (by simpa only [map_zero, x] using hz)
    have h1 : (1 : Matrix (Fin E) (Fin E) ℂ) = 0 :=
      (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)).injective (by
        simpa only [map_zero, u] using hu)
    exact one_ne_zero h1
  have hxC : x ∈ groundSpaceES C N := by
    have hGauge' : GaugePhaseEquiv C B := by simpa using hGauge
    rw [hGauge'.groundSpaceES_eq N]
    exact hx
  let U := blockedConfigLinearIsometryEquiv d N L
  have hxA : U x ∈ groundSpaceES A (N * L) := by
    rw [← groundSpaceES_blockTensor_map A L N]
    exact ⟨x, groundSpaceES_le_of_isometric_cointertwiner
      (blockTensor A L) B V hV hInt N hx, rfl⟩
  have hxA' : U x ∈ groundSpaceES A' (N * L) := by
    rw [← groundSpaceES_blockTensor_map A' L N]
    exact ⟨x, groundSpaceES_le_of_isometric_cointertwiner
      (blockTensor A' L) C W hW hInt' N hxC, rfl⟩
  have h := hN (U x) hxA (U x) hxA'
  rw [U.inner_map_map, U.norm_map] at h
  simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x)] at h
  nlinarith [norm_pos_iff.mpr hxne]

end MPSTensor

end PeriodicCornerSeparation
