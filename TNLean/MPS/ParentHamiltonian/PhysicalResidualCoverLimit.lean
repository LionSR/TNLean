/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectionDefectIsometry
import TNLean.MPS.ParentHamiltonian.ResidualWindowFullSectorSum
import TNLean.MPS.ParentHamiltonian.ResidualWindowLeftGroundSpace
import TNLean.MPS.ParentHamiltonian.ResidualWindowJointProjectionDecay
import TNLean.MPS.ParentHamiltonian.Martingale.AlignedResidueCoverGapLimit

/-!
# Physical residual covers from a primitive-sector resolution

A supplied isometric resolution of a blocked tensor identifies the joint
right, left, and full residual windows with the original physical interval
spaces. Primitive faithful inequivalent sectors, together with exact
orthogonal tail Gram matrices, give vanishing projection defects in the
original physical coordinates. The product order is reversed by taking
adjoints, so no commutativity of the interval projections is assumed.

The second result is an auxiliary finite-gap criterion. It retains exact
canonical kernels and an eventual aligned gap as explicit hypotheses; the
sector-resolution assumptions then extend the gap to all original volumes,
above the actual kernel at each volume. No periodicity of the original
tensor is required by either result.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), lines 2442--2531, and equations (3.12)--(3.16).
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D L : ℕ}

/-- A primitive, faithful, inequivalent isometric resolution of a blocked tensor,
with exact orthogonal correlated-tail Gram matrices, gives vanishing original
physical cover defects as the common overlap diverges. Both exterior lengths
may vary arbitrarily. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. The sector and Gram assumptions
are supplied explicitly; no periodicity of the original tensor is required. -/
theorem residual_cover_projection_defect_tendsto_zero_of_primitive_resolution
    [NeZero D] {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i)
    (hCoInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ)
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r)
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ} (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(groundSpaceES A (K n * L + M n * L + r n)).starProjection -
        (leftBoundaryMapES A (K n * L + M n * L) (r n)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K n * L) (M n * L) (r n)).range.starProjection‖)
      f (nhds 0) := by
  have hJoint := tendsto_norm_residualWindow_joint_projection_comp_sub_zero
    A B V ρ hP hρ hDistinct Q hQ hGram (K := K) (r := r) hM
  have hNorm (n : κ) :
      ‖(⨆ j,
          (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection.comp
          (⨆ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range).starProjection -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection‖ =
      ‖(groundSpaceES A (K n * L + M n * L + r n)).starProjection -
        (leftBoundaryMapES A (K n * L + M n * L) (r n)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K n * L) (M n * L) (r n)).range.starProjection‖ := by
    simp only [iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
      A B V hSum hCoInt,
      iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
        A B V hV hSum hInt,
      iSup_range_residualWindowMapES_eq_reindex_groundSpaceES_cover A B V hSum hCoInt]
    exact Submodule.norm_map_starProjection_comp_sub_eq _ _ _ _
  simpa only [hNorm] using hJoint

/-- Exact canonical kernels and an eventual aligned gap extend to all original
volumes under the supplied primitive-sector resolution and correlated-tail
Gram hypotheses. The gap is measured above the actual kernel, including
short volumes. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii). This is an auxiliary criterion with explicit
algebraic, kernel, and aligned-gap assumptions. -/
theorem exists_pos_openParentHamiltonianES_gap_of_aligned_gap_of_primitive_resolution
    [NeZero D] {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i)
    (hCoInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ)
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r)
    {R N₀ : ℕ} (hR : 0 < R) (hL : 0 < L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    {γ : ℝ} (hγ : 0 < γ)
    (hAligned : ∀ n ≥ N₀, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (n * L)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R (n * L) v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  exact exists_pos_openParentHamiltonianES_gap_of_aligned_gap_of_residue_cover_limit
    A hR hL hKernel hγ hAligned (fun K r =>
      residual_cover_projection_defect_tendsto_zero_of_primitive_resolution
        A B V ρ hP hρ hDistinct hV hSum hInt hCoInt Q hQ hGram
        (K := K) (r := r) Filter.tendsto_id)

end MPSTensor
