/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProjectedPositiveEnergy
import QICLean.Analysis.ProjectedTrialSpaceEnergy
import QICLean.Analysis.RitzCompression
import QICLean.Analysis.ViableSubspaceDimension
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Algebra.HermitianHelpers
import QICLean.Analysis.EuclideanEigenvectorBasis

/-!
# Extraction of a low-energy window from a close candidate space

Let `R` be a space that is `δ`-close to the window `G(c)` of an actual
Hamiltonian, spanned by the eigenvectors of energy at most `E₀ + c`. The
projection of the window into `R` has the dimension of the window and is
`δ`-close to it in both directions. The Ritz space of the same dimension,
computed from the Hamiltonian compressed to `R` alone, lies in `R`, and
every one of its vectors has energy at most
`E₀ + ((1 + 1/ρ) c + (1 + ρ) ‖H - E₀‖ δ) / (1 - δ)` for every `ρ > 0`.
No spectral gap at the edge of the window is assumed.

This is the extraction step of ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643, and the min–max argument of Theorem `t:alg1`,
lines 1811–1817, for the window of Theorem `t:alg2`, lines 1869–1878.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- For a vector `w` of a subspace `W`, the projection of `x` onto `W` has
squared norm at least `|⟨w, x⟩|² / ‖w‖²`. Supporting ALVV,
arXiv:1602.08828v2, the reformulation of closeness at line 488. -/
theorem norm_inner_sq_le_norm_sq_mul_norm_starProjection_sq (W : Submodule 𝕜 E)
    {w : E} (hw : w ∈ W) (x : E) :
    ‖⟪w, x⟫_𝕜‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖W.starProjection x‖ ^ 2 := by
  have hinner : ⟪w, x⟫_𝕜 = ⟪w, W.starProjection x⟫_𝕜 := by
    rw [← W.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.mpr hw]
  rw [hinner, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The projection of a target into a subspace that is `δ`-close to it is
`δ`-close to the target in both directions. Supporting ALVV,
arXiv:1602.08828v2, the extraction in Figure `fig:algo1`, lines 1641–1643. -/
theorem IsCloseTo.map_starProjection_isCloseTo {δ : ℝ} {U G : Submodule 𝕜 E}
    (h : IsCloseTo δ U G) (hδ : δ ≤ 1) :
    IsCloseTo δ (G.map U.starProjection.toLinearMap) G ∧
      IsCloseTo δ G (G.map U.starProjection.toLinearMap) := by
  have hU := isCloseTo_iff.mp h
  let V := G.map U.starProjection.toLinearMap
  have hmem (g : E) (hg : g ∈ G) : U.starProjection g ∈ V := ⟨g, hg, rfl⟩
  have hinnerU (g : E) : ⟪U.starProjection g, g⟫_𝕜 = (‖U.starProjection g‖ ^ 2 : 𝕜) := by
    calc
      ⟪U.starProjection g, g⟫_𝕜 = ⟪U.starProjection (U.starProjection g), g⟫_𝕜 := by
        rw [U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem g)]
      _ = ⟪U.starProjection g, U.starProjection g⟫_𝕜 := U.inner_starProjection_left_eq_right _ _
      _ = _ := inner_self_eq_norm_sq_to_K _
  have hnormInner (g : E) : ‖⟪U.starProjection g, g⟫_𝕜‖ = ‖U.starProjection g‖ ^ 2 := by
    rw [hinnerU, ← RCLike.ofReal_pow, RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
  refine ⟨isCloseTo_iff.mpr fun g hg ↦ ?_, isCloseTo_iff.mpr ?_⟩
  · -- Every vector of the target is captured by its own projection.
    have hcs := V.norm_inner_sq_le_norm_sq_mul_norm_starProjection_sq (hmem g hg) g
    rw [hnormInner] at hcs
    rcases eq_or_lt_of_le (sq_nonneg ‖U.starProjection g‖) with h0 | hpos
    · have hzero : (1 - δ) * ‖g‖ ^ 2 ≤ 0 := by simpa only [← h0] using hU g hg
      exact hzero.trans (sq_nonneg _)
    · have hle : ‖U.starProjection g‖ ^ 2 ≤ ‖V.starProjection g‖ ^ 2 := by
        nlinarith only [hcs, hpos]
      exact (hU g hg).trans hle
  · -- Every projected vector is captured by the target.
    rintro _ ⟨g, hg, rfl⟩
    change (1 - δ) * ‖U.starProjection g‖ ^ 2 ≤ ‖G.starProjection (U.starProjection g)‖ ^ 2
    have hcs := G.norm_inner_sq_le_norm_sq_mul_norm_starProjection_sq hg (U.starProjection g)
    rw [← inner_conj_symm, RCLike.norm_conj, hnormInner] at hcs
    have hg2 := hU g hg
    rcases eq_or_lt_of_le (sq_nonneg ‖g‖) with h0 | hpos
    · have hz : ‖U.starProjection g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((U.starProjection.le_of_opNorm_le U.starProjection_norm_le g).trans_eq (one_mul _)) 2
      rw [← h0] at hz
      have : ‖U.starProjection g‖ ^ 2 = 0 := le_antisymm hz (sq_nonneg _)
      rw [this, mul_zero]
      exact sq_nonneg _
    · have hδ0 : 0 ≤ 1 - δ := by linarith only [hδ]
      have hP0 : 0 ≤ ‖U.starProjection g‖ ^ 2 := sq_nonneg _
      have hstep : (1 - δ) * ‖U.starProjection g‖ ^ 2 * ‖g‖ ^ 2 ≤
          ‖U.starProjection g‖ ^ 2 * ‖U.starProjection g‖ ^ 2 :=
        by nlinarith only [hg2, hP0]
      have hfinal : (1 - δ) * ‖U.starProjection g‖ ^ 2 * ‖g‖ ^ 2 ≤
          ‖G.starProjection (U.starProjection g)‖ ^ 2 * ‖g‖ ^ 2 := by
        nlinarith only [hstep, hcs]
      exact le_of_mul_le_mul_right hfinal hpos

end Submodule

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Shifting a matrix by a scalar shifts its Euclidean action by the same
scalar. Supporting ALVV, arXiv:1602.08828v2, the canonical energy shift of
Theorem `t:aisgapless`, lines 1027–1041. -/
private theorem toEuclideanCLM_sub_smul_one_apply {σ : Type*} [Fintype σ] [DecidableEq σ]
    (H : Matrix σ σ ℂ) (c : ℂ) (x : EuclideanSpace ℂ σ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (H - c • 1) x =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) H x - c • x := by
  apply WithLp.ofLp_injective 2
  simp

/-- A space `R` that is `δ`-close to the original window `G(c)` contains the
projection of the window, of the same dimension and `δ`-close to the window in
both directions, and the Ritz space of the Hamiltonian compressed to `R` of
the same dimension. Every vector of the Ritz space has energy at most
`E₀ + ((1 + 1/ρ) c + (1 + ρ) A δ) / (1 - δ)`, where `A` is the norm of the
centred Hamiltonian, for every `ρ > 0`. No gap at the edge of the window is
used. ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1641–1643, and the
min–max step of Theorem `t:alg1`, lines 1811–1817. -/
theorem window_extraction_of_isCloseTo {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) {c δ : ℝ} (hc : 0 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (R : Submodule ℂ (EuclideanSpace ℂ σ))
    (hR : Submodule.IsCloseTo δ R
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c))) :
    let Gc := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
    let V := Gc.map R.starProjection.toLinearMap
    let A := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (H - (minEigenvalue hH : ℂ) • 1)‖
    let Rz := R.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) (Module.finrank ℂ Gc)
    V ≤ R ∧ Module.finrank ℂ V = Module.finrank ℂ Gc ∧
      Submodule.IsCloseTo δ V Gc ∧ Submodule.IsCloseTo δ Gc V ∧
      Rz ≤ R ∧ Module.finrank ℂ Rz = Module.finrank ℂ Gc ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x ∈ Rz,
        (inner ℂ x (Matrix.toEuclideanLin H x)).re ≤
          (minEigenvalue hH + ((1 + 1 / ρ) * c + (1 + ρ) * A * δ) / (1 - δ)) * ‖x‖ ^ 2 := by
  intro Gc V A Rz
  let H0 := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (H - (minEigenvalue hH : ℂ) • 1)
  -- The projected window: inclusion, dimension and closeness.
  obtain ⟨hVR, hdimV, -⟩ := Submodule.IsCloseTo.map_starProjection_energy_le hR hδ0 hδ1 0
    (fun _ _ ↦ by simp) (fun _ _ ↦ rfl) (le_of_eq norm_zero)
  obtain ⟨hVG, hGV⟩ := Submodule.IsCloseTo.map_starProjection_isCloseTo hR hδ1.le
  have hGR : Module.finrank ℂ Gc ≤ Module.finrank ℂ R := Submodule.IsCloseTo.finrank_le hR hδ1
  refine ⟨hVR, hdimV, hVG, hGV, R.ritzSubspace_le _ _,
    R.finrank_ritzSubspace _ _ hGR, ?_⟩
  intro ρ hρ x hx
  -- Energies of the window and of the projected window.
  have hshift (y : EuclideanSpace ℂ σ) :
      RCLike.re ⟪H0 y, y⟫_ℂ = (inner ℂ y (Matrix.toEuclideanLin H y)).re -
        minEigenvalue hH * ‖y‖ ^ 2 := by
    rw [← inner_re_symm]
    change (inner ℂ y (H0 y)).re = _
    rw [toEuclideanCLM_sub_smul_one_apply, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, Complex.sub_re]
    have hre : ((minEigenvalue hH : ℂ) * ((‖y‖ : ℂ) ^ 2)).re = minEigenvalue hH * ‖y‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact congrArg₂ (· - ·) rfl hre
  have hpos : H0.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff H0).mp
      (Matrix.isPositive_toEuclideanLin_iff.mpr (sub_minEigenvalue_smul_one_posSemidef hH))
  have hG : ∀ g ∈ Gc, RCLike.re ⟪H0 g, g⟫_ℂ ≤ c * ‖g‖ ^ 2 := by
    intro g hg
    have hle := Submodule.re_inner_apply_le_of_mem_spectralSpanLE hH.eigenvectorBasis
      hH.eigenvalues (Matrix.toEuclideanLin H) (hH.toEuclideanCLM_eigenvectorBasis)
      (minEigenvalue hH + c) hg
    rw [hshift]
    linarith only [hle]
  have hVenergy := Submodule.IsCloseTo.map_starProjection_positive_energy_le hR hδ0 hδ1 ρ hρ
    H0 hpos hc hG le_rfl
  let e := ((1 + 1 / ρ) * c + (1 + ρ) * A * δ) / (1 - δ)
  -- The Ritz space is controlled by the projected window as a trial space.
  let V' : Submodule ℂ R := V.comap R.subtype
  have hV'dim : Module.finrank ℂ V' = Module.finrank ℂ Gc :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hVR)).trans hdimV
  have htrial : ∀ y ∈ V', (inner ℂ (y : EuclideanSpace ℂ σ)
      (Matrix.toEuclideanLin H (y : EuclideanSpace ℂ σ))).re ≤
        (minEigenvalue hH + e) * ‖(y : EuclideanSpace ℂ σ)‖ ^ 2 := by
    intro y hy
    have h1 := hVenergy (y : EuclideanSpace ℂ σ) hy
    rw [hshift] at h1
    change _ ≤ e * _ at h1
    linarith only [h1]
  have hx' : x ∈ R.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH)
      (Module.finrank ℂ V') := by
    rw [hV'dim]
    exact hx
  exact R.re_inner_apply_le_of_mem_ritzSubspace _ V' (minEigenvalue hH + e) htrial hx'

end TNLean.MPS.AreaLaw
