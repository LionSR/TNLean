/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometricProjection
import TNLean.MPS.ParentHamiltonian.Martingale.IsometricCompressionGap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Parent projections supported in a frame

For subspaces \(S\subseteq F\), the parent interaction
\(h=1-P_S\) commutes with the frame projection \(P_F\), equals the
identity on \(F^\perp\), and satisfies \(h\ge 1-P_F\).
For a rectangular isometry \(U\) whose range contains \(S\), its
compression is exactly \(U^*hU=1-P_{U^*S}\), with kernel \(U^*S\).

These are auxiliary Hilbert-space results for the boundary-frame reduction
in GLM23, arXiv:2203.12563v3, Section 5, lines 1695–1777. The application
must prove that the actual parent support is contained in the actual frame;
no ambient surjectivity or dimension lower bound is assumed here.
-/

open scoped InnerProductSpace ComplexOrder

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {S F : Submodule ℂ E}

/-- The larger frame projection absorbs the supported projection on the left. -/
theorem starProjection_comp_starProjection_eq_right_of_le (hSF : S ≤ F) :
    F.starProjection.toLinearMap ∘ₗ S.starProjection.toLinearMap =
      S.starProjection.toLinearMap := by
  ext v
  exact starProjection_eq_self_iff.mpr (hSF (S.starProjection_apply_mem v))

/-- The larger frame projection also absorbs the supported projection on the right. -/
theorem starProjection_comp_starProjection_eq_left_of_le (hSF : S ≤ F) :
    S.starProjection.toLinearMap ∘ₗ F.starProjection.toLinearMap =
      S.starProjection.toLinearMap := by
  exact congrArg ContinuousLinearMap.toLinearMap
    (starProjection_comp_starProjection_of_le hSF)

/-- A frame containing the parent support reduces its complementary interaction. -/
theorem commute_starProjection_one_sub_starProjection_of_le (hSF : S ≤ F) :
    Commute F.starProjection.toLinearMap (1 - S.starProjection.toLinearMap) := by
  apply (commute_iff_eq _ _).mpr
  change F.starProjection.toLinearMap ∘ₗ (LinearMap.id - S.starProjection.toLinearMap) =
    (LinearMap.id - S.starProjection.toLinearMap) ∘ₗ F.starProjection.toLinearMap
  rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
    starProjection_comp_starProjection_eq_right_of_le hSF,
    starProjection_comp_starProjection_eq_left_of_le hSF]

/-- The supported parent interaction is the identity outside the frame. -/
theorem one_sub_starProjection_apply_of_mem_orthogonal_of_le
    (hSF : S ≤ F) {v : E} (hv : v ∈ Fᗮ) :
    (1 - S.starProjection.toLinearMap) v = v := by
  have hzero : S.starProjection v = 0 :=
    S.starProjection_apply_eq_zero_iff.mpr (orthogonal_le hSF hv)
  change v - S.starProjection v = v
  rw [hzero, sub_zero]

/-- The frame-complement penalty is bounded by the supported parent interaction. -/
theorem one_sub_starProjection_le_one_sub_starProjection_of_le (hSF : S ≤ F) :
    1 - F.starProjection.toLinearMap ≤ 1 - S.starProjection.toLinearMap := by
  apply sub_le_sub_left
  apply (isSymmetricProjection_starProjection S).le_iff_range_le_range
    (isSymmetricProjection_starProjection F) |>.mpr
  simpa only [range_starProjection] using hSF

/-- The supported interaction minus the frame-complement penalty is positive. -/
theorem isPositive_one_sub_starProjection_sub_one_sub_starProjection_of_le
    (hSF : S ≤ F) :
    ((1 - S.starProjection.toLinearMap) -
      (1 - F.starProjection.toLinearMap)).IsPositive :=
  LinearMap.le_def.mp (one_sub_starProjection_le_one_sub_starProjection_of_le hSF)

/-- The frame-complement penalty bounds the parent quadratic form from below. -/
theorem re_inner_one_sub_starProjection_le_of_le (hSF : S ≤ F) (v : E) :
    (⟪(1 - F.starProjection.toLinearMap) v, v⟫_ℂ).re ≤
      (⟪(1 - S.starProjection.toLinearMap) v, v⟫_ℂ).re := by
  have hpos := isPositive_one_sub_starProjection_sub_one_sub_starProjection_of_le hSF
  simpa only [RCLike.re_eq_complex_re, LinearMap.sub_apply, inner_sub_left,
    Complex.sub_re, sub_nonneg] using hpos.re_inner_nonneg_left v

/-- The parent energy controls the squared norm of the component outside the frame. -/
theorem norm_sq_starProjection_orthogonal_le_re_inner_one_sub_of_le
    (hSF : S ≤ F) (v : E) :
    ‖Fᗮ.starProjection v‖ ^ 2 ≤
      (⟪(1 - S.starProjection.toLinearMap) v, v⟫_ℂ).re := by
  calc
    ‖Fᗮ.starProjection v‖ ^ 2 = (⟪Fᗮ.starProjection v, v⟫_ℂ).re :=
      (re_inner_starProjection_eq_normSq Fᗮ v).symm
    _ = (⟪(1 - F.starProjection.toLinearMap) v, v⟫_ℂ).re := by
      rw [starProjection_orthogonal_val]
      rfl
    _ ≤ _ := re_inner_one_sub_starProjection_le_of_le hSF v

end Submodule

namespace LinearIsometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The range projection of a rectangular isometry is \(UU^*\). -/
theorem starProjection_range_eq_comp_adjoint (U : E →ₗᵢ[ℂ] F) :
    (LinearMap.range U.toLinearMap).starProjection.toLinearMap =
      U.toLinearMap ∘ₗ U.toLinearMap.adjoint := by
  simpa only [Submodule.map_top, Submodule.starProjection_top, ContinuousLinearMap.coe_id,
    LinearMap.id_comp, LinearMap.comp_id] using
    U.starProjection_map_eq_comp_adjoint (⊤ : Submodule ℂ E)

/-- Inclusion of the parent support in an isometric frame gives the exact reducing
commutator used by compression. -/
theorem commute_rangeProjection_one_sub_starProjection_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint)
      (1 - S.starProjection.toLinearMap) := by
  rw [← U.starProjection_range_eq_comp_adjoint]
  exact Submodule.commute_starProjection_one_sub_starProjection_of_le hS

/-- Mapping a supported subspace through the adjoint and back recovers that subspace. -/
theorem map_adjoint_map_eq_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    (S.map U.toLinearMap.adjoint).map U.toLinearMap = S := by
  have hAdjoint (v : E) : U.toLinearMap.adjoint (U v) = v :=
    LinearMap.congr_fun U.adjoint_comp_self' v
  have hRange (v : F) (hv : v ∈ S) : U (U.toLinearMap.adjoint v) = v := by
    obtain ⟨w, rfl⟩ := hS hv
    exact congrArg U (hAdjoint w)
  ext v
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    change U (U.toLinearMap.adjoint z) ∈ S
    rwa [hRange z hz]
  · intro hv
    exact ⟨U.toLinearMap.adjoint v, ⟨v, hv, rfl⟩, hRange v hv⟩

/-- Compression of a supported projection is projection onto its adjoint image. -/
theorem compression_starProjection_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    U.compression S.starProjection.toLinearMap =
      (S.map U.toLinearMap.adjoint).starProjection.toLinearMap := by
  ext v
  have hproj : U ((S.map U.toLinearMap.adjoint).starProjection v) =
      S.starProjection (U v) := by
    simpa only [U.map_adjoint_map_eq_of_le_range S hS] using
      U.map_starProjection (S.map U.toLinearMap.adjoint) v
  change U.toLinearMap.adjoint (S.starProjection (U v)) =
    (S.map U.toLinearMap.adjoint).starProjection v
  rw [← hproj]
  exact LinearMap.congr_fun U.adjoint_comp_self' _

/-- The compressed parent interaction is the complement of the projection onto
the compressed support. This is auxiliary to GLM23, Section 5, lines 1695–1777. -/
theorem compression_one_sub_starProjection_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    U.compression (1 - S.starProjection.toLinearMap) =
      1 - (S.map U.toLinearMap.adjoint).starProjection.toLinearMap := by
  ext v
  have hproj := LinearMap.congr_fun (U.compression_starProjection_of_le_range S hS) v
  have hAdjoint : U.toLinearMap.adjoint (U v) = v :=
    LinearMap.congr_fun U.adjoint_comp_self' v
  change U.toLinearMap.adjoint (U v - S.starProjection (U v)) =
    v - (S.map U.toLinearMap.adjoint).starProjection v
  rw [map_sub, hAdjoint]
  exact congrArg (v - ·) hproj

/-- Equivalently, the compressed parent interaction projects onto the orthogonal
complement of its compressed support. -/
theorem compression_one_sub_starProjection_eq_orthogonal_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    U.compression (1 - S.starProjection.toLinearMap) =
      (S.map U.toLinearMap.adjoint)ᗮ.starProjection.toLinearMap := by
  rw [U.compression_one_sub_starProjection_of_le_range S hS,
    Submodule.starProjection_orthogonal', ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one]

/-- The supported compressed interaction has exactly the adjoint image of the
original parent support as its kernel. -/
theorem ker_compression_one_sub_starProjection_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap) :
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      S.map U.toLinearMap.adjoint := by
  rw [U.compression_one_sub_starProjection_eq_orthogonal_of_le_range S hS,
    Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

/-- Compression preserves the norm gap of a supported parent interaction, with
the kernel expressed directly in the compressed support coordinates. -/
theorem norm_gap_compression_one_sub_starProjection_of_le_range
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F) (hS : S ≤ LinearMap.range U.toLinearMap)
    {δ : ℝ} (hGap : ∀ w ∈ Sᗮ,
      δ * ‖w‖ ≤ ‖(1 - S.starProjection.toLinearMap) w‖) :
    ∀ v ∈ (S.map U.toLinearMap.adjoint)ᗮ,
      δ * ‖v‖ ≤ ‖U.compression (1 - S.starProjection.toLinearMap) v‖ := by
  have hker : LinearMap.ker (1 - S.starProjection.toLinearMap) = S := by
    rw [← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
      ← Submodule.starProjection_orthogonal', Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal]
  have h := U.norm_gap_compression_of_commute (1 - S.starProjection.toLinearMap)
    (U.commute_rangeProjection_one_sub_starProjection_of_le_range S hS)
    (by simpa only [hker] using hGap)
  simpa only [U.ker_compression_one_sub_starProjection_of_le_range S hS] using h

end LinearIsometry
