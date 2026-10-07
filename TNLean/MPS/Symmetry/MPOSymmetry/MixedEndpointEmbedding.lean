/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSupport
import TNLean.Algebra.MatrixCoordinateInclusion

/-!
# The embedded first endpoint inside the extended local support

The first endpoint tensor is included in the diagonal physical sector of
the mixed interpolation, with all other physical letters zero. Compressing
the unweighted mixed tensor to the first virtual summand recovers this
embedded tensor. Its canonical two-site support is contained in the actual
extended support at parameter zero.

Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601 and
1690–1692. This inclusion is one direction of the endpoint parent comparison;
no common kernel or spectral gap is assumed or asserted.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The first endpoint in the common physical space, extended by zero
outside its diagonal physical sector. Source: arXiv:2203.12563,
Section 5, `defAgamma`, lines 1586–1601. -/
def mixedEndpointLeftTensor (A₀ : MPSTensor (D₀ * D₀) D₀) (D₁ : ℕ) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₀ := fun p =>
  match finSumFinEquiv.symm (finProdFinEquiv.symm p).1,
      finSumFinEquiv.symm (finProdFinEquiv.symm p).2 with
  | .inl a, .inl b => A₀ (finProdFinEquiv (a, b))
  | _, _ => 0

/-- Zero extension into the diagonal physical sector preserves endpoint
injectivity. Source: arXiv:2203.12563, Section 5, lines 1580–1601. -/
theorem isInjective_mixedEndpointLeftTensor
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) :
    Kraus.IsInjective (mixedEndpointLeftTensor A₀ D₁) := by
  have hle : Submodule.span ℂ (Set.range A₀) ≤
      Submodule.span ℂ (Set.range (mixedEndpointLeftTensor A₀ D₁)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
    apply Submodule.subset_span
    refine ⟨finProdFinEquiv (finSumFinEquiv (.inl a), finSumFinEquiv (.inl b)), ?_⟩
    simp [mixedEndpointLeftTensor]
  rw [hA₀] at hle
  exact top_unique hle

/-- The virtual first-summand projection is exactly the zero-parameter
weight. Source: arXiv:2203.12563, `defAgamma`, line 1589. -/
theorem coordinateInclusion_first_projection_eq_bondWeight :
    Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁)) *
      (Matrix.coordinateInclusion (Fin.castAddEmb D₁))ᴴ =
        bondInterpolationMatrix D₀ D₁ 0 := by
  have hdisjoint (a : Fin D₀) (b : Fin D₁) : Fin.castAdd D₁ a ≠ Fin.natAdd D₀ b := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [Matrix.coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.castAddEmb_apply, bondInterpolationMatrix, bondInterpolationWeight,
      Matrix.diagonal_apply, eq_comm, hdisjoint]

/-- Compression to the first virtual block is the actual embedded first
endpoint tensor. Source: arXiv:2203.12563, Section 5,
`defAgamma`, lines 1586–1601. -/
theorem mixedEndpointBase_first_compression
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    (Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁)))ᴴ *
      mixedEndpointBase A₀ A₁ p * Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
        mixedEndpointLeftTensor A₀ D₁ p := by
  rw [Matrix.coordinateInclusion_compression]
  ext i j
  simp only [mixedEndpointBase, Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.castAddEmb_apply, finSumFinEquiv_symm_apply_castAdd]
  unfold mixedEndpointLeftTensor
  cases hrow : finSumFinEquiv.symm (finProdFinEquiv.symm p).1 <;>
    cases hcol : finSumFinEquiv.symm (finProdFinEquiv.symm p).2 <;>
    simp [mixedEndpointLetter, Matrix.fromBlocks]

/-- Padding the endpoint boundary into the first virtual corner identifies
its canonical two-site vector with an extended-support vector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem insertedTwoSiteMap_first_boundary
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (X : Matrix (Fin D₀) (Fin D₀) ℂ) :
    let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
    insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
      (WithLp.toLp 2 (fun p => (V * X * Vᴴ) p.1 p.2)) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) 2)).symm
        (groundSpaceMap (mixedEndpointLeftTensor A₀ D₁) 2 X) := by
  dsimp only
  let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
  apply PiLp.ext
  intro σ
  rw [insertedTwoSiteMap_apply]
  have hη : Matrix.of (fun a b => (V * X * Vᴴ) a b) = V * X * Vᴴ := by
    ext a b
    rfl
  change Matrix.trace (mixedEndpointBase A₀ A₁ (σ 0) * bondInterpolationMatrix D₀ D₁ 0 *
    mixedEndpointBase A₀ A₁ (σ 1) * Matrix.of (fun a b => (V * X * Vᴴ) a b)) = _
  rw [hη, ← coordinateInclusion_first_projection_eq_bondWeight]
  change Matrix.trace (mixedEndpointBase A₀ A₁ (σ 0) * (V * Vᴴ) *
    mixedEndpointBase A₀ A₁ (σ 1) * (V * X * Vᴴ)) = _
  rw [show mixedEndpointBase A₀ A₁ (σ 0) * (V * Vᴴ) * mixedEndpointBase A₀ A₁ (σ 1) *
      (V * X * Vᴴ) =
      (mixedEndpointBase A₀ A₁ (σ 0) * V * Vᴴ * mixedEndpointBase A₀ A₁ (σ 1) * V * X) * Vᴴ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show Vᴴ * (mixedEndpointBase A₀ A₁ (σ 0) * V * Vᴴ *
      mixedEndpointBase A₀ A₁ (σ 1) * V * X) =
      (Vᴴ * mixedEndpointBase A₀ A₁ (σ 0) * V) *
        (Vᴴ * mixedEndpointBase A₀ A₁ (σ 1) * V) * X by simp only [Matrix.mul_assoc]]
  rw [mixedEndpointBase_first_compression, mixedEndpointBase_first_compression]
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- The canonical two-site support of the embedded first endpoint is
contained in the extended zero-parameter support. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem groundSpaceES_mixedEndpointLeftTensor_le_extendedSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    groundSpaceES (mixedEndpointLeftTensor A₀ D₁) 2 ≤
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0)).range := by
  rintro ψ ⟨_, ⟨X, rfl⟩, rfl⟩
  let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
  exact ⟨WithLp.toLp 2 (fun p => (V * X * Vᴴ) p.1 p.2),
    insertedTwoSiteMap_first_boundary A₀ A₁ X⟩

end MPOSymmetry
end MPSTensor
