/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram

/-!
# Mixed Gram operators for MPS boundary maps

The mixed Gram operator of two boundary maps is a reshuffling of the
rectangular mixed transfer map. This is the boundary-coordinate calculation
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`, used in
equation `limitepsilonm` (local source lines 1661--1691).
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-- The matrix-unit entries of the mixed boundary Gram operator are entries
of the iterated rectangular mixed transfer map. This is the boundary-coordinate
calculation in Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`. -/
theorem inner_single_mixed_groundSpaceGram_single
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (n : ℕ)
    (a b : Fin D₁) (c e : Fin D₂) :
    ⟪EuclideanSpace.single (b, a) 1,
      ((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n))
        (EuclideanSpace.single (e, c) 1)⟫_ℂ =
      ((Kraus.mixedMapLM B A) ^ n) (Matrix.single c a 1) e b := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    groundSpaceMapES_single, groundSpaceMapES_single]
  change inner ℂ (WithLp.toLp 2 (groundSpaceMap A n (Matrix.single a b 1)))
    (WithLp.toLp 2 (groundSpaceMap B n (Matrix.single c e 1))) = _
  rw [EuclideanSpace.inner_toLp_toLp, Kraus.mixedMapLM_pow_apply]
  simp [groundSpaceMap_apply, Matrix.trace_mul_single, dotProduct,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- Rectangular reshuffling formula for the mixed boundary Gram operator;
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma `disjoint`, equations
`ip` and `P12` (local source lines 1744--1777). -/
theorem adjoint_groundSpaceMapES_comp_eq_mixedTransfer
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (n : ℕ) :
    (groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n) =
      (Matrix.toEuclideanLin (fun (b, a) (e, c) ↦
        ((Kraus.mixedMapLM B A) ^ n) (Matrix.single c a 1) e b)).toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin D₂ × Fin D₂) ℂ).toBasis.ext fun ⟨e, c⟩ ↦ ?_
  apply PiLp.ext
  rintro ⟨b, a⟩
  have h := inner_single_mixed_groundSpaceGram_single A B n a b c e
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.coe_toContinuousLinearMap]
  change _ = ∑ j : Fin D₂ × Fin D₂,
    ((Kraus.mixedMapLM B A) ^ n) (Matrix.single j.2 a 1) j.1 b *
      (EuclideanSpace.single (e, c) (1 : ℂ)) j
  simpa [EuclideanSpace.single, PiLp.single_apply] using h

/-- Decay of the mixed transfer iterates implies operator-norm decay of the
mixed boundary Gram operators. This is the finite-dimensional passage in
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma `disjoint`, equations
`ip`--`limP12` (local source lines 1744--1820). -/
theorem adjoint_groundSpaceMapES_comp_tendsto_zero
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hdecay : ∀ X : Matrix (Fin D₂) (Fin D₁) ℂ,
      Filter.Tendsto (fun n ↦ ((Kraus.mixedMapLM B A) ^ n) X)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ (groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n))
      Filter.atTop (nhds 0) := by
  let Φ : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin D₂ × Fin D₂) →L[ℂ]
        EuclideanSpace ℂ (Fin D₁ × Fin D₁)) :=
    Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap
  have hM : Filter.Tendsto (fun n ↦ fun (b, a) (e, c) ↦
      ((Kraus.mixedMapLM B A) ^ n) (Matrix.single c a 1) e b)
      Filter.atTop (nhds (0 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)) := by
    exact tendsto_pi_nhds.mpr fun ⟨b, a⟩ ↦ tendsto_pi_nhds.mpr fun ⟨e, c⟩ ↦
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hdecay (Matrix.single c a 1)) e) b
  have h := (Φ.toLinearMap.continuous_of_finiteDimensional.tendsto 0).comp hM
  rw [map_zero] at h
  change Filter.Tendsto (fun n ↦
    (Matrix.toEuclideanLin (fun (b, a) (e, c) ↦
      ((Kraus.mixedMapLM B A) ^ n) (Matrix.single c a 1) e b)).toContinuousLinearMap)
      Filter.atTop (nhds 0) at h
  simpa only [← adjoint_groundSpaceMapES_comp_eq_mixedTransfer] using h

private theorem norm_le_sqrt_inverseGram_mul_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →L[ℂ] F) (hT : Function.Injective T) (x : E) :
    ‖x‖ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram T hT‖ * ‖T x‖ := by
  have h := ((ContinuousLinearMap.inverseGram T hT).comp T.adjoint).le_opNorm (T x)
  rw [ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt] at h
  change ‖((ContinuousLinearMap.inverseGram T hT).comp (T.adjoint.comp T)) x‖ ≤ _ at h
  simpa only [ContinuousLinearMap.inverseGram_comp_adjoint_comp_self,
    ContinuousLinearMap.id_apply] using h

/-- The mixed Gram norm bounds the overlap of two physical ground spaces,
with the inverse Gram norms accounting for boundary normalization. This is
the estimate combining `ip` with `C1C2` in Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma `disjoint`, lines 1744--1815. -/
theorem norm_inner_groundSpaceES_le_mixedGram
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (n : ℕ)
    (hA : Function.Injective (groundSpaceMapES A n))
    (hB : Function.Injective (groundSpaceMapES B n))
    {x y : EuclideanSpace ℂ (Cfg d n)}
    (hx : x ∈ groundSpaceES A n) (hy : y ∈ groundSpaceES B n) :
    ‖⟪x, y⟫_ℂ‖ ≤
      (Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hA‖ *
        ‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES B n) hB‖) *
      ‖x‖ * ‖y‖ := by
  obtain ⟨u, rfl⟩ := (range_groundSpaceMapES A n ▸ hx)
  obtain ⟨v, rfl⟩ := (range_groundSpaceMapES B n ▸ hy)
  change ‖⟪groundSpaceMapES A n u, groundSpaceMapES B n v⟫_ℂ‖ ≤ _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have h := (norm_inner_le_norm (𝕜 := ℂ) u
      (((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)) v)).trans
    (mul_le_mul_of_nonneg_left
      (((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)).le_opNorm v)
      (norm_nonneg u))
  have hbound := mul_le_mul
    (norm_le_sqrt_inverseGram_mul_norm (groundSpaceMapES A n) hA u)
    (mul_le_mul_of_nonneg_left
      (norm_le_sqrt_inverseGram_mul_norm (groundSpaceMapES B n) hB v)
      (norm_nonneg ((groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n))))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  convert h.trans hbound using 1 <;> first | rfl | (ring_nf; rfl)

end MPSTensor
