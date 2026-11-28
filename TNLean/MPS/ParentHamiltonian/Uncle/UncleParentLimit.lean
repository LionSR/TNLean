/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleTensor
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockedGroundSpaceTransport

/-!
# The canonical parent limit for a two-block uncle tensor

This is the perturbative limit in arXiv:1210.6613, Theorem
`thm:unclehamiltonian`. The rescaled blocked tensor is a regular polynomial
family. Injectivity of its value at zero ensures continuity of its actual
range projector. Off-diagonal virtual rescaling preserves the physical
range away from zero, giving the punctured limit of the original parent.

The uncle interaction is a matrix on two sites; the uncle Hamiltonian on the ring of \(N\)
sites is the Hamiltonian of its translates.
-/

open scoped Matrix Topology
open Kraus (blockTensor)

namespace MPSTensor

open scoped Matrix.Norms.Frobenius in
/-- Injectivity after blocking \(L\) sites at the base point suffices for
continuity of the actual local MPS ground-space projector. No injectivity
away from that point is assumed. -/
theorem continuousAt_map_groundSpace_starProjection_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {x₀ : X} (hA : ContinuousAt A x₀) (L : ℕ)
    (hInj : Kraus.IsNBlkInjective (A x₀) L) :
    ContinuousAt (fun x => ((groundSpace (A x) L).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap).starProjection) x₀ := by
  have hT : ContinuousAt (fun x => groundSpaceMapES (A x) L) x₀ :=
    (continuous_groundSpaceMapES_family
      (fun B : MPSTensor d D => B) continuous_id L).continuousAt.comp hA
  have hproj := ContinuousLinearMap.continuousAt_range_starProjection_of_injective
    (fun x => groundSpaceMapES (A x) L) hT
    (show Function.Injective (groundSpaceMapES (A x₀) L) from
      (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) L)).symm.injective.comp
        ((groundSpaceMap_injective_of_isNBlkInjective hInj).comp
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm.injective))
  simpa only [range_groundSpaceMapES] using hproj

/-- The matrix of the actual canonical interaction on \(L\) sites is continuous when the tensor
family is continuous and injective after blocking \(L\) sites at the base point. -/
theorem continuousAt_toMatrix'_parentInteraction_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {x₀ : X} (hA : ContinuousAt A x₀) (L : ℕ)
    (hInj : Kraus.IsNBlkInjective (A x₀) L) :
    ContinuousAt (fun x => LinearMap.toMatrix' (parentInteraction (A x) L)) x₀ := by
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d L) (Cfg d L) ℂ ≃⋆ₐ[ℂ] _).symm
  have he : Continuous e := e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have heq : (fun x => LinearMap.toMatrix' (parentInteraction (A x) L)) =
      fun x => e (1 - ((groundSpace (A x) L).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection) := by
    funext x
    rw [← toEuclideanCLM_toMatrix'_parentInteraction, StarAlgEquiv.symm_apply_apply]
  rw [heq]
  exact he.continuousAt.comp (continuousAt_const.sub
    (continuousAt_map_groundSpace_starProjection_of_isNBlkInjective A hA L hInj))

/-- The explicit uncle interaction on the original two physical sites: the matrix of the
canonical one-site parent projector of the blocked uncle tensor, read in the coordinates of the
two original sites. -/
noncomputable def uncleInteraction {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) : Matrix (Cfg d 2) (Cfg d 2) ℂ :=
  (LinearMap.toMatrix' (parentInteraction (uncleTensor A B R L) 1)).submatrix
    (Kraus.blockedConfigEquiv d 1 2).symm (Kraus.blockedConfigEquiv d 1 2).symm

private theorem toEuclideanLin_submatrix_blockedConfigEquiv_apply {d D : ℕ}
    (T : MPSTensor (Kraus.blockPhysDim d 2) D) (v : EuclideanSpace ℂ (Cfg d 2)) :
    Matrix.toEuclideanLin ((LinearMap.toMatrix' (parentInteraction T 1)).submatrix
        (Kraus.blockedConfigEquiv d 1 2).symm (Kraus.blockedConfigEquiv d 1 2).symm) v =
      blockedConfigLinearIsometryEquiv d 1 2
        (((groundSpace T 1).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)ᗮ.starProjection
          ((blockedConfigLinearIsometryEquiv d 1 2).symm v)) := by
  have hP : ((groundSpace T 1).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)ᗮ.starProjection
      ((blockedConfigLinearIsometryEquiv d 1 2).symm v) =
      Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction T 1))
        ((blockedConfigLinearIsometryEquiv d 1 2).symm v) := by
    rw [toEuclideanLin_toMatrix'_parentInteraction]
    rfl
  rw [hP]
  ext σ
  simp only [Matrix.toLpLin_apply, blockedConfigLinearIsometryEquiv_apply_apply, Matrix.mulVec,
    dotProduct, Matrix.submatrix_apply]
  refine Fintype.sum_equiv (Kraus.blockedConfigEquiv d 1 2).symm _ _ fun ρ => ?_
  rw [blockedConfigLinearIsometryEquiv_symm_apply_apply, Equiv.apply_symm_apply]

/-- The uncle interaction acts as the orthogonal projection onto the complement of the one-site
ground space of the blocked uncle tensor, transported along the physical-blocking isometry. -/
theorem toEuclideanLin_uncleInteraction_apply {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (v : EuclideanSpace ℂ (Cfg d 2)) :
    Matrix.toEuclideanLin (uncleInteraction A B R L) v =
      blockedConfigLinearIsometryEquiv d 1 2
        (((groundSpace (uncleTensor A B R L) 1).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap)ᗮ.starProjection
          ((blockedConfigLinearIsometryEquiv d 1 2).symm v)) :=
  toEuclideanLin_submatrix_blockedConfigEquiv_apply (uncleTensor A B R L) v

private theorem toMatrix'_parentInteraction_eq_uncleInterpolant_submatrix {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {ε : ℂ} (hε : ε ≠ 0) :
    LinearMap.toMatrix' (parentInteraction (twoBlockPerturbation A P B Q R L ε) 2) =
      (LinearMap.toMatrix' (parentInteraction (uncleTensorInterpolant A P B Q R L ε) 1)).submatrix
        (Kraus.blockedConfigEquiv d 1 2).symm (Kraus.blockedConfigEquiv d 1 2).symm := by
  have hG : groundSpace (uncleTensorInterpolant A P B Q R L ε) 1 =
      groundSpace (blockTensor (twoBlockPerturbation A P B Q R L ε) 2) 1 := by
    rw [← twoBlockVirtualScale_blockTensor A P B Q R L hε]
    exact groundSpace_twoBlockVirtualScale_one (inv_ne_zero hε) _
  apply Matrix.toEuclideanLin.injective
  ext v : 1
  rw [toEuclideanLin_submatrix_blockedConfigEquiv_apply, toEuclideanLin_toMatrix'_parentInteraction,
    hG]
  change ((groundSpace (twoBlockPerturbation A P B Q R L ε) 2).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap)ᗮ.starProjection v = _
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, LinearIsometryEquiv.apply_symm_apply]
  rw [starProjection_map_groundSpace_blockTensor_map_apply
    (twoBlockPerturbation A P B Q R L ε) 2 1]

/-- The two-block uncle interaction is the punctured operator-norm limit of
the actual canonical two-site parent interactions. Injectivity is assumed
only for the explicit limiting uncle tensor, exactly as in the source. -/
theorem tendsto_toMatrix'_parentInteraction_twoBlockPerturbation {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) :
    Filter.Tendsto (fun ε : ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ)
      (LinearMap.toMatrix' (parentInteraction (twoBlockPerturbation A P B Q R L ε) 2)))
      (𝓝[≠] 0) (𝓝 (Matrix.toEuclideanCLM (𝕜 := ℂ) (uncleInteraction A B R L))) := by
  have hInj : Kraus.IsNBlkInjective (uncleTensorInterpolant A P B Q R L 0) 1 := by
    rw [uncleTensorInterpolant_zero]
    exact Kraus.isNBlkInjective_one_of_isInjective hU
  have hP := continuousAt_toMatrix'_parentInteraction_of_isNBlkInjective
    (uncleTensorInterpolant A P B Q R L)
    (continuous_uncleTensorInterpolant A P B Q R L).continuousAt 1 hInj
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d 2) (Cfg d 2) ℂ ≃⋆ₐ[ℂ] _)
  have he : Continuous e := e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have hC : ContinuousAt (fun ε : ℂ => e
      ((LinearMap.toMatrix' (parentInteraction (uncleTensorInterpolant A P B Q R L ε) 1)).submatrix
        (Kraus.blockedConfigEquiv d 1 2).symm (Kraus.blockedConfigEquiv d 1 2).symm)) 0 :=
    he.continuousAt.comp ((Continuous.matrix_submatrix continuous_id _ _).continuousAt.comp hP)
  have hlim := hC.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [uncleTensorInterpolant_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [toMatrix'_parentInteraction_eq_uncleInterpolant_submatrix A P B Q R L hε]

/-- At every fixed periodic chain length, the actual canonical parent
Hamiltonian converges in operator norm to the Hamiltonian of the translates of the explicit
uncle interaction. This is the finite-chain uncle-Hamiltonian form theorem. -/
theorem tendsto_hamiltonian_parentRingInteraction_twoBlockPerturbation {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Filter.Tendsto (fun ε : ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ)
      (parentRingInteraction (twoBlockPerturbation A P B Q R L ε) 2 N).hamiltonian)
      (𝓝[≠] 0) (𝓝 (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (ManyBody.Interaction.translationInvariant N (uncleInteraction A B R L)).hamiltonian)) := by
  have : NeZero N := ⟨by omega⟩
  let e2 := (Matrix.toEuclideanCLM : Matrix (Cfg d 2) (Cfg d 2) ℂ ≃⋆ₐ[ℂ] _)
  let eN := (Matrix.toEuclideanCLM : Matrix (Cfg d N) (Cfg d N) ℂ ≃⋆ₐ[ℂ] _)
  let F : Matrix (Cfg d 2) (Cfg d 2) ℂ →ₗ[ℂ] Matrix (Cfg d N) (Cfg d N) ℂ :=
    IsLinearMap.mk' (fun h => (ManyBody.Interaction.translationInvariant N h).hamiltonian)
      ⟨fun h h' => by
        simp only [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hN,
          ManyBody.placeAlong_add, Finset.sum_add_distrib],
      fun c h => by
        simp only [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hN,
          ManyBody.placeAlong_smul, Finset.smul_sum]⟩
  have hF : Continuous fun T : EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) =>
      eN (F (e2.symm T)) :=
    (eN.toAlgEquiv.toLinearMap ∘ₗ F ∘ₗ
      e2.symm.toAlgEquiv.toLinearMap).continuous_of_finiteDimensional
  have hlim := (hF.tendsto _).comp
    (tendsto_toMatrix'_parentInteraction_twoBlockPerturbation A P B Q R L hU)
  simpa only [Function.comp_def, StarAlgEquiv.symm_apply_apply, e2, eN, F,
    IsLinearMap.mk'_apply] using hlim

/-- The same finite-chain uncle limit holds along real perturbation parameters,
with complex tensor entries and arbitrary diagonal perturbation blocks. -/
theorem tendsto_hamiltonian_parentRingInteraction_twoBlockPerturbation_real {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Filter.Tendsto (fun ε : ℝ => Matrix.toEuclideanCLM (𝕜 := ℂ)
      (parentRingInteraction (twoBlockPerturbation A P B Q R L (ε : ℂ)) 2 N).hamiltonian)
      (𝓝[≠] 0) (𝓝 (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (ManyBody.Interaction.translationInvariant N (uncleInteraction A B R L)).hamiltonian)) := by
  apply (tendsto_hamiltonian_parentRingInteraction_twoBlockPerturbation A P B Q R L hU hN).comp
  exact Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    fun ε hε => by simpa using hε

end MPSTensor
