/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTensor
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport

/-!
# The canonical parent limit for a two-block uncle tensor

This is the perturbative limit in arXiv:1210.6613, Theorem
`thm:unclehamiltonian`. The rescaled blocked tensor is a regular polynomial
family. Injectivity of its value at zero ensures continuity of its actual
range projector. Off-diagonal virtual rescaling preserves the physical
range away from zero, giving the punctured limit of the original parent.
-/

open scoped Matrix Topology

namespace MPSTensor

/-- Injectivity after blocking \(L\) sites at the base point suffices for
continuity of the actual local MPS ground-space projector. No injectivity
away from that point is assumed. -/
theorem continuousAt_groundSpaceES_starProjection_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {x₀ : X} (hA : ContinuousAt A x₀) (L : ℕ)
    (hInj : Kraus.IsNBlkInjective (A x₀) L) :
    ContinuousAt (fun x => (groundSpaceES (A x) L).starProjection) x₀ := by
  have hT : ContinuousAt (fun x => groundSpaceMapES (A x) L) x₀ :=
    (continuous_groundSpaceMapES_family
      (fun B : MPSTensor d D => B) continuous_id L).continuousAt.comp hA
  have hproj := ContinuousLinearMap.continuousAt_range_starProjection_of_injective
    (fun x => groundSpaceMapES (A x) L) hT
    (groundSpaceMapES_injective_of_isNBlkInjective hInj)
  simpa only [range_groundSpaceMapES] using hproj

/-- The actual canonical interaction on \(L\) sites is continuous when the
tensor family is continuous and injective after blocking \(L\) sites at the
base point. -/
theorem continuousAt_parentInteractionES_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {x₀ : X} (hA : ContinuousAt A x₀) (L : ℕ)
    (hInj : Kraus.IsNBlkInjective (A x₀) L) :
    ContinuousAt (fun x => LinearMap.toContinuousLinearMap
      (parentInteractionES (A x) L)) x₀ := by
  have h : ContinuousAt (fun x =>
      (1 : EuclideanSpace ℂ (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d L)) -
        (groundSpaceES (A x) L).starProjection) x₀ :=
    continuousAt_const.sub
      (continuousAt_groundSpaceES_starProjection_of_isNBlkInjective A hA L hInj)
  convert h using 1
  ext x v
  simp only [parentInteractionES, Submodule.starProjection_orthogonal]
  rfl

/-- The explicit uncle interaction on the original two physical sites: the
canonical one-site parent projector of the blocked uncle tensor, transported
back along the existing physical-blocking isometry. -/
noncomputable def uncleInteractionES {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  let e := (blockedConfigLinearIsometryEquiv d 1 2).toContinuousLinearEquiv
  e.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (parentInteractionES (uncleTensor A B R L) 1)).comp
      e.symm.toContinuousLinearMap)

private theorem parentInteractionES_eq_uncleInterpolant_conj {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {ε : ℂ} (hε : ε ≠ 0) :
    LinearMap.toContinuousLinearMap
      (parentInteractionES (twoBlockPerturbation A P B Q R L ε) 2) =
      let e := (blockedConfigLinearIsometryEquiv d 1 2).toContinuousLinearEquiv
      e.toContinuousLinearMap.comp
        ((LinearMap.toContinuousLinearMap
          (parentInteractionES (uncleTensorInterpolant A P B Q R L ε) 1)).comp
            e.symm.toContinuousLinearMap) := by
  have hG : groundSpace (uncleTensorInterpolant A P B Q R L ε) 1 =
      groundSpace (blockTensor (twoBlockPerturbation A P B Q R L ε) 2) 1 := by
    rw [← twoBlockVirtualScale_blockTensor A P B Q R L hε]
    exact groundSpace_twoBlockVirtualScale_one (inv_ne_zero hε) _
  have hGES : groundSpaceES (uncleTensorInterpolant A P B Q R L ε) 1 =
      groundSpaceES (blockTensor (twoBlockPerturbation A P B Q R L ε) 2) 1 := by
    simp only [groundSpaceES, hG]
  apply ContinuousLinearMap.ext
  intro v
  change (groundSpaceES (twoBlockPerturbation A P B Q R L ε) 2)ᗮ.starProjection v =
    blockedConfigLinearIsometryEquiv d 1 2
      ((groundSpaceES (uncleTensorInterpolant A P B Q R L ε) 1)ᗮ.starProjection
        ((blockedConfigLinearIsometryEquiv d 1 2).symm v))
  rw [hGES]
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, LinearIsometryEquiv.apply_symm_apply]
  rw [starProjection_groundSpaceES_blockTensor_map_apply
    (twoBlockPerturbation A P B Q R L ε) 2 1]

/-- The two-block uncle interaction is the punctured operator-norm limit of
the actual canonical two-site parent interactions. Injectivity is assumed
only for the explicit limiting uncle tensor, exactly as in the source. -/
theorem tendsto_parentInteractionES_twoBlockPerturbation {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) :
    Filter.Tendsto (fun ε : ℂ => LinearMap.toContinuousLinearMap
      (parentInteractionES (twoBlockPerturbation A P B Q R L ε) 2))
      (𝓝[≠] 0) (𝓝 (uncleInteractionES A B R L)) := by
  have hInj : Kraus.IsNBlkInjective (uncleTensorInterpolant A P B Q R L 0) 1 := by
    rw [uncleTensorInterpolant_zero]
    exact Kraus.isNBlkInjective_one_of_isInjective hU
  have hP := continuousAt_parentInteractionES_of_isNBlkInjective
    (uncleTensorInterpolant A P B Q R L)
    (continuous_uncleTensorInterpolant A P B Q R L).continuousAt 1 hInj
  let e := (blockedConfigLinearIsometryEquiv d 1 2).toContinuousLinearEquiv
  have hC : ContinuousAt (fun ε : ℂ => e.toContinuousLinearMap.comp
      ((LinearMap.toContinuousLinearMap
        (parentInteractionES (uncleTensorInterpolant A P B Q R L ε) 1)).comp
          e.symm.toContinuousLinearMap)) 0 :=
    continuousAt_const.clm_comp (hP.clm_comp continuousAt_const)
  have hlim := hC.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [uncleTensorInterpolant_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (parentInteractionES_eq_uncleInterpolant_conj A P B Q R L hε).symm

/-- The periodic uncle Hamiltonian formed by translating the explicit local
uncle projector. The existing cyclic restriction/adjoint formula embeds each
local term, with the same normalization as the canonical parent Hamiltonian. -/
noncomputable def uncleHamiltonianES {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →L[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : Fin N, (((d ^ 2 : ℕ) : ℂ)⁻¹) • ∑ τ : Cfg d N,
    (LinearMap.toContinuousLinearMap
      ((cyclicRestrictES (d := d) (Fin.pos i) 2 i τ).adjoint)).comp
        ((uncleInteractionES A B R L).comp
          (LinearMap.toContinuousLinearMap
            (cyclicRestrictES (d := d) (Fin.pos i) 2 i τ)))

/-- At every fixed periodic chain length, the actual canonical parent
Hamiltonian converges in operator norm to the sum of the explicit uncle
projectors. This is the finite-chain uncle-Hamiltonian form theorem. -/
theorem tendsto_parentHamiltonianES_twoBlockPerturbation {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) {N : ℕ} (hN : 2 ≤ N) :
    Filter.Tendsto (fun ε : ℂ => LinearMap.toContinuousLinearMap
      (parentHamiltonianES (twoBlockPerturbation A P B Q R L ε) 2 N))
      (𝓝[≠] 0) (𝓝 (uncleHamiltonianES A B R L N)) := by
  have hP := tendsto_parentInteractionES_twoBlockPerturbation A P B Q R L hU
  have hloc (i : Fin N) (τ : Cfg d N) :=
    ((continuous_const : Continuous fun H :
      EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) =>
      LinearMap.toContinuousLinearMap
        ((cyclicRestrictES (d := d) (Fin.pos i) 2 i τ).adjoint)).clm_comp
          (continuous_id.clm_comp (continuous_const : Continuous fun _ :
            EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) =>
            LinearMap.toContinuousLinearMap
              (cyclicRestrictES (d := d) (Fin.pos i) 2 i τ)))).continuousAt.tendsto.comp hP
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℂ => (((d ^ 2 : ℕ) : ℂ)⁻¹)) (𝓝[≠] 0) _).smul
        (tendsto_finsetSum Finset.univ fun τ _ => hloc i τ)
  convert hsum using 1
  · funext ε
    rw [parentHamiltonianES_eq_sum_localTermES]
    apply ContinuousLinearMap.ext
    intro v
    change (∑ i : Fin N, localTermES (twoBlockPerturbation A P B Q R L ε) 2 i) v = _
    simp only [LinearMap.sum_apply, sum_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [localTermES_eq_average_localTermESSummand _ hN i]
    simp [localTermESSummand]
  · rfl

/-- The same finite-chain uncle limit holds along real perturbation parameters,
with complex tensor entries and arbitrary diagonal perturbation blocks. -/
theorem tendsto_parentHamiltonianES_twoBlockPerturbation_real {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hU : Kraus.IsInjective (uncleTensor A B R L)) {N : ℕ} (hN : 2 ≤ N) :
    Filter.Tendsto (fun ε : ℝ => LinearMap.toContinuousLinearMap
      (parentHamiltonianES (twoBlockPerturbation A P B Q R L (ε : ℂ)) 2 N))
      (𝓝[≠] 0) (𝓝 (uncleHamiltonianES A B R L N)) := by
  apply (tendsto_parentHamiltonianES_twoBlockPerturbation A P B Q R L hU hN).comp
  exact Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    fun ε hε => by simpa using hε

end MPSTensor
