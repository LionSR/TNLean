/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSwap

/-!
# Actual open-Hamiltonian transport between the mixed endpoints

A bijection of the physical alphabet commutes with taking a local window
and with extending a local operator by the spectator identity. Consequently
the actual nonwrapping Hamiltonian is conjugated by the full-chain physical
reindexing isometry whenever its local interaction is conjugated by the
corresponding local isometry.

The explicit sector exchange therefore identifies the actual second
endpoint open Hamiltonian with the first endpoint of the reversed tensor
pair. No support, kernel, reduction, or spectral-gap hypothesis is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped BigOperators

namespace MPSTensor

noncomputable section

variable {d₁ d₂ R N : ℕ}

/-- Reindexing physical letters commutes with replacement of a cyclic
window, including the unchanged spectator sites. -/
theorem reindex_cyclicCfg
    (e : Fin d₁ ≃ Fin d₂) (i : Fin N) (ω : Cfg d₁ R) (τ : Cfg d₁ N) :
    (fun k => e (cyclicCfg (Fin.pos i) R i ω τ k)) =
      cyclicCfg (Fin.pos i) R i (fun r => e (ω r)) (fun k => e (τ k)) := by
  funext k
  simp only [cyclicCfg]
  split_ifs <;> rfl

/-- The actual cyclic window restriction intertwines physical alphabet
reindexing with its shorter-window counterpart. -/
theorem cyclicRestrictES_physicalReindex
    (e : Fin d₁ ≃ Fin d₂) (i : Fin N) (τ : Cfg d₁ N)
    (v : EuclideanSpace ℂ (Cfg d₂ N)) :
    cyclicRestrictES (Fin.pos i) R i τ (physicalReindexLinearIsometryEquiv e N v) =
      physicalReindexLinearIsometryEquiv e R
        (cyclicRestrictES (Fin.pos i) R i (fun k => e (τ k)) v) := by
  apply PiLp.ext
  intro ω
  change v (fun k => e (cyclicCfg (Fin.pos i) R i ω τ k)) =
    v (cyclicCfg (Fin.pos i) R i (fun r => e (ω r)) (fun k => e (τ k)))
  rw [reindex_cyclicCfg]

private theorem localInteraction_apply_cyclicRestriction
    {d : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    periodicLocalInteractionES h i v σ =
      h (cyclicRestrictES (Fin.pos i) R i σ v) (extractWindow R i σ) := by
  rw [periodicLocalInteractionES_apply_fiber h hRN]
  change h (WithLp.toLp 2 fun ω => v
    ((cyclicActiveBlockConfigEquiv d R hRN i).symm
      (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2))) (extractWindow R i σ) = _
  congr 1
  apply PiLp.ext
  intro ω
  change v ((cyclicActiveBlockConfigEquiv d R hRN i).symm
    (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2)) =
      v (cyclicCfg (Fin.pos i) R i ω σ)
  rw [cyclicCfg_eq_join_cyclicActiveBlock hRN]

/-- Extending a conjugated local interaction intertwines with the original
extension under the actual full-chain physical reindexing isometry. -/
theorem periodicLocalInteractionES_physicalReindex_apply
    (e : Fin d₁ ≃ Fin d₂)
    (h : EuclideanSpace ℂ (Cfg d₂ R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d₂ R))
    (i : Fin N) (v : EuclideanSpace ℂ (Cfg d₂ N)) :
    periodicLocalInteractionES
        ((physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj h) i
        (physicalReindexLinearIsometryEquiv e N v) =
      physicalReindexLinearIsometryEquiv e N (periodicLocalInteractionES h i v) := by
  by_cases hRN : R ≤ N
  · apply PiLp.ext
    intro σ
    rw [localInteraction_apply_cyclicRestriction _ hRN, cyclicRestrictES_physicalReindex]
    change physicalReindexLinearIsometryEquiv e R
        (h ((physicalReindexLinearIsometryEquiv e R).symm
          (physicalReindexLinearIsometryEquiv e R
            (cyclicRestrictES (Fin.pos i) R i (fun k => e (σ k)) v))))
        (extractWindow R i σ) =
      periodicLocalInteractionES h i v (fun k => e (σ k))
    rw [LinearIsometryEquiv.symm_apply_apply,
      physicalReindexLinearIsometryEquiv_apply_apply,
      localInteraction_apply_cyclicRestriction _ hRN]
  · simp [periodicLocalInteractionES, hRN]

/-- Physical alphabet reindexing conjugates the actual translated local
operator. This also covers interaction lengths exceeding the chain length,
where both extensions are zero by definition. -/
theorem periodicLocalInteractionES_physicalReindex_conj
    (e : Fin d₁ ≃ Fin d₂)
    (h : EuclideanSpace ℂ (Cfg d₂ R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d₂ R))
    (i : Fin N) :
    periodicLocalInteractionES
        ((physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj h) i =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (periodicLocalInteractionES h i) := by
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (physicalReindexLinearIsometryEquiv e N).surjective v
  change periodicLocalInteractionES
      ((physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj h) i
      (physicalReindexLinearIsometryEquiv e N w) =
    physicalReindexLinearIsometryEquiv e N
      (periodicLocalInteractionES h i
        ((physicalReindexLinearIsometryEquiv e N).symm
          (physicalReindexLinearIsometryEquiv e N w)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact periodicLocalInteractionES_physicalReindex_apply e h i w

/-- The actual open sum is conjugated by the full-chain physical isometry
when its local interaction is conjugated by the local physical isometry. -/
theorem openInteractionHamiltonianES_physicalReindex_conj
    (e : Fin d₁ ≃ Fin d₂)
    (h : EuclideanSpace ℂ (Cfg d₂ R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d₂ R)) (N : ℕ) :
    openInteractionHamiltonianES
        ((physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj h) N =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (openInteractionHamiltonianES h N) := by
  simp only [openInteractionHamiltonianES, periodicLocalInteractionES_physicalReindex_conj,
    map_sum]

namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- Every actual second-endpoint local term is the sector-exchanged actual
first-endpoint term for the reversed pair, on the same physical window. -/
theorem mixedEndpoint_localInteraction_one_eq_conj_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (i : Fin N) :
    periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap i =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).toLinearEquiv.conj
        (periodicLocalInteractionES (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap i) := by
  rw [mixedEndpointParentInteraction_one_eq_conj_swap,
    periodicLocalInteractionES_physicalReindex_conj]

/-- The actual second-endpoint open Hamiltonian is the conjugate of the
actual first-endpoint open Hamiltonian for the reversed tensor pair. -/
theorem mixedEndpoint_openInteractionHamiltonian_one_eq_conj_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).toLinearEquiv.conj
        (openInteractionHamiltonianES (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap N) := by
  rw [mixedEndpointParentInteraction_one_eq_conj_swap,
    openInteractionHamiltonianES_physicalReindex_conj]

/-- Pointwise intertwining of the actual endpoint open Hamiltonians under
the concrete sector-exchange isometry. -/
theorem mixedEndpoint_openInteractionHamiltonian_one_apply_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg ((D₁ + D₀) * (D₁ + D₀)) N)) :
    openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N
        (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N v) =
      physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
        (openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap N v) := by
  rw [mixedEndpoint_openInteractionHamiltonian_one_eq_conj_swap]
  change physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
    (openInteractionHamiltonianES (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap N
      ((physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).symm
        (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

end MPOSymmetry

end

end MPSTensor
