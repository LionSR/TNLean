/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointPeriodicGap
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSwap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRightOpenTransport
import TNLean.MPS.ParentHamiltonian.Martingale.IsometricConjugationGap

/-!
# The actual joint periodic parent at the second endpoint

Physical sector exchange conjugates the actual periodic Hamiltonian to
the first-endpoint Hamiltonian of the reversed family. It also transports
the actual component MPS vectors with their common coefficient space.
The first-endpoint kernel and gap therefore give the corresponding
second-endpoint statements without a new phase-counting argument.

The second endpoint requires positive second-block dimensions only.
Taking the minimum of the two endpoint constants gives one bound valid
at both endpoints. Each endpoint constant comes from its common joint
canonical parent; there is no minimum over separate block gaps. No gap
over the intervening path is asserted.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped BigOperators InnerProductSpace Matrix

namespace MPSTensor

/-- A physical alphabet isometry conjugates the full periodic sum whenever
it conjugates the local interaction. Both oriented terms are retained on a
two-site ring, and zero or short chain spaces require no extra hypotheses. -/
theorem periodicInteractionHamiltonianES_physicalReindex_conj
    {d₁ d₂ R : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (h : EuclideanSpace ℂ (Cfg d₂ R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d₂ R)) (N : ℕ) :
    periodicInteractionHamiltonianES
        ((physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj h) N =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (periodicInteractionHamiltonianES h N) := by
  simp only [periodicInteractionHamiltonianES, periodicLocalInteractionES_physicalReindex_conj,
    map_sum]

namespace MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The actual periodic Hamiltonians for the original and reversed joint
families at reflected parameters are conjugate by physical sector exchange.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_eq_conj_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) (N : ℕ) :
    periodicInteractionHamiltonianES (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N =
      (physicalReindexLinearIsometryEquiv
        (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N).toLinearEquiv.conj
          (periodicInteractionHamiltonianES
            (jointMixedEndpointParentInteraction A₁ A₀ (1 - γ)).toLinearMap N) := by
  rw [jointMixedEndpointParentInteraction_eq_conj_reflect_swap,
    periodicInteractionHamiltonianES_physicalReindex_conj]

/-- Sector exchange transports every actual periodic component vector.
As a trace identity under a permutation, this includes length zero.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem mpv_jointMixedEndpointInterpolation_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ)
    (x : Fin r) (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    mpv (jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x)
        (fun i => jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁ (σ i)) =
      mpv (jointMixedEndpointInterpolation A₀ A₁ γ x) σ := by
  let e := jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap (D₀ x) (D₁ x))
  have hword (w : List (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))) :
      Kraus.evalWord (Kraus.reindexPhysical e
        (jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x)) w =
          Φ (Kraus.evalWord (jointMixedEndpointInterpolation A₀ A₁ γ x) w) := by
    induction w with
    | nil => simp only [Kraus.evalWord_nil, map_one]
    | cons p w ih =>
        rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih]
        change jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x (e p) * _ = _
        rw [jointMixedEndpointInterpolation_reflect_swap, map_mul]
  calc
    mpv (jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x) (fun i => e (σ i)) =
        mpv (Kraus.reindexPhysical e
          (jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x)) σ :=
      (mpv_reindexPhysical e _ σ).symm
    _ = mpv (jointMixedEndpointInterpolation A₀ A₁ γ x) σ := by
      change Matrix.trace (Kraus.evalWord _ (List.ofFn σ)) =
        Matrix.trace (Kraus.evalWord _ (List.ofFn σ))
      rw [hword]
      exact Matrix.trace_reindex (mixedEndpointBondSwap (D₀ x) (D₁ x)) _

/-- The full common periodic component map intertwines the physical
isometry. The same coefficient vector is retained for every block label.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockPeriodicMpvMapES_jointMixed_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) (N : ℕ)
    (c : EuclideanSpace ℂ (Fin r)) :
    physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N
      (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₁ A₀ (1 - γ)) N c) =
        blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ γ) N c := by
  apply PiLp.ext
  intro σ
  simp only [physicalReindexLinearIsometryEquiv_apply_apply, blockPeriodicMpvMapES_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [mpv_jointMixedEndpointInterpolation_reflect_swap]

/-- The actual parameter-one ground space is exactly the span of the
actual parameter-one component MPS vectors, including the two-site ring.
Only the second endpoint block dimensions must be positive.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_one_eq_actual
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₁ : ∀ x, 0 < D₁ x) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N) =
        (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 1) N).range := by
  let U := physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N
  have hConj : U.toLinearEquiv.conj (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₁ A₀ 0).toLinearMap N) =
        periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N := by
    simpa only [sub_self] using (jointMixedEndpoint_periodic_eq_conj_reflect_swap A₀ A₁ 1 N).symm
  have hMap (c : EuclideanSpace ℂ (Fin r)) :
      U (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₁ A₀ 0) N c) =
        blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 1) N c := by
    simpa only [sub_self] using blockPeriodicMpvMapES_jointMixed_reflect_swap A₀ A₁ 1 N c
  rw [U.ker_eq_map_of_conj _ _ hConj,
    jointMixedEndpoint_periodic_groundSpace_eq_actual A₁ A₀ h₁ h₀ hD₁ hN]
  apply le_antisymm
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (hMap c).symm⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₁ A₀ 0) N c,
      ⟨c, rfl⟩, hMap c⟩

/-- Both actual endpoint kernels are the ranges of their actual component
MPS maps. Empty labels and zero physical alphabets remain included.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_endpoints_eq_actual
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x)
    (γ : ℝ) (hγ : γ = 0 ∨ γ = 1) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N) =
        (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ γ) N).range := by
  rcases hγ with rfl | rfl
  · exact jointMixedEndpoint_periodic_groundSpace_eq_actual A₀ A₁ h₀ h₁ hD₀ hN
  · exact jointMixedEndpoint_periodic_groundSpace_one_eq_actual A₀ A₁ h₀ h₁ hD₁ hN

/-- The actual second periodic endpoint has a strictly positive uniform
gap, derived from the first endpoint of the reversed family with the same
gap constant. No positivity of the first block dimensions is required.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem exists_uniform_jointMixedEndpoint_periodic_one_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₁ : ∀ x, 0 < D₁ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N v‖ := by
  obtain ⟨δ, hδ, hGap⟩ := exists_uniform_jointMixedEndpoint_periodic_gap A₁ A₀ h₁ h₀ hD₁
  refine ⟨δ, hδ, ?_⟩
  intro N hN
  let U := physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N
  apply (U.norm_gap_iff_of_conj _ _ ?_ δ).mp (hGap N hN)
  simpa only [sub_self] using (jointMixedEndpoint_periodic_eq_conj_reflect_swap A₀ A₁ 1 N).symm

/-- One strictly positive constant bounds both actual periodic endpoints,
uniformly over rings of at least two sites. This is a minimum of two
common-parent endpoint bounds, and asserts no gap between the endpoints.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem exists_uniform_jointMixedEndpoint_periodic_endpoints_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ, γ = 0 ∨ γ = 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  obtain ⟨δ₀, hδ₀, hGap₀⟩ := exists_uniform_jointMixedEndpoint_periodic_gap A₀ A₁ h₀ h₁ hD₀
  obtain ⟨δ₁, hδ₁, hGap₁⟩ := exists_uniform_jointMixedEndpoint_periodic_one_gap A₀ A₁ h₀ h₁ hD₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro γ (rfl | rfl) N hN v hv
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans
      (hGap₀ N hN v hv)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans
      (hGap₁ N hN v hv)

end MPOSymmetry
end MPSTensor
