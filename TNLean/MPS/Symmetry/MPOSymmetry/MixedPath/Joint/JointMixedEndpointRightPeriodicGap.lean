/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Joint.JointMixedEndpointPeriodicGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Joint.JointMixedEndpointSwap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointRightOpenTransport
import QICLean.Spectral.Gap.IsometricConjugationGap

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

open MPTensor

open scoped BigOperators InnerProductSpace Matrix ComplexOrder
open ManyBody.Interaction (translationInvariant)

namespace MPSTensor

/-- A physical alphabet isometry conjugates the Hamiltonian of the translates on the ring
whenever it conjugates the local matrix. Both oriented terms are retained on a two-site ring,
and short rings require no extra hypotheses. -/
theorem toEuclideanLin_hamiltonian_translationInvariant_physicalReindex_conj
    {d₁ d₂ R : ℕ} (e : Fin d₁ ≃ Fin d₂)
    {h' : Matrix (Cfg d₁ R) (Cfg d₁ R) ℂ} {h : Matrix (Cfg d₂ R) (Cfg d₂ R) ℂ}
    (hh : Matrix.toEuclideanLin h' =
      (physicalReindexLinearIsometryEquiv e R).toLinearEquiv.conj (Matrix.toEuclideanLin h))
    (N : ℕ) [NeZero N] :
    Matrix.toEuclideanLin (translationInvariant N h').hamiltonian =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (Matrix.toEuclideanLin (translationInvariant N h).hamiltonian) := by
  simp only [ManyBody.Interaction.hamiltonian, map_sum]
  exact Fintype.sum_congr _ _ fun i ↦
    toEuclideanLin_translationInvariant_term_physicalReindex_conj e hh i

namespace MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The Hamiltonians of the translates of the extended interactions of the original and
reversed joint families at reflected parameters are conjugate by physical sector exchange.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_eq_conj_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) (N : ℕ) [NeZero N] :
    Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian =
      (physicalReindexLinearIsometryEquiv
        (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N).toLinearEquiv.conj
          (Matrix.toEuclideanLin (translationInvariant N
            (jointMixedEndpointParentInteraction A₁ A₀ (1 - γ))).hamiltonian) :=
  toEuclideanLin_hamiltonian_translationInvariant_physicalReindex_conj _
    (jointMixedEndpointParentInteraction_eq_conj_reflect_swap A₀ A₁ γ) N

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
      rw [mpv_eq, mpv_eq, coeff_eq, coeff_eq, hword]
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

/-- The kernel of the Hamiltonian of the translates of the extended interaction at parameter
one is exactly the span of the actual parameter-one component MPS vectors, including the
two-site ring. Only the second endpoint block dimensions must be positive.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_one_eq_actual
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₁ : ∀ x, 0 < D₁ x) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) =
        (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 1) N).range := by
  have : NeZero N := ⟨by omega⟩
  let U := physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N
  have hConj : U.toLinearEquiv.conj (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian) =
        Matrix.toEuclideanLin
          (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian := by
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

/-- Both endpoint kernels of the Hamiltonian of the translates of the extended interaction are
the ranges of their actual component MPS maps. Empty labels and zero physical alphabets remain
included. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_endpoints_eq_actual
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x)
    (γ : ℝ) (hγ : γ = 0 ∨ γ = 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian) =
        (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ γ) N).range := by
  rcases hγ with rfl | rfl
  · exact jointMixedEndpoint_periodic_groundSpace_eq_actual A₀ A₁ h₀ h₁ hD₀ hN
  · exact jointMixedEndpoint_periodic_groundSpace_one_eq_actual A₀ A₁ h₀ h₁ hD₁ hN

/-- Every nonzero eigenvalue of the Hamiltonian of the translates of the extended interaction
at the second endpoint is at least one strictly positive constant, uniformly over rings of at
least two sites. The bound is derived from the first endpoint of the reversed family with the
same constant. No positivity of the first block dimensions is required.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem exists_uniform_jointMixedEndpoint_periodic_one_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₁ : ∀ x, 0 < D₁ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨δ, hδ, hGap⟩ := exists_uniform_jointMixedEndpoint_periodic_gap A₁ A₀ h₁ h₀ hD₁
  refine ⟨δ, hδ, ?_⟩
  intro N hN
  have : NeZero N := ⟨by omega⟩
  let U := physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) N
  have hPQ : U.toLinearEquiv.conj (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian) =
      Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian := by
    simpa only [sub_self] using (jointMixedEndpoint_periodic_eq_conj_reflect_swap A₀ A₁ 1 N).symm
  intro μ hμ
  exact hGap N hN μ ((ManyBody.hasEigenvalue_iff_of_intertwine U.toLinearEquiv
    (fun ψ ↦ (U.map_apply_eq_of_conj _ _ hPQ ψ).symm) μ).mp hμ)

/-- One strictly positive constant bounds the nonzero eigenvalues of the Hamiltonians of the
translates of the extended interaction at both endpoints, uniformly over rings of at least two
sites. This is a minimum of two common-parent endpoint bounds, and asserts no gap between the
endpoints. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem exists_uniform_jointMixedEndpoint_periodic_endpoints_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ, γ = 0 ∨ γ = 1 → ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨δ₀, hδ₀, hGap₀⟩ := exists_uniform_jointMixedEndpoint_periodic_gap A₀ A₁ h₀ h₁ hD₀
  obtain ⟨δ₁, hδ₁, hGap₁⟩ := exists_uniform_jointMixedEndpoint_periodic_one_gap A₀ A₁ h₀ h₁ hD₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro γ (rfl | rfl) N hN
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_left _ _) (hGap₀ N hN)
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_right _ _) (hGap₁ N hN)

end MPOSymmetry
end MPSTensor
