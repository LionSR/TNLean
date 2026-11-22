/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowJointProjectionDecay
import TNLean.MPS.ParentHamiltonian.Blocking.ResidueCoverGapCriterion
import QICLean.Spectral.Gap.OrthogonalKernelGap
import TNLean.MPS.ParentHamiltonian.Periodic.PeriodicBlockFamilyQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicOriginalIntersection

/-!
# A periodic tensor has a uniform original-chain open-parent gap

The canonical interaction range is chosen from the original cyclic
intersection. The residual cover projection estimate gives a uniform gap
at all sufficiently large volumes, including every residue modulo the
period. Finite-dimensional spectral bounds at the remaining finitely many
volumes give one constant for every volume. The gap is taken on the
complement of the actual Hamiltonian kernel, including below the interaction
range, where the Hamiltonian vanishes.

**Scope restriction (periodic tensor presentation):** The results concern
an explicitly supplied normalized periodic tensor. The passage from a
general GVBS presentation to this tensor presentation remains separate;
see docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma commutation (ii), equations (3.12)--(3.16), and Section 6.

## One periodic parent interaction with finite and infinite-volume gaps

A normalized periodic tensor supplies one positive original-chain interaction
whose open kernels are its boundary spaces above the chosen range. The same
interaction has a uniform norm gap on the actual finite-chain kernel
complement at every volume and a common infinite-volume commutator gap in
all pure zero-energy states. The latter conclusion uses the literal interval
commutators along any exhaustion with both margins diverging. The finite and
infinite-volume constants are allowed to differ.

**Scope restriction (periodic tensor presentation):** The result concerns an
explicit normalized periodic tensor. The passage from a general GVBS
presentation to this tensor presentation remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 933--947, Lemma existenceinteraction, and Section 6.

## A positive original-chain parent interaction and its infinite-volume gap

A normalized periodic tensor admits a positive finite-range interaction whose
open-chain kernel is its MPS boundary space at every volume at least the
interaction range. The same interaction has one positive infinite-volume
commutator gap in every pure zero-energy state, along every interval
exhaustion for which both margins diverge.

The interaction range and matrix are derived from the original cyclic
intersection. The primitive blocked sectors and their faithful invariant
matrices are derived when proving the gap. Periodicity also forces a nonzero
physical dimension, so that no dimension, interaction, kernel, or density
witness is supplied separately.

**Scope restriction (periodic tensor presentation):** The result concerns an
explicit normalized periodic tensor. Identifying the support spaces of a
general GVBS presentation with these MPS spaces remains separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
This theorem makes no assertion of a finite-chain gap for every residue.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma existenceinteraction, and Section 6.
-/

section

open scoped ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- Periodicity alone derives a canonical original-chain interaction range,
exact open kernels above that range, and one norm gap at every volume.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma commutation (ii), and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_pos_openParentHamiltonianES_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ N, ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨R, hR, hKernel, N₀, _hRN, δ, hδ, hGap⟩ :=
    hA.exists_pos_openParentHamiltonianES_gap_of_residue_cover_limit
      hA.residual_cover_projection_defect_tendsto_zero
  obtain ⟨γ, hγ, hAll⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖)
    (fun N γ η hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N => LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES A R N)) hδ hGap
  exact ⟨R, hR, hKernel, γ, hγ, hAll⟩

/-- A normalized periodic tensor admits a positive local matrix interaction
with exact original-chain open kernels and one norm gap at every volume.
No interaction, faithful invariant matrix, or sector separation is supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma existenceinteraction, and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_positive_parent_interaction_uniform_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖ := by
  obtain ⟨R, hR, hKernel, δ, hδ, hGap⟩ := hA.exists_pos_openParentHamiltonianES_gap
  refine ⟨R, hR, canonicalParentInteractionMatrix A R,
    canonicalParentInteractionMatrix_posSemidef A R, ?_, δ, hδ, ?_⟩
  · simpa only [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR] using hKernel
  · simpa only [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR] using hGap

end MPSTensor

end

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D m : ℕ}
/-- Periodicity derives one positive original-chain interaction with exact
kernels above its range, a uniform finite-chain norm gap at every volume, and
a common literal infinite-volume commutator gap in every pure zero-energy
state. The same interaction is used for both gaps. Neither interaction,
dimension, support, density nor convergence data are supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 933--947, Lemma existenceinteraction, and Section 6, in the explicit
normalized periodic tensor setting. -/
theorem IsPeriodic.exists_positive_parent_interaction_finite_and_quasiLocal_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A)
    : let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  (openInteractionMatrix h ((ℓ n + k) + r n)) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨R, hR, h, hh, hKernel, δ, hδ, hFinite⟩ :=
    hA.exists_positive_parent_interaction_uniform_gap
  have hEventual : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N :=
    (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hQuasi⟩ :=
    hA.exists_pos_quasiLocalCommutator_limit_gap_of_eventual_kernel h hR hh hEventual
  exact ⟨R, hR, h, hh, hKernel, δ, hδ, hFinite, γ, hγ, hQuasi⟩
end MPSTensor

end

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D m : ℕ}

/-- Periodicity alone derives a positive original-chain parent interaction
with exact open kernels for every \(N\ge R\) and a common positive
infinite-volume gap in all pure zero-energy states. The gap constant precedes
all states, observables, filters, and interval margins.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma existenceinteraction, and Section 6, in the explicit periodic tensor
setting. -/
theorem IsPeriodic.exists_positive_parent_interaction_quasiLocalCommutator_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A)
    : let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N) ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  (openInteractionMatrix h ((ℓ n + k) + r n)) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨R, hR, h, hh, hKernel⟩ := hA.exists_positive_parent_interaction
  have hEventual : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N :=
    (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ :=
    hA.exists_pos_quasiLocalCommutator_limit_gap_of_eventual_kernel h hR hh hEventual
  exact ⟨R, hR, h, hh, hKernel, γ, hγ, hGap⟩
end MPSTensor

end
