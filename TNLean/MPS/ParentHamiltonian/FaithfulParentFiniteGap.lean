/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyOpenParentGap
import TNLean.MPS.ParentHamiltonian.FaithfulPeriodicGroundSpace
import TNLean.MPS.ParentHamiltonian.CanonicalGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.FaithfulQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.CanonicalParentGroundState
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionExistence

/-!
# Finite and infinite parent gaps for faithful stationary generators

Normalized tensors with a faithful stationary matrix admit exact canonical
parent kernels at every sufficiently large interaction range. The same
canonical interaction has a uniform finite-volume norm gap at every original
length, and a common literal infinite-volume commutator gap in all pure
zero-energy states. The generated stationary state itself has zero energy;
its purity is not assumed.

**Scope restriction (supplied stationary generators):** The normalized
tensor and faithful stationary matrix are supplied. Their construction from
an arbitrary GVBS boundary-limit presentation remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma `existenceinteraction`, lines 2195--2230, and Section 6.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- Faithful stationary normalized generators give exact canonical kernels
at all sufficiently large interaction ranges and one norm gap at every
original volume for each such range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6,
in the supplied generating-data setting. -/
theorem exists_openParentHamiltonianES_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    ∃ R₀, 0 < R₀ ∧ ∀ R, R₀ ≤ R →
      (∀ N, R ≤ N →
        LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N,
        ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨b, _hb, dim, _hdim, B, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  obtain ⟨R₀, hR₀, hFamily⟩ := exists_openParentHamiltonianES_gap_of_periodic_family
    (fun _ => 1) B (fun _ => one_ne_zero) m hPeriodic
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨hKernel, δ, hδ, hGap⟩ := hFamily R hR
  have hH := openParentHamiltonianES_eq_of_groundSpaceES_eq (hR₀.trans_le hR) (hGS R)
  refine ⟨fun N hN => ?_, δ, hδ, fun N v hv => ?_⟩
  · rw [hH N, hKernel N hN]
    exact (hGS N).symm
  · rw [hH N] at hv ⊢
    exact hGap N v hv

/-- One constructed parent interaction has exact open kernels, contains the
generated stationary state in its zero-energy face, and has both an all-length
finite-volume gap and a common literal infinite-volume commutator gap in every
pure zero-energy state. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorems 1.1--1.2 and Section 6, in the supplied generating-data setting. -/
theorem exists_positive_parent_finite_and_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) ∧
      quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) ∈
        parentGroundStateFace h ∧
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
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  change (∑ i, (A i)ᴴ * A i) = 1 at hA
  obtain ⟨R, hR, hRange⟩ :=
    exists_openParentHamiltonianES_gap_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  obtain ⟨hCanonicalKernel, δ, hδ, hFinite⟩ := hRange R le_rfl
  obtain ⟨h, hEq, hh, hKernel⟩ :=
    exists_positive_canonical_parent_interaction_of_exact_open_kernels A hR hCanonicalKernel
  have hH (N : ℕ) : openInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      openParentHamiltonianES A R N := by
    rw [hEq, toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR]
  have hMember : quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) ∈
      parentGroundStateFace h := by
    rw [hEq]
    exact quasiLocalExpectation_mem_parentGroundStateFace_canonicalParentInteraction
      A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) R
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh ((eventually_ge_atTop R).mono fun N hN => hKernel N hN)
  refine ⟨R, hR, h, hh, hKernel, hMember, δ, hδ, ?_, γ, hγ, hGap⟩
  simpa only [hH] using hFinite

end MPSTensor
