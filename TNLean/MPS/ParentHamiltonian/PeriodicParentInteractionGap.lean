/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicQuasiLocalGroundStateGap
import TNLean.MPS.ParentHamiltonian.PeriodicOriginalIntersection
/-!
# A positive original-chain parent interaction and its infinite-volume gap

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
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
This theorem makes no assertion of a finite-chain gap for every residue.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma existenceinteraction, and Section 6.
-/

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
