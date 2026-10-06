/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicOpenParentGap
import TNLean.MPS.ParentHamiltonian.PeriodicQuasiLocalGroundStateGap

/-!
# One periodic parent interaction with finite and infinite-volume gaps

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
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 933--947, Lemma existenceinteraction, and Section 6.
-/

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
