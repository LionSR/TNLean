/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyOpenParentGap
import TNLean.MPS.ParentHamiltonian.Martingale.CanonicalGapToInteractionGap
import TNLean.MPS.ParentHamiltonian.AllLengthOpenInteractionMatrix

/-!
# Gaps for a supplied positive interaction and a periodic family

Let a finite weighted family consist of normalized periodic tensors.
Every positive interaction of positive range whose open kernels eventually
equal the joint MPS boundary spaces has one norm gap at every original
volume, above its actual finite-volume kernel. The canonical all-range gap
and a finite-window comparison derive the gap of the supplied interaction.
No local-kernel identity at its interaction range is assumed.

For the same supplied interaction, the literal infinite-volume commutator
energies have a common positive lower bound in every pure zero-energy state,
along every exhaustion with divergent boundary margins. No translation
invariance of the classified state, sector inequivalence, invariant matrix,
primitive presentation, finite gap, or lower interaction-range bound is
supplied. The finite family may be empty.

**Scope restriction (tensor presentation):** These statements concern finite
weighted families of normalized periodic tensors. The passage from general
GVBS data to such tensor presentations remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 933--947, condition C1, and Section 6, lines 2593--2675.
-/

open Filter SpinChain
open scoped Matrix MatrixOrder ComplexOrder BigOperators Topology
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ}

/-- Every positive finite-range interaction with eventual joint open kernels
for a finite periodic family has a uniform gap at every original volume,
above the actual finite-volume kernel. No local parent-kernel identity or
interaction-range lower bound is required. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, condition C1,
and Section 6, lines 2593--2675. -/
theorem exists_openInteractionMatrix_gap_of_periodic_family_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h N) v‖ := by
  obtain ⟨R₀, hR₀, hCanonical⟩ := exists_openParentHamiltonianES_gap_of_periodic_family
    μ A hμ m hPeriodic
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_openInteractionHamiltonianES_gap_of_canonical_gaps_of_eventual_kernel
      (toTensorFromBlocks μ A) hR₀ hCanonical (Matrix.toEuclideanLin h) hR
      (Matrix.isPositive_toEuclideanLin_iff.mpr hh) hKernel
  refine ⟨δ, hδ, ?_⟩
  intro N
  simpa only [openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix_all h hR N]
    using hGap N


/-- One supplied positive interaction with eventual periodic-family open
kernels has both an all-length finite gap and a common literal infinite-volume
commutator gap for every pure zero-energy state. The constants precede all
states, observables, filters, and divergent margins. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6, lines 2593--2675. -/
theorem exists_finite_quasiLocal_gap_of_periodic_family_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h N) v‖) ∧
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
  obtain ⟨δ, hδ, hFinite⟩ :=
    exists_openInteractionMatrix_gap_of_periodic_family_of_eventual_kernel
      μ A hμ m hPeriodic h hR hh hKernel
  obtain ⟨γ, hγ, hInfinite⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hKernel
  exact ⟨δ, hδ, hFinite, γ, hγ, hInfinite⟩

end MPSTensor
