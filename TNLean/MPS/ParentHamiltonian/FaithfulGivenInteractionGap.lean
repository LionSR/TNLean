/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FaithfulParentFiniteGap
import TNLean.MPS.ParentHamiltonian.Martingale.CanonicalGapToInteractionGap

/-!
# Gaps for a given interaction with faithful stationary generators

Every positive interaction of positive range whose eventual open kernels are
the boundary spaces of supplied faithful stationary normalized generators
has a uniform finite-volume gap at every original chain length. The same
given interaction also has a common literal infinite-volume commutator gap
in every pure zero-energy state. The local kernel is not assumed to equal the
boundary space at the interaction range.

**Scope restriction (supplied stationary generators):** The generators are
supplied; their construction from an arbitrary GVBS boundary-limit
presentation remains separate. See
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, and Section 6, lines 2593--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D R : ℕ}

/-- The supplied interaction's eventual exact boundary kernels suffice for
an all-length norm gap. No local kernel condition is added. Source:
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
in the supplied faithful generating-data setting. -/
theorem exists_given_interaction_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖ := by
  obtain ⟨R₀, hR₀, hCanonical⟩ :=
    exists_openParentHamiltonianES_gap_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  exact exists_openInteractionHamiltonianES_gap_of_canonical_gaps_of_eventual_kernel
    A hR₀ hCanonical (Matrix.toEuclideanLin h) hR
    (Matrix.isPositive_toEuclideanLin_iff.mpr hh) hKernel

/-- The same given positive interaction has a uniform finite norm gap and
one literal infinite-volume commutator gap in every pure zero-energy state.
Only its eventual exact open kernels are supplied. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 6,
in the supplied faithful generating-data setting. -/
theorem exists_given_interaction_finite_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
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
  obtain ⟨δ, hδ, hFinite⟩ :=
    exists_given_interaction_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh hKernel
  obtain ⟨γ, hγ, hInfinite⟩ :=
    exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh hKernel
  exact ⟨δ, hδ, hFinite, γ, hγ, hInfinite⟩

end MPSTensor
