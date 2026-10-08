/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicFamilyInteractionCriterion
import TNLean.MPS.ParentHamiltonian.PeriodicSectorRepresentatives
import TNLean.MPS.ParentHamiltonian.PeriodicGroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.CanonicalGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionExistence

/-!
# Canonical interactions and pure-state gaps for periodic families

A finite weighted family of normalized periodic tensors admits a canonical
parent interaction with exact joint open ground spaces at every sufficiently
large volume. Equivalent sectors can be discarded without changing any
finite ground space. The selected inequivalent family has independent middle
spaces on sufficiently large original intervals, so its individual one-step
intersection identities combine to give the joint identity.

The resulting interaction has a common literal infinite-volume commutator
gap in every pure zero-energy state. No translation invariance, primitive
presentation, sector separation, local interaction, or kernel identity is
supplied. The finite family may be empty.

**Scope restriction (tensor presentation):** These statements concern finite
weighted families of normalized periodic tensors. The passage from arbitrary
GVBS data to such tensor presentations remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
forintersection, Lemma existenceinteraction, Theorems 1.1--1.2, and
Section 6, lines 2649--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d b : ℕ} [NeZero d] {D : Fin b → ℕ}

/-- A finite weighted family of normalized periodic tensors has exact canonical
open kernels for every sufficiently large interaction range and every volume
at least that range. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 4, Proposition forintersection, and Lemma existenceinteraction.
Equivalent sectors are selected internally with equality at every length. -/
theorem exists_ker_openParentHamiltonianES_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks μ A) R N) =
        groundSpaceES (toTensorFromBlocks μ A) N := by
  obtain ⟨g, sel, hsel, hD, hP, hDistinct, hCover, hJoint⟩ :=
    exists_periodic_sector_representatives μ A hμ hPeriodic
  let B := fun j => A (sel j)
  have hIndep := eventually_groundSpaceES_iSupIndep_of_isPeriodic B
    (fun j => m (sel j)) hP hDistinct.forall_ne_transport
  obtain ⟨R₀, hR₀, hKernel⟩ := exists_ker_openParentHamiltonianES_of_periodic_family_independence
    (fun _ => 1) B (fun _ => one_ne_zero) (fun j => m (sel j)) hP
    (hIndep.mono fun n hn => (groundSpace_iSupIndep_iff_groundSpaceES_iSupIndep B n).mpr hn)
  refine ⟨R₀, hR₀, fun R N hR hRN => ?_⟩
  rw [openParentHamiltonianES_eq_of_groundSpaceES_eq (lt_of_lt_of_le hR₀ hR)
    (hJoint R) N, hJoint N]
  exact hKernel R N hR hRN

/-- A finite weighted family of normalized periodic tensors admits a positive
canonical interaction with exact joint open kernels. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 4 and Lemma existenceinteraction. Equivalent
sectors are removed internally without changing any finite ground space. -/
theorem exists_positive_parent_interaction_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks μ A) N := by
  obtain ⟨R, hR, hKernel⟩ := exists_ker_openParentHamiltonianES_of_periodic_family
    μ A hμ m hPeriodic
  obtain ⟨h, _heq, hh, hKernelInteraction⟩ :=
    exists_positive_canonical_parent_interaction_of_exact_open_kernels
      (toTensorFromBlocks μ A) hR (fun N => hKernel R N le_rfl)
  exact ⟨R, hR, h, hh, hKernelInteraction⟩

/-- A periodic family admits one canonical interaction and a common literal
infinite-volume commutator gap for all its pure zero-energy states. The constant
precedes all states, local observables, filters, and interval margins. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6. -/
theorem exists_positive_parent_interaction_quasiLocalCommutator_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks μ A) N) ∧
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
  obtain ⟨R, hR, h, hh, hKernel⟩ :=
    exists_positive_parent_interaction_of_periodic_family μ A hμ m hPeriodic
  have hEventual := (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hEventual
  exact ⟨R, hR, h, hh, hKernel, γ, hγ, hGap⟩

end MPSTensor
