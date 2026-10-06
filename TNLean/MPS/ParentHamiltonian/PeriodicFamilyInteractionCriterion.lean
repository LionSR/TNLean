/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveFamilyIntersection
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionExistence

/-!
# A periodic-family interaction criterion

Individual normalized periodic tensors have the one-step intersection
property on all sufficiently large original intervals. If the original
middle ground spaces of a finite family are eventually independent, the
geometric joint-intersection criterion combines those identities. Contiguous
iteration constructs a positive canonical interaction with exact open kernels.
The same interaction has a common infinite-volume commutator gap in every pure
zero-energy state, along every exhaustion with diverging boundary margins.

**Scope restriction (periodic-family independence criterion):** Eventual
independence of the original family middle spaces is explicitly assumed.
This is a sufficient criterion, not the unrestricted periodic-family
existence theorem. Repeated equivalent sectors must first be removed by an
exact support-preserving selection before deriving this hypothesis.
The passage from general GVBS states to tensor support data also remains
separate; see `docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
`forintersection`, Lemma `existenceinteraction`, Theorems 1.1--1.2, and
Section 6, lines 2649--2675. No translation invariance of a state being
classified, supplied interaction, kernel identity, or finite gap is assumed.
-/


open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d b : ℕ} [NeZero d] {D : Fin b → ℕ}

/-- Eventual independence of the original middle ground spaces of a periodic
family gives exact canonical open kernels at every volume at least any
sufficiently large interaction range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 4, Proposition `forintersection`, and
Lemma `existenceinteraction`. Independence remains an explicit hypothesis. -/
theorem exists_ker_openParentHamiltonianES_of_periodic_family_independence
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hIndep : ∀ᶠ n in atTop, iSupIndep (fun j => groundSpace (A j) n)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks μ A) R N) =
        groundSpaceES (toTensorFromBlocks μ A) N := by
  apply exists_ker_openParentHamiltonianES_eq_groundSpaceES_of_eventually_restriction_intersection
  have hStep := eventually_iSup_groundSpace_restriction_intersection_of_independent_middle
    A hIndep (fun j => (hPeriodic j).exists_eventually_groundSpace_restriction_intersection.elim
      fun n₀ hn₀ => (eventually_ge_atTop n₀).mono fun n hn => hn₀ n hn)
  filter_upwards [hStep] with n hn
  simpa only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] using hn

/-- A periodic family with eventually independent original middle spaces
admits a positive canonical interaction with exact joint open kernels.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
in the explicitly stated periodic-family independence criterion. -/
theorem exists_positive_parent_interaction_of_periodic_family_independence
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hIndep : ∀ᶠ n in atTop, iSupIndep (fun j => groundSpace (A j) n)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks μ A) N := by
  obtain ⟨R, hR, hKernel⟩ := exists_ker_openParentHamiltonianES_of_periodic_family_independence
    μ A hμ m hPeriodic hIndep
  obtain ⟨h, _heq, hh, hKernelInteraction⟩ :=
    exists_positive_canonical_parent_interaction_of_exact_open_kernels
      (toTensorFromBlocks μ A) hR (fun N => hKernel R N le_rfl)
  exact ⟨R, hR, h, hh, hKernelInteraction⟩

/-- Eventual middle-space independence constructs one canonical interaction
and a common literal infinite-volume commutator gap for all pure zero-energy
states of a periodic family. The constant precedes all states, local
observables, filters, and interval margins. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6, in the stated
periodic-family independence criterion. -/
theorem exists_positive_parent_interaction_quasiLocalCommutator_gap_of_periodic_family_independence
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hIndep : ∀ᶠ n in atTop, iSupIndep (fun j => groundSpace (A j) n)) :
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
    exists_positive_parent_interaction_of_periodic_family_independence μ A hμ m hPeriodic hIndep
  have hEventual := (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hEventual
  exact ⟨R, hR, h, hh, hKernel, γ, hγ, hGap⟩

end MPSTensor

