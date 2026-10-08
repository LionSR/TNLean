/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyParentInteractionGap
import TNLean.MPS.ParentHamiltonian.CanonicalGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.FaithfulQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.CanonicalParentGroundState

/-!
# Constructed parent interactions for faithful stationary generators

A normalized tensor with a faithful stationary matrix has a finite periodic
presentation of every boundary space. The periodic family intersection
therefore constructs an exact canonical parent interaction for the original
tensor. The same interaction has a common positive infinite-volume commutator
gap in every pure zero-energy state. Neither an interaction nor an eventual
kernel identity is supplied.

**Scope restriction (supplied stationary generators):** The tensor and its
faithful stationary matrix are supplied. Constructing them from an arbitrary
GVBS boundary-limit presentation remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Section 3, lines 1394--1483, Lemma existenceinteraction, lines 2195--2230,
and Section 6, lines 2649--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- Faithful stationary normalized generators have exact canonical open
kernels at every volume at least any sufficiently large interaction range.
No irreducibility, periodicity, or kernel identity is supplied. Source:
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1, Lemma existenceinteraction,
lines 2195--2230, in the supplied generating-data setting. -/
theorem exists_ker_openParentHamiltonianES_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨b, _hb, dim, _hdim, B, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  obtain ⟨R₀, hR₀, hKernel⟩ := exists_ker_openParentHamiltonianES_of_periodic_family
    (fun _ => 1) B (fun _ => one_ne_zero) m hPeriodic
  refine ⟨R₀, hR₀, fun R N hR hN => ?_⟩
  rw [openParentHamiltonianES_eq_of_groundSpaceES_eq (hR₀.trans_le hR) (hGS R) N,
    hKernel R N hR hN]
  exact (hGS N).symm

/-- Faithful stationary normalized generators have a positive canonical
parent interaction with the exact original boundary kernel at every volume
at least its range. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1
and Lemma existenceinteraction, in the supplied generating-data setting. -/
theorem exists_positive_parent_interaction_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N := by
  obtain ⟨R, hR, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  refine ⟨R, hR, canonicalParentInteractionMatrix A R,
    canonicalParentInteractionMatrix_posSemidef A R, ?_⟩
  intro N hN
  rw [toEuclideanLin_canonicalParentInteractionMatrix,
    openInteractionHamiltonianES_parentInteractionES A hR]
  exact hKernel R N le_rfl hN

/-- One constructed positive parent interaction has exact open kernels and
a common literal infinite-volume commutator gap in every pure zero-energy
state. The interaction and kernel property are derived from the normalized
faithful stationary generators. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6, lines 2649--2675,
in the supplied generating-data setting. -/
theorem exists_positive_parent_interaction_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
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
  obtain ⟨R, hR, hCanonicalKernel⟩ :=
    exists_ker_openParentHamiltonianES_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  let h := canonicalParentInteractionMatrix A R
  have hh : h.PosSemidef := canonicalParentInteractionMatrix_posSemidef A R
  have hKernel : ∀ N, R ≤ N → LinearMap.ker
      (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N := by
    intro N hN
    rw [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR]
    exact hCanonicalKernel R N le_rfl hN
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh ((eventually_ge_atTop R).mono fun N hN => hKernel N hN)
  exact ⟨R, hR, h, hh, hKernel,
    quasiLocalExpectation_mem_parentGroundStateFace_canonicalParentInteraction
      A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) R, γ, hγ, hGap⟩

end MPSTensor
