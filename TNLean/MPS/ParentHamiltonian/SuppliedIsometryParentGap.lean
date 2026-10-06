/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SuppliedIsometryInsertion
import TNLean.MPS.ParentHamiltonian.StationaryParentFiniteGap
import QICLean.Channel.FixedPoint.Cesaro

/-!
# Constructed stationary states and parent gaps from a supplied isometry

A supplied physical-first isometry gives trace-preserving tensor generators.
Their channel has a stationary density matrix. Compressing its support gives
faithful generators for the same state, and a positive parent interaction
with finite and infinite gaps.

**Scope restriction (supplied physical isometry):** The isometry is supplied.
No construction from an arbitrary GVBS boundary-limit presentation is asserted;
see `docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
The finite kernels belong to the faithful compressed generators, and need not
be the full boundary spaces of the original slices.

Source context: Nachtergaele, arXiv:cond-mat/9410110, equations (3.5)--(3.6),
lines 1436--1450, Theorems 1.1--1.2, and Section 6. Stationary-density existence
uses the trace-preserving channel fixed-point theorem, proved by Cesàro means.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- A supplied isometry of positive virtual dimension admits a normalized
stationary positive virtual matrix. No faithfulness is assumed.
Source context: Nachtergaele, arXiv:cond-mat/9410110, equation (3.6),
lines 1445--1450, with the trace-preserving channel fixed-point theorem. -/
theorem exists_stationary_density_tensorOfPhysicalIsometry
    [NeZero D] (V : Matrix (Fin d × Fin D) (Fin D) ℂ) (hV : Vᴴ * V = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ Kraus.map (tensorOfPhysicalIsometry V) ρ = ρ := by
  have hChannel := Kraus.isChannel_mapLM (tensorOfPhysicalIsometry V)
    (isLeftCanonical_tensorOfPhysicalIsometry V hV)
  obtain ⟨ρ, ⟨hρ, htr⟩, _hSupport, hFix⟩ :=
    hChannel.exists_fixed_density_of_preserves_compression
      (E := Kraus.mapLM (tensorOfPhysicalIsometry V)) (P := 1)
      ⟨Matrix.isHermitian_one, one_mul _⟩ one_ne_zero (fun X => by simp)
  exact ⟨ρ, hρ, htr, hFix⟩

/-- A supplied physical-first isometry of positive virtual dimension gives
normalized stationary state data and a constructed positive parent interaction
with finite and infinite gaps. The original generated state is preserved under
faithful support compression; no purity of that state is asserted.
Source context: Nachtergaele, arXiv:cond-mat/9410110, equation (3.6),
Theorems 1.1--1.2, and Section 6, for the supplied-isometry representation. -/
theorem exists_positive_parent_finite_and_quasiLocal_gap_of_physical_isometry
    [NeZero D] (V : Matrix (Fin d × Fin D) (Fin D) ℂ) (hV : Vᴴ * V = 1) :
    let A := tensorOfPhysicalIsometry V
    let hA := isLeftCanonical_tensorOfPhysicalIsometry V hV
    ∃ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)
      (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ),
      Matrix.trace ρ = 1 ∧
    ∃ (E : ℕ) (hE : 0 < E) (B : MPSTensor d E)
      (σ : Matrix (Fin E) (Fin E) ℂ) (hB : IsLeftCanonical B)
      (hσ : σ.PosDef) (hσFix : Kraus.map B σ = σ),
      let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
      let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
      quasiLocalExpectation A hA hρ hFix htr =
        quasiLocalExpectation B hB hσ.posSemidef hσFix (ne_of_gt hσ.trace_pos) ∧
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES B N) ∧
      quasiLocalExpectation A hA hρ hFix htr ∈
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
  obtain ⟨ρ, hρ, hTrace, hFix⟩ := exists_stationary_density_tensorOfPhysicalIsometry V hV
  have htr : Matrix.trace ρ ≠ 0 := hTrace.trans_ne one_ne_zero
  refine ⟨ρ, hρ, htr, hFix, hTrace, ?_⟩
  exact exists_positive_parent_finite_and_quasiLocal_gap_of_leftCanonical_of_posSemidef_fixedPoint
    (tensorOfPhysicalIsometry V) (isLeftCanonical_tensorOfPhysicalIsometry V hV) hρ htr hFix

end MPSTensor
