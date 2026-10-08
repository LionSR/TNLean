/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalExpectationEquality
import TNLean.MPS.ParentHamiltonian.FaithfulParentInteractionGap

/-!
# Constructed parent interactions for stationary MPS states

A normalized tensor with a nonzero positive stationary matrix can be compressed
to faithful stationary generators for the identical quasi-local state. Those
generators yield a positive parent interaction whose sufficiently long open
kernels are their boundary spaces. The original generated state belongs to its
zero-energy face, and one positive literal commutator gap holds in every pure
state in that face. No purity of the original generated state is asserted.

**Scope restriction (supplied stationary generators):** The tensor and its
nonzero positive stationary matrix are supplied. Constructing them from an
arbitrary GVBS boundary-limit presentation remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
The finite kernels are the compressed boundary spaces; no equality with the
original tensor's full boundary spaces is asserted.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Section 3, lines 1394--1483, Lemma existenceinteraction, lines 2195--2230,
and Section 6, lines 2649--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- A stationary MPS state with a nonzero positive virtual matrix has faithful
compressed generators and a constructed positive parent interaction. The
original state lies in the zero-energy face, and one positive literal
commutator gap holds in every pure state in that face. Dimensions, faithfulness,
the interaction, and its finite kernel property are derived internally.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Section 3, Lemma existenceinteraction, and Section 6. -/
theorem exists_positive_parent_interaction_quasiLocal_gap_of_leftCanonical_of_posSemidef_fixedPoint
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
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
  obtain ⟨E, hE, _V, B, σ, hB, hσ, hσFix, _hV, _hVrange,
    _hCorner, _hσEq, _hInt, _hTrace, hStateEq⟩ :=
    exists_faithful_quasiLocalExpectation_supportCompression_of_leftCanonical
      A hA hρ htr hFix
  let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
  let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
  obtain ⟨R, hR, h, hh, hKernel, hMember, γ, hγ, hGap⟩ :=
    exists_positive_parent_interaction_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
      B hB hσ hσFix
  refine ⟨E, hE, B, σ, hB, hσ, hσFix, hStateEq,
    R, hR, h, hh, hKernel, ?_, γ, hγ, hGap⟩
  exact hStateEq.symm ▸ hMember

end MPSTensor
