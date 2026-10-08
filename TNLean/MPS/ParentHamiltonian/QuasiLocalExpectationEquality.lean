/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.MPS.ParentHamiltonian.StationarySupportCompression
import TNLean.MPS.Core.PhysicalDimension

/-!
# Equality of quasi-local MPS expectations

Equality of all finite insertion expectations for two normalized stationary
positive generating data sets implies equality of their continuous quasi-local
functionals. The bond dimensions may differ. In particular, compression to
the support of a nonzero positive stationary matrix preserves the actual
quasi-local state, as well as its finite insertion expectations.

**Scope restriction (supplied stationary generating data):** The support
compression consequence assumes a tensor and a nonzero positive stationary
matrix. It does not construct these generators from an arbitrary GVBS
boundary limit; that passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), and lines 1394--1467, the generating representation.
The functional equality is the uniqueness of continuous extension from the
finite observable algebras.
-/

open SpinChain
open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D E : ℕ}

/-- Equality of every finite insertion expectation implies equality of the
continuous quasi-local state functionals, for possibly different bond
dimensions. No faithfulness or purity is required.
Source context: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), and uniqueness of continuous extension. -/
theorem quasiLocalExpectation_eq_of_forall_observableInsertionExpectation_eq
    [NeZero d] (A : MPSTensor d D) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hFix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (B : MPSTensor d E) (hB : ∑ i, (B i)ᴴ * B i = 1)
    {σ : Matrix (Fin E) (Fin E) ℂ} (hσ : σ.PosSemidef)
    (hσFix : Kraus.transferMap B σ = σ) (hσtr : Matrix.trace σ ≠ 0)
    (hInsertion : ∀ (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X) :
    quasiLocalExpectation A hA hρ hFix htr =
      quasiLocalExpectation B hB hσ hσFix hσtr := by
  apply (localMPSState B hB hσ hσFix hσtr).quasiLocalFunctional_unique
    (quasiLocalExpectation A hA hρ hFix htr)
  intro Λ X
  rw [quasiLocalExpectation_quasiLocalObservable]
  exact hInsertion _ _

/-- Compression to the support of a nonzero positive stationary matrix gives
faithful normalized generators for the identical continuous quasi-local state.
The support isometry and exact compressed data are retained. No purity or
minimality is assumed.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), and Wolf, restriction to full-rank fixed points. -/
theorem exists_faithful_quasiLocalExpectation_supportCompression_of_leftCanonical
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ (E : ℕ) (hE : 0 < E) (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ)
      (hB : IsLeftCanonical B) (hσ : σ.PosDef) (hσFix : Kraus.map B σ = σ),
      let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
      let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      (∀ i, A i * V = V * B i) ∧ Matrix.trace σ = Matrix.trace ρ ∧
      quasiLocalExpectation A hA hρ hFix htr =
        quasiLocalExpectation B hB hσ.posSemidef hσFix (ne_of_gt hσ.trace_pos) := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, hCorner, hσEq, hσ, hB,
    hInt, hσFix, hTrace, hInsertion⟩ :=
    exists_faithful_stationary_supportCompression_of_leftCanonical A hA hρ htr hFix
  let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
  let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
  refine ⟨E, hE, V, B, σ, hB, hσ, hσFix, hV, hVrange,
    hCorner, hσEq, hInt, hTrace, ?_⟩
  exact quasiLocalExpectation_eq_of_forall_observableInsertionExpectation_eq
    A hA hρ hFix htr B hB hσ.posSemidef hσFix (ne_of_gt hσ.trace_pos) hInsertion

end MPSTensor
