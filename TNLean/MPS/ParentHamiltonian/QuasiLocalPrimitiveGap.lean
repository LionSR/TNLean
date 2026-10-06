/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.MPS.ParentHamiltonian.PrimitiveLocalParentInteractionGap
import TNLean.QCA.QuasiLocalInterval

/-!
# A primitive-sector commutator gap in the quasi-local state

The normalized positive quasi-local MPS state has the original trace
insertion expectations on finite intervals. The primitive local commutator
bound therefore gives a positive energy inequality for every centered local
observable in this constructed state. All finite-volume and limiting estimates
are derived from the tensor and the positive parent interaction.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (one primitive sector):** The commutator theorem assumes
a normalized primitive tensor with a positive-definite invariant matrix and
interaction range at least \(D^4+1\). Identification of all pure multiblock
GVBS states and construction of the GNS Hamiltonian remain separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open scoped Matrix BigOperators ComplexOrder
open SpinChain

namespace MPSTensor

variable {d D : ℕ}

/-- The completed MPS expectation on a consecutive matrix observable is the
original trace insertion formula. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem quasiLocalExpectation_quasiLocalIntervalObservable [NeZero d]
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    quasiLocalExpectation A hTP hρ hfix htr (quasiLocalIntervalObservable d a k X) =
      observableInsertionExpectation A ρ X := by
  rw [quasiLocalIntervalObservable_apply, quasiLocalExpectation_interval,
    StarAlgEquiv.apply_symm_apply]

/-- Every positive parent interaction at range at least \(D^4+1\) has a
positive commutator bound in the constructed primitive quasi-local state.
The constant is independent of the interval, its position, and the observable.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsPrimitiveMPS.exists_pos_quasiLocalCommutator_gap_of_isParentInteraction
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) (hR : D ^ 4 + 1 ≤ R) :
    let ω := quasiLocalExpectation A hP.norm hP.fixedPoint_psd
      hP.fixedPoint_is_fixed hP.trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧ ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω (quasiLocalIntervalObservable d a k X) = 0 →
        γ * (ω (star (quasiLocalIntervalObservable d a k X) *
          quasiLocalIntervalObservable d a k X)).re ≤
        (ω (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ)) ((R - 1 + k) + (R - 1))
          (localCommutatorObservable h X))).re := by
  dsimp only
  obtain ⟨γ, hγ, hgap⟩ := hP.exists_pos_localCommutator_gap_of_isParentInteraction hρ h hh hR
  refine ⟨γ, hγ, ?_⟩
  intro a k X hk hcenter
  rw [quasiLocalExpectation_quasiLocalIntervalObservable] at hcenter
  rw [← map_star (quasiLocalIntervalObservable d a k) X, ← map_mul,
    quasiLocalExpectation_quasiLocalIntervalObservable,
    quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hgap X hk hcenter

end MPSTensor
