/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedPrimitiveQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyPresentation
import TNLean.MPS.ParentHamiltonian.GaugePhaseSeparationTransport

/-!
# Original-chain commutator gaps for finite periodic tensor families

A positive finite-range interaction whose eventual open-chain kernels are
the joint boundary spaces of a finite weighted periodic tensor family has one
positive commutator gap in every pure zero-energy state. The conclusion concerns
every centered local observable and the literal finite-volume energy limit
along arbitrary diverging boundary margins.

A common positive blocking length, primitive sectors, faithful invariant
matrices, and their inequivalence are derived internally. Translation invariance
of a competing state and a lower bound on the interaction range beyond
positivity are unnecessary. Empty tensor families are allowed; their
zero-energy state face is empty.

**Scope restriction (periodic tensor families):** An explicit finite periodic
MPS family and its eventual original open-chain kernel identity are assumed.
Identifying a general GVBS presentation with these tensor data and finite
support spaces remains separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
No finite-volume gap in other residue classes is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
site grouping at lines 825--836, and Section 6, lines 2649--2675;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ}
/-- The eventual original joint kernel of a finite weighted periodic family
gives one positive literal commutator gap for all pure zero-energy states and
all centered original local observables. The common blocking length and the
primitive faithful inequivalent sectors are derived internally.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675; DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
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
  obtain ⟨L, hL, g, E, hE, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    exists_primitive_blockFamilyPresentation_of_isPeriodic μ A hμ m hPeriodic
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (E j) := fun j => ⟨Nat.ne_of_gt (hE j)⟩
  exact exists_pos_quasiLocalCommutator_limit_gap_of_blocked_primitive_family
    (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
    ρ hP hρ hDistinct.forall_ne_transport hJoint h hR hh hker
end MPSTensor
