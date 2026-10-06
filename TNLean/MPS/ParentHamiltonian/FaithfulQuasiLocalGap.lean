/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalDimension
import TNLean.MPS.ParentHamiltonian.FaithfulPeriodicGroundSpace
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyQuasiLocalGap

/-!
# Infinite-volume gaps for faithful normalized generators

A left-canonical tensor with a positive-definite stationary matrix admits a
finite periodic-sector presentation of every finite boundary space. Therefore
a positive finite-range interaction whose eventual open-chain kernels are
these spaces has a common positive commutator gap in all pure zero-energy
states. The energy is the literal finite-volume commutator limit along any
exhaustion with both boundary margins diverging. The tensor itself need not
be irreducible, primitive, or periodic.

**Scope restriction (supplied faithful generating data):** A normalized tensor
and a faithful stationary matrix are supplied. The result does not construct
these data from an arbitrary GVBS boundary limit. That separate passage is
recorded in
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, the normalized generating data in Section 3, lines 1394--1483,
and the infinite-volume argument in Section 6, lines 2649--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D R : ℕ}

/-- Faithful normalized generating data and an eventual exact open-chain
kernel identity give one positive literal commutator gap in every pure
zero-energy state, for every centered local observable and every diverging
pair of boundary margins. No irreducibility, primitivity, periodicity, or
translation invariance of a competing state is assumed.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, Section 3, lines 1394--1483, and Section 6, lines 2649--2675. -/
theorem exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
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
  obtain ⟨b, _hb, dim, _hdim, B, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  have hJointKer : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) B) N :=
    hker.mono fun N hN => hN.trans (hGS N)
  exact exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    (fun _ => 1) B (fun _ => one_ne_zero) m hPeriodic h hR hh hJointKer

end MPSTensor
