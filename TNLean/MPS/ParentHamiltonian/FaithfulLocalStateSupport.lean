/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalDimension
import TNLean.MPS.ParentHamiltonian.LocalDensitySupport
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.QCA.QuasiLocalInterval

/-!
# Finite restrictions of faithful MPS states

The quasi-local state defined by a trace-preserving tensor and a faithful
stationary matrix has the same finite density on every translated interval.
The range of that density is exactly the MPS boundary space, including on
the empty interval. The physical dimension is derived from normalization.

**Scope restriction (supplied faithful generators):** The generating tensor
and faithful stationary matrix are supplied. Their construction from an
arbitrary GVBS presentation is separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and the local density support identification at lines 1724--1738.
-/

open SpinChain
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

/-- Every finite restriction of the state defined by faithful stationary
generators has a density whose range is exactly the tensor boundary space.
The same density represents every translation of the interval.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and lines 1724--1738. -/
theorem exists_quasiLocalExpectation_density_range_eq_groundSpaceES [NeZero D]
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.transferMap A ρ = ρ) (k : ℕ) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ σ : Matrix (Cfg d k) (Cfg d k) ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos)
          (quasiLocalIntervalObservable d a k X) = Matrix.trace (σ * X)) ∧
      LinearMap.range (Matrix.toEuclideanLin σ) = groundSpaceES A k := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  change (∑ i, (A i)ᴴ * A i) = 1 at hA
  obtain ⟨σ, hσ, htr, hrep, hRange⟩ :=
    exists_local_density_range_eq_groundSpaceES A hA hρ k
  refine ⟨σ, hσ, htr, ?_, hRange⟩
  intro a X
  rw [quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hrep X

end MPSTensor
