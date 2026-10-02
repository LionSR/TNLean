/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.LocalParentExpectation

/-!
# Purity of the primitive quasi-local MPS state

The constructed state has expectation one on every finite-interval MPS support
projection. Any two states occurring in a nontrivial convex decomposition
inherit these support constraints. Supported-state uniqueness for a primitive
tensor with a faithful invariant matrix therefore proves purity among all
states of the quasi-local algebra. Translation invariance of the constituents
is not assumed, and no finite-chain uniqueness is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 854--887 and 1469--1482,
and the local support discussion in Section 3. The result concerns the
trace-preserving primitive canonical data used to construct the state; classification of the full
multiblock ground-state face is a separate assertion.
-/

open scoped Matrix ComplexOrder BigOperators
open SpinChain

namespace MPSTensor

variable {d D : ℕ} [NeZero d]

/-- Every interval support projection has expectation one in the constructed
state. Primitivity is not required. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1 and equations (3.1)--(3.2b). -/
theorem quasiLocalExpectation_groundSpaceProjection_eq_one
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (a : ℤ) (N : ℕ) :
    quasiLocalExpectation A hTP hρ hfix htr
      (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  have hX : groundSpaceES A N ≤ LinearMap.ker
      (Matrix.toEuclideanLin (1 - groundSpaceProjectionMatrix A N)) := by
    intro v hv
    change Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (1 - groundSpaceProjectionMatrix A N) v = 0
    rw [map_sub, map_one]
    simp only [groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply,
      sub_apply, one_apply_eq_self, Submodule.starProjection_eq_self_iff.mpr hv, sub_self]
  have hzero := quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    A hTP hρ hfix htr a (1 - groundSpaceProjectionMatrix A N) hX
  rw [map_sub, map_one, map_sub,
    (quasiLocalExpectation_isState A hTP hρ hfix htr).2.1] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- A trace-preserving primitive tensor with a faithful invariant matrix
determines a pure state of the quasi-local algebra. Extremality is taken
among all states, with no translation-invariance restriction.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 1469--1482
and Section 3. -/
theorem IsPrimitiveMPS.isPureQuasiLocalState_quasiLocalExpectation [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    IsPureQuasiLocalState d
      (quasiLocalExpectation A hP.norm hP.fixedPoint_psd
        hP.fixedPoint_is_fixed hP.trace_ne_zero) := by
  refine isPureQuasiLocalState_of_unique_supported_state _
    (quasiLocalExpectation_isState A hP.norm hP.fixedPoint_psd
      hP.fixedPoint_is_fixed hP.trace_ne_zero)
    (fun i : ℤ × ℕ => quasiLocalIntervalObservable d i.1 i.2
      (groundSpaceProjectionMatrix A i.2))
    (fun i => isStarProjection_quasiLocalIntervalObservable_groundSpaceProjectionMatrix
      A i.1 i.2)
    (fun i => quasiLocalExpectation_groundSpaceProjection_eq_one A hP.norm
      hP.fixedPoint_psd hP.fixedPoint_is_fixed hP.trace_ne_zero i.1 i.2) ?_
  intro φ hφ hSupport
  exact hP.eq_quasiLocalExpectation_of_groundSpace_support hρ φ hφ
    (fun a N => hSupport (a, N))

end MPSTensor
