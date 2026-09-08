/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleCutComparison
import TNLean.MPS.MPU.SimpleTensorEquivalence

/-!
# Physical dimensions of the inverse-compatible source ranks

For a simple canonical-form-II MPU whose physical adjoint is related to the
same tensor by a unitary virtual gauge, the existing cut comparison gives
$r=\ell$. The simple-MPU rank product $r\ell=d^2$ then yields $\ell=d$ and
$r=d$. A single equivalence identifies the common raw source rank with the
physical index; no independent endpoint casts are chosen.

Source: CPSV17, `ThmFund1` (arXiv:1703.09188, lines 563–571), and FBC25,
`eq:defT` in the self-inverse case (arXiv:2502.20257, lines 1552–1563), with
the cut comparison at lines 5432–5443. This is a consequence of the stated
self-adjoint gauge hypothesis, not the general finite-group index argument
at line 1547. No scalar relation, adjoint simplicity, additional positivity,
or new virtual gauge is required. Only ranks and their coordinates are
identified here, not physical composition or the complementary relation.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)

include hU hsimple hT in
/-- Both source ranks equal the physical dimension under the self-adjoint
unitary gauge. Source: CPSV17 `ThmFund1` (lines 563–571), combined with the
FBC25 cut comparison (lines 5432–5443). No phase relation is assumed. -/
theorem inverseCompatible_sourceRanks_eq_physical : ℓ[U] = d ∧ r[U] = d := by
  have hr := rightRank_eq_leftRank_of_physicalAdjointTensor_eq_unitary_gauge U T hT
  have hprod : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 0 1).mp hsimple
  rw [hr] at hprod
  have hl : ℓ[U] = d := Nat.mul_self_inj.mp hprod
  exact ⟨hl, hr.trans hl⟩

/-- The single common-rank-to-physical equivalence used for raw endpoint
coordinates. Source: the rank consequence of CPSV17 `ThmFund1` (lines 563–571)
and FBC25's self-adjoint cut comparison (lines 5432–5443). -/
noncomputable def inverseCompatiblePhysicalEquiv : Fin ℓ[U] ≃ Fin d :=
  finCongr (inverseCompatible_sourceRanks_eq_physical U T hU hsimple hT).1

end MPOTensor
