/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleGroupCohomology
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# The anomaly class in degree-three group cohomology

For a group of matrix product operators with normal doubled-index tensors, every
choice of fusion tensors gives a scalar three-cocycle `ω`
(arXiv:2502.20257, `eq:3-cocycle`), and two choices give cohomologous cocycles
(`eq:omegagauge`). Through the identification of scalar three-cocycles with
Mathlib's degree-three group cohomology of the trivial representation on `ℂˣ`,
the class of `ω` in `H³(G, ℂˣ)` is therefore an invariant of the operator family.

## Main definitions

* `MPOTensor.GroupFamily.IsNormalRepresentation.anomalyClass`: the class of the
  anomaly three-cocycle in `H³(G, ℂˣ)`.

## Main results

* `MPOTensor.GroupFamily.FusionData.anomalyClass_omega_eq`: two choices of fusion
  tensors give the same class in `H³(G, ℂˣ)`.
* `MPOTensor.GroupFamily.FusionData.anomalyClass_omega`: every choice of fusion
  tensors represents the anomaly class.
-/

namespace MPOTensor

namespace GroupFamily

open TNLean.Algebra

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d}

namespace FusionData

/-- The degree-three class of the anomaly three-cocycle does not depend on the
fusion tensors (arXiv:2502.20257, `eq:omegagauge`). -/
theorem anomalyClass_omega_eq (hF : F.IsNormalRepresentation) (fd fd' : FusionData F) :
    ScalarThreeCochain.anomalyClass ⟨fd'.omega, isCocycle_omega hF⟩ =
      ScalarThreeCochain.anomalyClass ⟨fd.omega, isCocycle_omega hF⟩ :=
  (ScalarThreeCochain.cohomologousTo_iff_anomalyClass_eq _ _).1
    (omega_cohomologousTo hF fd fd')

end FusionData

namespace IsNormalRepresentation

/-- The anomaly class in `H³(G, ℂˣ)` of a group of matrix product operators with
normal doubled-index tensors: the class of the three-cocycle `ω` of
arXiv:2502.20257, `eq:3-cocycle`, for any choice of fusion tensors. -/
noncomputable def anomalyClass (hF : F.IsNormalRepresentation) :
    groupCohomology (scalarH2Representation G) 3 :=
  ScalarThreeCochain.anomalyClass
    ⟨hF.nonempty_fusionData.some.omega, FusionData.isCocycle_omega hF⟩

end IsNormalRepresentation

namespace FusionData

/-- Every choice of fusion tensors represents the anomaly class. -/
theorem anomalyClass_omega (hF : F.IsNormalRepresentation) (fd : FusionData F) :
    ScalarThreeCochain.anomalyClass ⟨fd.omega, isCocycle_omega hF⟩ = hF.anomalyClass :=
  anomalyClass_omega_eq hF hF.nonempty_fusionData.some fd

/-- The anomaly class vanishes exactly when the anomaly three-cocycle of some,
equivalently every, choice of fusion tensors has trivial gauge class. -/
theorem isTrivialGaugeClass_omega_iff (hF : F.IsNormalRepresentation) (fd : FusionData F) :
    ScalarThreeCochain.IsTrivialGaugeClass fd.omega ↔ hF.anomalyClass = 0 := by
  rw [← anomalyClass_omega hF fd]
  exact ScalarThreeCochain.isTrivialGaugeClass_iff_anomalyClass_eq_zero
    ⟨fd.omega, isCocycle_omega hF⟩

end FusionData

end GroupFamily

end MPOTensor
