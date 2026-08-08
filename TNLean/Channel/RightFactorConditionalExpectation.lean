/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.CfcKronecker
import TNLean.Channel.FixedPoint.ConditionalExpectation
import TNLean.Channel.KrausCPTP

/-!
# Conditional expectation onto one right matrix factor

This file constructs the trace-preserving conditional expectation
\[
  E(A)=\frac{\mathbf 1_m}{m}\otimes\operatorname{tr}_m(A)
\]
from `M_m(ℂ) ⊗ M_d(ℂ)` onto `1_m ⊗ M_d(ℂ)`. It is the one-block codomain
retraction needed when a finite-dimensional codomain algebra is represented
inside a full matrix algebra in Wolf's operator-system extension theorem.

The completely positive proof uses the existing channel operations: interchange
the tensor factors, trace out the new right factor, prepare the maximally mixed
left state, and interchange the factors back.

## Main definitions

* `Matrix.rightFactorStarSubalgebra`: the subalgebra `1_m ⊗ M_d(ℂ)`.
* `Matrix.rightFactorConditionalExpectation`: the normalized partial-trace map.

## Main results

* `Matrix.rightFactorConditionalExpectation_apply`: the explicit evaluation formula.
* `Matrix.rightFactorConditionalExpectation_isKrausCPTP`: the map is trace-preserving
  and completely positive.
* `Matrix.rightFactorConditionalExpectation_fixes`: the map fixes the right factor.
* `Matrix.rightFactorConditionalExpectation_range_subset`: its range lies in the
  right-factor subalgebra.
* `Matrix.rightFactorConditionalExpectation_idempotent`: the map is idempotent.
* `Matrix.rightFactorConditionalExpectation_unital`: the map is unital.
* `Matrix.rightFactorConditionalExpectation_isConditionalExpectation`: the map is a
  conditional expectation in the sense of `Kraus.IsConditionalExpectation`.
* `Matrix.rightFactorConditionalExpectation_isKrausCPTP_and_isConditionalExpectation`:
  the combined interface used by the operator-system extension argument.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5,
  Equation (1.40), and the operator-system extension theorem; local source
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570
  and 616--626.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace Matrix

variable {m d : ℕ}

/-- The normalized partial-trace expectation onto the right matrix factor.

It is implemented as tensor-factor interchange, partial trace, preparation of
`m⁻¹ • 1`, and tensor-factor interchange back. Thus its definition directly
exhibits the standard completely positive construction.

Source: the one-block trace-preserving choice associated with Wolf,
Proposition 1.5 and Equation (1.40); it supplies the codomain retraction for
the extension theorem at local source lines 616--626. -/
def rightFactorConditionalExpectation :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  (equivReindexMap (Equiv.prodComm (Fin d) (Fin m))).comp
    ((preparationMap (α := Fin d) (maximallyMixedOn (dA := m))).comp
      ((partialTraceRightLM (α := Fin d) (β := Fin m)).comp
        (equivReindexMap (Equiv.prodComm (Fin m) (Fin d)))))

/-- Evaluation of the right-factor conditional expectation:
`E(A) = 1_m ⊗ (m⁻¹ • partialTraceLeft A)`. -/
@[simp]
theorem rightFactorConditionalExpectation_apply
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    rightFactorConditionalExpectation (m := m) A =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
        (((m : ℂ)⁻¹) • partialTraceLeft A) := by
  ext p q
  simp [rightFactorConditionalExpectation, maximallyMixedOn, equivReindexMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, preparationMap,
    partialTraceRightLM, partialTraceRight_apply, Matrix.partialTraceLeft_apply]
  ring

/-- The normalized partial-trace expectation is trace-preserving and completely
positive. The proof composes the existing CPTP reindexing and partial-trace
maps with preparation of the maximally mixed state. -/
theorem rightFactorConditionalExpectation_isKrausCPTP [NeZero m] :
    IsKrausCPTP (rightFactorConditionalExpectation (m := m) (d := d)) := by
  have hReindexIn :=
    equivReindexMap_isKrausCPTP (Equiv.prodComm (Fin m) (Fin d))
  have hTrace := partialTraceRightLM_isKrausCPTP (α := Fin d) (β := Fin m)
  have hTraceReindex := isKrausCPTP_comp hReindexIn hTrace
  have hPrepare := preparationMap_isKrausCPTP (α := Fin d)
    (maximallyMixedOn (dA := m)) maximallyMixedOn_posSemidef
    maximallyMixedOn_trace
  have hPrepareTrace := isKrausCPTP_comp hTraceReindex hPrepare
  have hReindexOut :=
    equivReindexMap_isKrausCPTP (Equiv.prodComm (Fin d) (Fin m))
  exact isKrausCPTP_comp hPrepareTrace hReindexOut

/-- The normalized partial-trace expectation is completely positive. -/
theorem rightFactorConditionalExpectation_isKrausCP [NeZero m] :
    IsKrausCP (rightFactorConditionalExpectation (m := m) (d := d)) :=
  rightFactorConditionalExpectation_isKrausCPTP.isKrausCP

/-- The unital star subalgebra `1_m ⊗ M_d(ℂ)` inside
`M_m(ℂ) ⊗ M_d(ℂ)`. -/
def rightFactorStarSubalgebra :
    StarSubalgebra ℂ (Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :=
  StarAlgHom.range (rightKroneckerEmbed (m := Fin m) (n := Fin d))

/-- Membership in the right-factor star subalgebra means being of the form
`1_m ⊗ X`. -/
theorem mem_rightFactorStarSubalgebra
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    A ∈ rightFactorStarSubalgebra (m := m) (d := d) ↔
      ∃ X : Matrix (Fin d) (Fin d) ℂ, A = 1 ⊗ₖ X := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, hX.symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨X, rfl⟩

/-- The normalized partial-trace expectation fixes every element of the right
factor pointwise. -/
theorem rightFactorConditionalExpectation_fixes [NeZero m]
    (X : Matrix (Fin d) (Fin d) ℂ) :
    rightFactorConditionalExpectation (m := m)
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X := by
  rw [rightFactorConditionalExpectation_apply, partialTraceLeft_kronecker,
    Matrix.trace_one, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℂ) ≠ 0), one_smul]

/-- The range of the normalized partial-trace expectation is contained in the
right-factor star subalgebra. -/
theorem rightFactorConditionalExpectation_range_subset
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    rightFactorConditionalExpectation (m := m) A ∈
      rightFactorStarSubalgebra (m := m) (d := d) := by
  rw [mem_rightFactorStarSubalgebra, rightFactorConditionalExpectation_apply]
  exact ⟨((m : ℂ)⁻¹) • partialTraceLeft A, rfl⟩

/-- The normalized partial-trace expectation is idempotent. -/
theorem rightFactorConditionalExpectation_idempotent [NeZero m]
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    rightFactorConditionalExpectation (m := m)
        (rightFactorConditionalExpectation (m := m) A) =
      rightFactorConditionalExpectation (m := m) A := by
  rw [rightFactorConditionalExpectation_apply A]
  exact rightFactorConditionalExpectation_fixes (m := m) _

/-- The normalized partial-trace expectation is unital. -/
theorem rightFactorConditionalExpectation_unital [NeZero m] :
    rightFactorConditionalExpectation (m := m) (d := d) 1 = 1 := by
  rw [← Matrix.one_kronecker_one]
  exact rightFactorConditionalExpectation_fixes (m := m) 1

/-- The normalized partial trace is a completely positive conditional
expectation onto `1_m ⊗ M_d(ℂ)`.

This packages complete positivity, unitality, idempotence, range inclusion,
and pointwise fixation using the project's `Kraus.IsConditionalExpectation`
terminology. -/
theorem rightFactorConditionalExpectation_isConditionalExpectation [NeZero m] :
    Kraus.IsConditionalExpectation
      (rightFactorConditionalExpectation (m := m) (d := d))
      (rightFactorStarSubalgebra (m := m) (d := d)) where
  positive :=
    (isKrausCP_iff_isCPMap.mp rightFactorConditionalExpectation_isKrausCP).isPositiveMap
  idempotent := rightFactorConditionalExpectation_idempotent
  unital := rightFactorConditionalExpectation_unital
  range_subset := rightFactorConditionalExpectation_range_subset
  fixes A hA := by
    rw [mem_rightFactorStarSubalgebra] at hA
    obtain ⟨X, rfl⟩ := hA
    exact rightFactorConditionalExpectation_fixes X

/-- The normalized partial trace is simultaneously trace-preserving completely
positive and a conditional expectation onto the right-factor star subalgebra.
This is the full one-block interface used by the operator-system extension
argument. -/
theorem rightFactorConditionalExpectation_isKrausCPTP_and_isConditionalExpectation
    [NeZero m] :
    IsKrausCPTP (rightFactorConditionalExpectation (m := m) (d := d)) ∧
      Kraus.IsConditionalExpectation
        (rightFactorConditionalExpectation (m := m) (d := d))
        (rightFactorStarSubalgebra (m := m) (d := d)) :=
  ⟨rightFactorConditionalExpectation_isKrausCPTP,
    rightFactorConditionalExpectation_isConditionalExpectation⟩

end Matrix
