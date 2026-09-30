/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.Periodic.Normalization
import TNLean.MPS.Periodic.PeriodExistence
import TNLean.MPS.SharedInfra.Scaling

/-!
# Periodic normalization of an arbitrary nonzero irreducible tensor

Every nonzero irreducible MPS tensor becomes, after a nonzero scalar rescaling
and a gauge transformation, left-canonical with a transfer map of spectral
radius one and peripheral spectrum the `m`-th roots of unity for some positive
`m`: a periodic block in the sense of `IsPeriodic`.  This generalizes
`MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal`
(`TNLean/MPS/FundamentalTheorem/SectorBNT/PowerSumCoefficients.lean`), which
covers only the period-one (algebraically normal) case, to tensors that may be
genuinely periodic.

This is the trace-reduction normalization step of
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`,
§"Trace reduction and explicit multiplicities": rescaling a nonzero
irreducible composition factor `T_a` by `s_a⁻¹ = ρ(𝓔_{T_a})^{-1/2}` and gauging
by the positive-definite fixed point of the rescaled adjoint transfer map
produces the normalized periodic representative `A_a`.

## Main result

* `MPSTensor.exists_leftCanonical_periodic_scale_of_irreducible`
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- **Periodic normalization of a nonzero irreducible tensor.**

For a nonzero irreducible tensor `A`, rescaling by `ζ = ρ(𝓔_A)^{-1/2}` and
gauging by the positive-definite fixed point of the trace-preserving
normalization produces a left-canonical representative `B` whose transfer map
has spectral radius one and peripheral spectrum the `m`-th roots of unity for
some positive `m`.  The scalar `ζ` records the rescaling in the matrix product
vectors.

Source: `t1_unblocked.tex`, §"Trace reduction and explicit multiplicities",
equations `moa-t1:factor-normalization`. -/
theorem exists_leftCanonical_periodic_scale_of_irreducible
    [NeZero D] {A : MPSTensor d D}
    (hIrr : Kraus.IsIrreducibleFamily A) (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (m : ℕ), ζ ≠ 0 ∧
      GaugeEquiv (fun i => ζ • A i) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      IsPeriodic m B := by
  classical
  obtain ⟨ρ, r, hρ, hr, hEig⟩ := exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hA
  have hIrrMap : IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr
  have hRad :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (Kraus.transferMap (d := d) (D := D) A)) =
        ENNReal.ofReal r :=
    spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap (d := d) (D := D) A) (Kraus.transferMap_isCPMap A) hIrrMap ρ r hρ hr hEig
  set ζ : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ) with hζ_def
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hζ : ζ ≠ 0 := by
    simp only [hζ_def, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact hsqrt_pos.ne'
  have hnormζ : ‖ζ‖ = (Real.sqrt r)⁻¹ := by
    rw [hζ_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsqrt_pos)]
  have hIrrScaled : Kraus.IsIrreducibleFamily (fun i => ζ • A i) :=
    isIrreducibleTensor_smul hζ A hIrr
  have hRadScaled :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (Kraus.transferMap (d := d) (D := D) (fun i => ζ • A i))) = 1 := by
    rw [spectralRadius_transferMap_smul ζ hζ A, hRad]
    have hval : ‖ζ‖ ^ 2 * r = 1 := by
      rw [hnormζ, inv_pow, Real.sq_sqrt hr.le]
      field_simp
    have hnnreal : ‖ζ‖₊ ^ 2 * r.toNNReal = 1 := by
      apply NNReal.coe_injective
      push_cast [Real.coe_toNNReal r hr.le]
      exact hval
    change (↑‖ζ‖₊ : ENNReal) ^ 2 * (↑r.toNNReal : ENNReal) = 1
    rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, hnnreal, ENNReal.coe_one]
  obtain ⟨m, hSpec⟩ :=
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one hIrrScaled hRadScaled
  obtain ⟨σ, hσ, hσfix, hGauge, hPer⟩ := hSpec.exists_isPeriodic_tpGauge
  refine ⟨Kraus.tpGauge (d := d) (D := D) (fun i => ζ • A i) σ, ζ, m, hζ, hGauge, ?_, hPer⟩
  intro N τ
  rw [← hGauge.sameMPV N τ]
  simp only [mpv, coeff]
  rw [Kraus.evalWord_smul]
  simp [List.length_ofFn, Matrix.trace_smul]

end MPSTensor
