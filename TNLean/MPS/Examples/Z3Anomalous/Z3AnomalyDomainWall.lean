/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicClass
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorCohomology
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalyClass

/-!
# The `ℤ₃` representation `{1, U, U†}`: domain-wall phase and cocycle class

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.C, `Intequiv`,
`Papers/2405.00439/MPU-DW.tex` lines 2013–2021, and Section IV.D, lines 2038–2054: the
domain-wall phase `∏_{k=1}^{o(g)} ω⁻¹(g, g^k, g)` and its `n = 3` table.

**Formalized here.** For every choice of fusion tensors of `Z3Anomalous.family`, the anomaly
three-cochain has the cyclic invariant of the cocycle `ω₂` of line 2040 at the generator, and
not that of `ω₀` or `ω₁`; so it is not cohomologous to `ω₀` or `ω₁`. Its domain-wall phase at the
generator is `exp(2πi/3)`, the `n = 3`, `j = 2`, `a = 1` entry of the printed table. Since the
cyclic invariant at the generator determines the class of a three-cocycle of `ℤ₃`
(`TNLean.Algebra.ScalarThreeCocycleCyclicClass`), the cochain is cohomologous to `ω₂`, and the
anomaly class of the family in `H³(ℤ₃, ℂˣ)` is the class of `ω₂`. The orientation of the
anomaly three-cochain is that of `TNLean.MPS.Examples.Z3Anomalous.Z3AnomalyClass`, whose
L-symbols satisfy the coupled pentagon equation `coupledpent` of the source (line 1876) with `ω`
on the same side.

## Main results

* `Z3Anomalous.eisensteinOmega_eq_rootOfUnity`: `ω₃ = exp(2πi/3)`.
* `Z3Anomalous.cyclicInvariant_omega_z3_eq_cyclicCocycle_two`.
* `Z3Anomalous.not_cohomologousTo_cyclicCocycle_omega_z3`.
* `Z3Anomalous.domainWallPhase_omega_z3`.
* `Z3Anomalous.cohomologousTo_cyclicCocycle_two_omega_z3`,
  `Z3Anomalous.anomalyClass_family_eq_cyclicCocycle_two`: the class is that of `ω₂`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open TNLean.Algebra

namespace Z3Anomalous

/-- Bridge: the primitive cube root `ω₃ = (−1 + i√3)/2` of the Eisenstein ring is
`exp(2πi/3)`. -/
theorem eisensteinOmega_eq_rootOfUnity :
    eisensteinOmega = ScalarThreeCochain.rootOfUnity 3 := by
  have harg : (2 * Real.pi * Complex.I / ((3 : ℕ) : ℂ)) =
      ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ScalarThreeCochain.rootOfUnity, harg, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three, eisensteinOmega]
  push_cast
  ring

/-- The generator `z3Gen` of `ℤ₃` has order `3`. -/
theorem orderOf_z3Gen : orderOf z3Gen = 3 :=
  orderOf_eq_prime z3Gen_pow_three (by decide)

/-- Bridge: **for every choice of fusion tensors, the anomaly three-cochain of `{1, U, U†}`
has the cyclic invariant of `ω₂`** at the generator. -/
theorem cyclicInvariant_omega_z3_eq_cyclicCocycle_two (fd : family.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega z3Gen 3 =
      ScalarThreeCochain.cyclicInvariant (ScalarThreeCochain.cyclicCocycle 3 2) z3Gen 3 := by
  apply Units.ext
  rw [cyclicInvariant_omega_z3, z3Gen,
    ScalarThreeCochain.cyclicInvariant_cyclicCocycle_one (by norm_num),
    eisensteinOmega_eq_rootOfUnity]

/-- Bridge: for every choice of fusion tensors, the anomaly three-cochain of `{1, U, U†}` is
not cohomologous to `ω_j` unless `j ≡ 2 mod 3`. -/
theorem not_cohomologousTo_cyclicCocycle_omega_z3 (fd : family.FusionData) {j : ℕ}
    (hj : ¬ j ≡ 2 [MOD 3]) :
    ¬ ScalarThreeCochain.CohomologousTo fd.omega (ScalarThreeCochain.cyclicCocycle 3 j) := by
  intro h
  have hj' := h.cyclicInvariant_eq z3Gen_pow_three
  rw [cyclicInvariant_omega_z3_eq_cyclicCocycle_two] at hj'
  have heq := congrArg Units.val hj'
  simp only [z3Gen, ScalarThreeCochain.cyclicInvariant_cyclicCocycle_one (show 1 < 3 by norm_num)]
    at heq
  have hprim : IsPrimitiveRoot (ScalarThreeCochain.rootOfUnity 3) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  rw [pow_eq_pow_mod j hprim.pow_eq_one] at heq
  exact hj (hprim.pow_inj (by norm_num) (Nat.mod_lt _ (by norm_num)) heq).symm

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2013–2021 and 2046–2054:
**for every choice of fusion tensors, the domain-wall phase of `{1, U, U†}` at the generator is
`exp(2πi/3)`**, the `j = 2`, `a = 1` entry of the printed `n = 3` table. -/
theorem domainWallPhase_omega_z3 (fd : family.FusionData) :
    (ScalarThreeCochain.domainWallPhase fd.omega z3Gen : ℂ) =
      Complex.exp ((2 * Real.pi / 3) * Complex.I) := by
  rw [← ScalarThreeCochain.domainWallPhase_cyclicCocycle_three.2.2.1,
    ScalarThreeCochain.domainWallPhase_eq_inv_cyclicInvariant,
    ScalarThreeCochain.domainWallPhase_eq_inv_cyclicInvariant, orderOf_z3Gen,
    cyclicInvariant_omega_z3_eq_cyclicCocycle_two]
  change _ = ((ScalarThreeCochain.cyclicInvariant _ z3Gen (orderOf z3Gen))⁻¹ : ℂˣ).val
  rw [orderOf_z3Gen]

/-- Project result: **for every choice of fusion tensors, the anomaly three-cochain of
`{1, U, U†}` is cohomologous to `ω₂`**, the cocycle of arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` line 2040. It follows from the equality of cyclic invariants and
the classification of the three-cocycles of `ℤ₃` stated there. -/
theorem cohomologousTo_cyclicCocycle_two_omega_z3 (fd : family.FusionData) :
    ScalarThreeCochain.CohomologousTo fd.omega (ScalarThreeCochain.cyclicCocycle 3 2) :=
  ScalarThreeCochain.cohomologousTo_of_cyclicInvariant_eq (by norm_num)
    (MPOTensor.GroupFamily.FusionData.isCocycle_omega family_isNormalRepresentation)
    (ScalarThreeCochain.cyclicCocycle_isCocycle 3 2)
    (cyclicInvariant_omega_z3_eq_cyclicCocycle_two fd)

/-- Project result: **the anomaly class of `{1, U, U†}` in `H³(ℤ₃, ℂˣ)` is the class of `ω₂`**,
the cocycle of arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040. -/
theorem anomalyClass_family_eq_cyclicCocycle_two :
    family_isNormalRepresentation.anomalyClass =
      ScalarThreeCochain.anomalyClass (ScalarThreeCochain.cyclicCocycleSubtype 3 2) := by
  rw [← MPOTensor.GroupFamily.FusionData.anomalyClass_omega family_isNormalRepresentation
    z3FusionData]
  exact (ScalarThreeCochain.cohomologousTo_iff_anomalyClass_eq _ _).1
    (cohomologousTo_cyclicCocycle_two_omega_z3 z3FusionData)

end Z3Anomalous
