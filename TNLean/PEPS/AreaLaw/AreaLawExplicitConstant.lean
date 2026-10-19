/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheoremFromTwoFamilies
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries

/-!
# The two-dimensional area law with an explicit constant

The proof of Theorem 1.1 of the area-law manuscript produces its constant from the
constants of Propositions 9.6, 10.2 and 11.2. This module assembles that constant from the
named constants of the three propositions, so that the only remaining input is a tuple of
transport constants `c₀, Cent, eent, Cen, een` satisfying the finite-family transport bound
`Scan.CollarScan.FiniteFamilyTransportBound`. These constants are universal: they do not
depend on `q, R, J, Δ`, the domain, the Hamiltonian, the state or the cut.

## Main results

* `uniformAreaLawConstantAt`, `uniformAreaLaw_explicit_of_le`: the constant of Theorem 1.1 at
  any upper bound `B` for the safe-box constant of Proposition 9.5, and Theorem 1.1 with it.
* `uniformAreaLawConstantExplicit`: the constant of Theorem 1.1 as a function of
  `q, R, J, Δ` and the transport constants.
* `uniformAreaLaw_explicit`: Theorem 1.1 with this constant, for every tuple of transport
  constants satisfying the transport bound.
* `uniformAreaLawConstantClosed`, `uniformAreaLaw_closed`: the constant at the explicit
  transport constants of the companion library, and Theorem 1.1 with it, with no hypothesis
  beyond those of Theorem 1.1.
* `uniformAreaLawConstantClosedAt`, `uniformAreaLaw_closed_of_le`: the same at any upper bound
  `B` for the closed safe-box constant `physicalBoxConstantClosed q R J Δ`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 39–53), with the proof in
  `10-geometry.tex`, lines 803–857. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The explicit constant is recorded in `docs/notes/arealaw2d_explicit_constant.tex`
(Section `sec:top`).

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The constant of Theorem 1.1 at the template constants `D₀ = 2R + 11` and `C_tpl = 24`, as
a function of the Hamiltonian parameters `q, R, J, Δ`, a safe-box constant `Cbox` of
Proposition 9.5 and the transport constants `c₀, Cent, eent, Cen, een`:
* `C₁ = sublinearCollarConstant q J Δ Cbox` and
  `N₁ = sublinearCollarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10) c₀
  Cent eent Cen een` (Proposition 9.6);
* `C₂ = amplificationConstantExplicit q R J Δ C₀ 100` and
  `N₂ = max (amplificationThresholdExplicit q R J Δ C₀ 100) (Exponents.collarRadiusThreshold C₂
  1)` with `C₀ = max C₁ 1` (Proposition 10.2);
* `C₃ = twoFamilyDecompositionConstant (2R + 11) 24 n_* c₁` at the lower scale
  `n_* = uniformAreaLawScale N₁ N₂ C₂` and the birth-separation constant
  `c₁ = Geometry.birthTemplateSeparationConstant = 1/112` (Proposition 11.2);
and the constant is `uniformAreaLawConstantOf q C₂ C₃ = c_D log q + c_M c_D / 2` with
`c_D = max C₃ 0` and `c_M = max C₂ 0`. The source asserts only that a constant exists.
Source: proof of Theorem 1.1, `10-geometry.tex`, lines 803–857; the constant is tabulated in
`docs/notes/arealaw2d_explicit_constant.tex`, Section `sec:top`. -/
noncomputable def uniformAreaLawConstantAt (q R : ℕ) (J Δ Cbox c₀ Cent eent Cen een : ℝ) :
    ℝ :=
  let C₀ := max (sublinearCollarConstant q J Δ Cbox) 1
  let N₁ := sublinearCollarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10) c₀
    Cent eent Cen een
  let C₂ := amplificationConstantExplicit q R J Δ C₀ 100
  let N₂ := max (amplificationThresholdExplicit q R J Δ C₀ 100)
    (Exponents.collarRadiusThreshold C₂ 1)
  uniformAreaLawConstantOf q C₂ (twoFamilyDecompositionConstant (2 * (R : ℝ) + 11) 24
    (uniformAreaLawScale N₁ N₂ C₂) Geometry.birthTemplateSeparationConstant)

/-- The constant of Theorem 1.1 at the safe-box constant
`Cbox = Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een` of Proposition 9.5:
`uniformAreaLawConstantAt` at this `Cbox`. Source: proof of Theorem 1.1, `10-geometry.tex`,
lines 803–857; the constant is tabulated in `docs/notes/arealaw2d_explicit_constant.tex`,
Section `sec:top`. -/
noncomputable def uniformAreaLawConstantExplicit (q R : ℕ) (J Δ c₀ Cent eent Cen een : ℝ) :
    ℝ :=
  uniformAreaLawConstantAt q R J Δ (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een)
    c₀ Cent eent Cen een

/-- **The area law at any upper bound for the safe-box constant.** Fix `q ≥ 1`, `R`, `J ≥ 0`
and `Δ > 0`, let `c₀, Cent, eent, Cen, een` be transport constants with `0 < c₀` satisfying the
finite-family transport bound `Scan.CollarScan.FiniteFamilyTransportBound`, and let `B` be at
least the safe-box constant `Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een`.
Then `uniformAreaLawConstantAt q R J Δ B c₀ Cent eent Cen een` is nonnegative, and every cut of
every finite induced domain, for every gapped ground state of every admissible Hamiltonian,
has regional entropy at most this constant times the number of cut edges.

This is an auxiliary result: Theorem 1.1 of the source (`00-introduction.tex`, lines 39–53)
asserts only that a constant exists. The safe-box estimate of Proposition 9.5 holds with every
larger constant, so the proof of Theorem 1.1 runs unchanged from `B`. Source: proof of
Theorem 1.1, `10-geometry.tex`, lines 803–857, and Proposition 9.5, `08-scanner.tex`,
lines 681–805. -/
theorem uniformAreaLaw_explicit_of_le (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) {c₀ Cent eent Cen een : ℝ} (hc₀ : 0 < c₀)
    (htr : Scan.CollarScan.FiniteFamilyTransportBound c₀ Cent eent Cen een) {B : ℝ}
    (hB : Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een ≤ B) :
    0 ≤ uniformAreaLawConstantAt q R J Δ B c₀ Cent eent Cen een ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstantAt q R J Δ B c₀ Cent eent Cen een *
              (edgeBoundary Λ A).card := by
  have hB₀ : 0 ≤ B :=
    (Scan.physicalBoxConstantExplicit_nonneg q R hq hJ hΔ c₀ Cent eent Cen een).trans hB
  have hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ (2 * R + 11) r ≤
      B * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := fun r hr ↦
    (Scan.boxEntropy_le_boxError_explicit q R hq hJ hΔ hc₀ htr _ (by omega) r hr).trans
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (Nat.cast_nonneg r) _))
  refine ⟨uniformAreaLawConstantOf_nonneg hq _ _, ?_⟩
  exact regionalEntropy_le_of_collar_amplification_twoFamilies_constants hq hΔ
    (sublinearCollarBound_real_of_boxEntropy_explicit (D₀ := 2 * (R : ℝ) + 11) (Ctpl := 24) q R
      hq hJ hΔ (by linarith) le_rfl hB₀ hbox hc₀ htr)
    (amplificationBound_explicit (J := J) (C₀ := max (sublinearCollarConstant q J Δ B) 1)
      q R hΔ (lt_max_of_lt_right one_pos) 100)
    (isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant _ _ _
      Geometry.isBirthSeparationConstant_birthTemplateSeparationConstant)

/-- **The area law with an explicit constant, from the transport bound.** Fix `q ≥ 1`, `R`,
`J ≥ 0` and `Δ > 0`, and let `c₀, Cent, eent, Cen, een` be transport constants with
`0 < c₀` satisfying the finite-family transport bound
`Scan.CollarScan.FiniteFamilyTransportBound`. Then the constant
`uniformAreaLawConstantExplicit q R J Δ c₀ Cent eent Cen een` is nonnegative, and every cut of
every finite induced domain, for every gapped ground state of every admissible Hamiltonian,
has regional entropy at most this constant times the number of cut edges.

This is an auxiliary result: Theorem 1.1 of the source (`00-introduction.tex`, lines 39–53)
asserts only that a constant exists, and `uniformAreaLaw` is that statement. Beyond the
hypotheses of Theorem 1.1, the only remaining input is the transport bound at constants with
`0 < c₀`; these constants are universal and do not depend on `q, R, J, Δ`, and
`Scan.CollarScan.finiteFamilyTransportBound_explicit` supplies explicit values. Source: proof
of Theorem 1.1, `10-geometry.tex`, lines 803–857; the constant is tabulated in
`docs/notes/arealaw2d_explicit_constant.tex`, Section `sec:top`. -/
theorem uniformAreaLaw_explicit (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {c₀ Cent eent Cen een : ℝ} (hc₀ : 0 < c₀)
    (htr : Scan.CollarScan.FiniteFamilyTransportBound c₀ Cent eent Cen een) :
    0 ≤ uniformAreaLawConstantExplicit q R J Δ c₀ Cent eent Cen een ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstantExplicit q R J Δ c₀ Cent eent Cen een *
              (edgeBoundary Λ A).card :=
  uniformAreaLaw_explicit_of_le q R hq hJ hΔ hc₀ htr le_rfl

/-- The constant of Theorem 1.1 as a closed-form function of `q, R, J, Δ` alone:
`uniformAreaLawConstantExplicit` at the explicit transport constants of the companion
library. Source: proof of Theorem 1.1, `10-geometry.tex`, lines 803–857; the constant is
tabulated in `docs/notes/arealaw2d_explicit_constant.tex`, Section `sec:top`. -/
noncomputable def uniformAreaLawConstantClosed (q R : ℕ) (J Δ : ℝ) : ℝ :=
  uniformAreaLawConstantExplicit q R J Δ TensorPower.ReplicaTransport.transportThreshold
    TensorPower.ReplicaTransport.transportEntropyConst
    TensorPower.ReplicaTransport.transportEntropyExponent
    TensorPower.ReplicaTransport.transportEnergyConst
    TensorPower.ReplicaTransport.transportEnergyExponent

/-- **The area law with an explicit constant.** Fix `q ≥ 1`, `R`, `J ≥ 0` and `Δ > 0`. Then
`uniformAreaLawConstantClosed q R J Δ` is nonnegative, and every cut of every finite induced
domain, for every gapped ground state of every admissible Hamiltonian, has regional entropy
at most this constant times the number of cut edges.

This is an auxiliary result with no hypothesis beyond those of Theorem 1.1
(`00-introduction.tex`, lines 39–53), which asserts only that a constant exists;
`uniformAreaLaw` is that statement. Source: proof of Theorem 1.1, `10-geometry.tex`,
lines 803–857; the constant is tabulated in `docs/notes/arealaw2d_explicit_constant.tex`,
Section `sec:top`. -/
theorem uniformAreaLaw_closed (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    0 ≤ uniformAreaLawConstantClosed q R J Δ ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstantClosed q R J Δ * (edgeBoundary Λ A).card :=
  uniformAreaLaw_explicit q R hq hJ hΔ TensorPower.ReplicaTransport.transportThreshold_pos
    Scan.CollarScan.finiteFamilyTransportBound_explicit

/-- The safe-box constant of Proposition 9.5 at the explicit transport constants of the
companion library, as a function of `q, R, J, Δ` alone. Source: Proposition 9.5,
`08-scanner.tex`, lines 681–805. -/
noncomputable def physicalBoxConstantClosed (q R : ℕ) (J Δ : ℝ) : ℝ :=
  Scan.physicalBoxConstantExplicit q R J Δ TensorPower.ReplicaTransport.transportThreshold
    TensorPower.ReplicaTransport.transportEntropyConst
    TensorPower.ReplicaTransport.transportEntropyExponent
    TensorPower.ReplicaTransport.transportEnergyConst
    TensorPower.ReplicaTransport.transportEnergyExponent

/-- The constant of Theorem 1.1 at a safe-box constant `B` and the explicit transport constants
of the companion library. At `B = physicalBoxConstantClosed q R J Δ` it is
`uniformAreaLawConstantClosed q R J Δ`. Source: proof of Theorem 1.1, `10-geometry.tex`,
lines 803–857. -/
noncomputable def uniformAreaLawConstantClosedAt (q R : ℕ) (J Δ B : ℝ) : ℝ :=
  uniformAreaLawConstantAt q R J Δ B TensorPower.ReplicaTransport.transportThreshold
    TensorPower.ReplicaTransport.transportEntropyConst
    TensorPower.ReplicaTransport.transportEntropyExponent
    TensorPower.ReplicaTransport.transportEnergyConst
    TensorPower.ReplicaTransport.transportEnergyExponent

/-- At the closed safe-box constant, `uniformAreaLawConstantClosedAt` is the closed constant of
Theorem 1.1. -/
theorem uniformAreaLawConstantClosedAt_physicalBoxConstantClosed (q R : ℕ) (J Δ : ℝ) :
    uniformAreaLawConstantClosedAt q R J Δ (physicalBoxConstantClosed q R J Δ) =
      uniformAreaLawConstantClosed q R J Δ :=
  rfl

/-- **The area law at any upper bound for the closed safe-box constant.** Fix `q ≥ 1`, `R`,
`J ≥ 0` and `Δ > 0`, and let `B ≥ physicalBoxConstantClosed q R J Δ`. Then
`uniformAreaLawConstantClosedAt q R J Δ B` is nonnegative, and every cut of every finite induced
domain, for every gapped ground state of every admissible Hamiltonian, has regional entropy at
most this constant times the number of cut edges.

This is an auxiliary result whose only hypothesis beyond those of Theorem 1.1
(`00-introduction.tex`, lines 39–53) is the bound on `B`. Source: proof of Theorem 1.1,
`10-geometry.tex`, lines 803–857. -/
theorem uniformAreaLaw_closed_of_le (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) {B : ℝ} (hB : physicalBoxConstantClosed q R J Δ ≤ B) :
    0 ≤ uniformAreaLawConstantClosedAt q R J Δ B ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstantClosedAt q R J Δ B * (edgeBoundary Λ A).card :=
  uniformAreaLaw_explicit_of_le q R hq hJ hΔ TensorPower.ReplicaTransport.transportThreshold_pos
    Scan.CollarScan.finiteFamilyTransportBound_explicit hB

end TNLean.PEPS.AreaLaw
