/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawTheorem

/-!
# The two-dimensional area law with an explicit constant

The proof of Theorem 1.1 of the area-law manuscript produces its constant from the
constants of Propositions 9.6, 10.2 and 11.2. This module assembles that constant from the
named constants of the three propositions, so that the only remaining input is a tuple of
transport constants `c₀, Cent, eent, Cen, een` satisfying the finite-family transport bound
`Scan.CollarScan.FiniteFamilyTransportBound`. These constants are universal: they do not
depend on `q, R, J, Δ`, the domain, the Hamiltonian, the state or the cut.

## Main results

* `uniformAreaLawConstantExplicit`: the constant of Theorem 1.1 as a function of
  `q, R, J, Δ` and the transport constants.
* `uniformAreaLaw_explicit`: Theorem 1.1 with this constant, for every tuple of transport
  constants satisfying the transport bound.
* `uniformAreaLawConstantClosed`, `uniformAreaLaw_closed`: the constant at the explicit
  transport constants of the companion library, and Theorem 1.1 with it, with no hypothesis
  beyond those of Theorem 1.1.

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
a function of the Hamiltonian parameters `q, R, J, Δ` and the transport constants
`c₀, Cent, eent, Cen, een`:
* `Cbox = Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een` (Proposition 9.5);
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
noncomputable def uniformAreaLawConstantExplicit (q R : ℕ) (J Δ c₀ Cent eent Cen een : ℝ) :
    ℝ :=
  let Cbox := Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een
  let C₀ := max (sublinearCollarConstant q J Δ Cbox) 1
  let N₁ := sublinearCollarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10) c₀
    Cent eent Cen een
  let C₂ := amplificationConstantExplicit q R J Δ C₀ 100
  let N₂ := max (amplificationThresholdExplicit q R J Δ C₀ 100)
    (Exponents.collarRadiusThreshold C₂ 1)
  uniformAreaLawConstantOf q C₂ (twoFamilyDecompositionConstant (2 * (R : ℝ) + 11) 24
    (uniformAreaLawScale N₁ N₂ C₂) Geometry.birthTemplateSeparationConstant)

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
              (edgeBoundary Λ A).card := by
  refine ⟨uniformAreaLawConstantOf_nonneg hq _ _, ?_⟩
  exact regionalEntropy_le_of_collar_amplification_twoFamilies_constants hq hΔ
    (sublinearCollarBound_real_explicit (D₀ := 2 * (R : ℝ) + 11) (Ctpl := 24) q R hq hJ hΔ
      (by linarith) le_rfl c₀ Cent eent Cen een hc₀ htr)
    (amplificationBound_explicit (J := J)
      (C₀ := max (sublinearCollarConstant q J Δ
        (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een)) 1)
      q R hΔ (lt_max_of_lt_right one_pos) 100)
    (isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant _ _ _
      Geometry.isBirthSeparationConstant_birthTemplateSeparationConstant)

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

end TNLean.PEPS.AreaLaw
