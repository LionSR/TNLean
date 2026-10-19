/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawExplicitConstant
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundBound
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxStepBound

/-!
# The two-dimensional area law with a constant that iterates no recursion

The closed-form constant `uniformAreaLawConstantClosed q R J Δ` of Theorem 1.1 contains the
safe-box constant of Proposition 9.5, which is the value of the bootstrap recursion after a
fixed number of rounds. This module replaces that value by an upper bound with no iteration
left: one round is at most `A (1 + C)^(2k)`, the number of rounds is at most the round budget
`initialBoxBootstrapRoundBound q R J Δ`, and so the safe-box constant is at most
`((A + 1)(1 + C₀))^((4k)^M)` with `M` that budget. The area law then holds with the constant
of Theorem 1.1 evaluated at this bound.

This is an auxiliary result: Theorem 1.1 asserts only that a constant exists, and
`uniformAreaLaw` is that statement.

## Main results

* `physicalBoxConstantElementary`, `physicalBoxConstantClosed_le_elementary`: the bound for
  the closed safe-box constant.
* `uniformAreaLawConstantElementary`, `uniformAreaLaw_elementary`: the area law with the
  constant of Theorem 1.1 at that bound.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Theorem 1.1 (`00-introduction.tex`, lines 39–53) and its proof (`10-geometry.tex`,
lines 803–857), with the safe-box estimate of Proposition 9.5 (`08-scanner.tex`,
lines 681–805). The constant is tabulated in `docs/notes/arealaw2d_explicit_constant.tex`,
Section `sec:top`. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

open Scan

/-- The bound `((A + 1)(1 + C₀))^((4k)^M)` for the closed safe-box constant, where `A` is the
prefactor of one bootstrap round at the explicit transport constants, `C₀` the explicit
initial constant, `k = ⌈1/ν⌉` at the initial exponent and `M` the round budget. Source: proof
of Proposition 9.5, `08-scanner.tex`, lines 681–805. -/
noncomputable def physicalBoxConstantElementary (q R : ℕ) (J Δ : ℝ) : ℝ :=
  ((boxStepPrefactor q R (initialBoxExponent_pos_and_lt_one q R J Δ).1
        (initialBoxExponent_pos_and_lt_one q R J Δ).2 J Δ
        (latticeTruncationRadiusConstant R J Δ 2)
        TensorPower.ReplicaTransport.transportThreshold
        TensorPower.ReplicaTransport.transportEntropyConst
        TensorPower.ReplicaTransport.transportEntropyExponent
        TensorPower.ReplicaTransport.transportEnergyConst
        TensorPower.ReplicaTransport.transportEnergyExponent + 1) *
      (1 + initialBoxConstantExplicit q R J Δ)) ^
    ((2 * (2 * boxStepExponent (initialBoxExponent q R J Δ))) ^
      initialBoxBootstrapRoundBound q R J Δ)

/-- For `q ≥ 1`, `J ≥ 0` and `Δ > 0`, the closed safe-box constant is at most
`physicalBoxConstantElementary q R J Δ`. Source: proof of Proposition 9.5, `08-scanner.tex`,
lines 681–805. -/
theorem physicalBoxConstantClosed_le_elementary (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    physicalBoxConstantClosed q R J Δ ≤ physicalBoxConstantElementary q R J Δ :=
  physicalBoxConstantExplicit_le_pow_pow q R hq hJ hΔ _ _ _ _ _
    (boxBootstrapRounds_initial_le q R J Δ)

/-- The constant of Theorem 1.1 at the safe-box bound `physicalBoxConstantElementary`, a
function of `q, R, J, Δ` in which no recursion is iterated. Source: proof of Theorem 1.1,
`10-geometry.tex`, lines 803–857. -/
noncomputable def uniformAreaLawConstantElementary (q R : ℕ) (J Δ : ℝ) : ℝ :=
  uniformAreaLawConstantClosedAt q R J Δ (physicalBoxConstantElementary q R J Δ)

/-- **The area law with a constant that iterates no recursion.** Fix `q ≥ 1`, `R`, `J ≥ 0` and
`Δ > 0`. Then `uniformAreaLawConstantElementary q R J Δ` is nonnegative, and every cut of
every finite induced domain, for every gapped ground state of every admissible Hamiltonian,
has regional entropy at most this constant times the number of cut edges.

This is an auxiliary result with no hypothesis beyond those of Theorem 1.1
(`00-introduction.tex`, lines 39–53), which asserts only that a constant exists;
`uniformAreaLaw` is that statement. Source: proof of Theorem 1.1, `10-geometry.tex`,
lines 803–857. -/
theorem uniformAreaLaw_elementary (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    0 ≤ uniformAreaLawConstantElementary q R J Δ ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstantElementary q R J Δ * (edgeBoundary Λ A).card :=
  uniformAreaLaw_closed_of_le q R hq hJ hΔ (physicalBoxConstantClosed_le_elementary q R hq hJ hΔ)

end TNLean.PEPS.AreaLaw
