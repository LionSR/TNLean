/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocol

/-!
# Retained norm of the distributed protocol

Section 8.1 of the polynomial-PEPS manuscript stresses that the protocol "does not rely on
renormalizing an exponentially small success amplitude" (`07-assembly.tex:50–51`). For a
protocol with the bounds of Proposition 7.1 consumed by §8, the final reference vector is
`Ω ⊗ Ξ` with `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1` (`eq:reference-junk`), and the actual final vector `Ψ`
lies within `C² L⁻¹⁷` of it. Hence

* `1 - C L⁻⁵⁷ - C² L⁻¹⁷ ≤ ‖Ψ‖`;
* the physical density `ρ = Tr_private |Ψ⟩⟨Ψ|` satisfies
  `1 - Re Tr ρ ≤ 2 (C L⁻⁵⁷ + C² L⁻¹⁷)`.

Neither estimate needs a smallness hypothesis on the losses, and no vector is normalized.
The protocol and its bounds are the hypothesis `DyadicProtocol.IsDistributionProtocol`; this
module does not construct it.

## Main results

* `TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol.retained_norm_and_trace_le`:
  the two estimates for the actual final vector of a protocol.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `eq:reference-junk`, the bound
  `‖Ψ - Ω ⊗ Ξ‖ ≤ C L⁻¹⁷` and the paragraph after `eq:protocol-density`,
  `07-assembly.tex:18–51`; immutable revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  These are original proofs; no OpenAI Lean code is copied or adapted.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol
open TNLean.Lattice.PartyCircuit

open TNLean.Lattice.PartyCircuit

variable {L q : ℕ} {P : Type} [Fintype P] {D : DyadicProtocol L q P} {Ω : StateSpace L q}
  {C_N C_K C_E : ℝ} {b k r : ℕ}

/-- **Retained norm and trace of the protocol.** For a protocol with the bounds of §8 on a
square of side `L ≥ 1`, with count constant `C_N`, error constant `C_E ≥ 0` and `‖Ω‖ = 1`,
the actual final vector `Ψ` satisfies `1 - C_E L⁻⁵⁷ - C_N C_E L⁻¹⁷ ≤ ‖Ψ‖`, and its physical
density `ρ` satisfies `1 - Re Tr ρ ≤ 2 (C_E L⁻⁵⁷ + C_N C_E L⁻¹⁷)`. No upper bound on the losses
is assumed.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `eq:reference-junk` and the
paragraph following `eq:protocol-density`, `07-assembly.tex:18–51`. -/
theorem retained_norm_and_trace_le (h : D.IsDistributionProtocol Ω C_N C_K C_E b k r)
    (hL : 1 ≤ L) (hC : 0 ≤ C_E) (hΩ : ‖Ω‖ = 1) :
    1 - C_E / (L : ℝ) ^ 57 - C_N * C_E / (L : ℝ) ^ 17 ≤ ‖D.readout (D.trajectory D.changes)‖ ∧
      1 - D.physicalDensity.trace.re ≤
        2 * (C_E / (L : ℝ) ^ 57 + C_N * C_E / (L : ℝ) ^ 17) := by
  classical
  obtain ⟨Ξ, hΞ, hlower, href⟩ := h.reference_changes
  exact protocol_norm_and_trace_deficit_le
    (fun t ↦ ((D.step t).eval : Mem (D.layout t) →ₗ[ℂ] Mem (D.layout (t + 1))))
    D.trajectory D.reference hL hC hC h.changes_le
    (fun t _ v ↦ D.norm_step_eval_le t v) D.norm_reference_zero.le D.trajectory_zero
    (fun t _ ↦ D.trajectory_succ t) h.reference_step D.readout.toLinearIsometry Ω Ξ hΩ hΞ
    hlower href

end TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol
