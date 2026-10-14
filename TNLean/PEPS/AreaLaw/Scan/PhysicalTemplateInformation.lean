/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import TNLean.PEPS.AreaLaw.Scan.TemplateFinalInformation

/-!
# Original-template information from the physical safe-box bootstrap

Discharge the genuine uniform fixed-exponent safe-box premise of the
actual-template information theorem using the physical bootstrap. The
conclusion concerns the same original gapped ground state and literal
template regions. The source template separation and collar scale condition
remain explicit; no safe-box estimate or scanner certificate is assumed.

This additive theorem leaves the accepted cut/volume packaging unchanged.
Its imported physical source chain still requires validation and integration;
it does not establish the repair-tree construction or the full area law.
See `docs/paper-gaps/arealaw2d_physical_template_information_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Proposition 9.5, lines 681--805, and the information
conclusion of Proposition 9.6, lines 808--944, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved by composition; no upstream Lean proof text reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Geometry

/-- Both final information powers for each separated template in the
original physical gapped ground state. The physical safe-box bootstrap
supplies the fixed-exponent entropy estimate internally. Constants and a
single threshold precede all finite instances; `D₀` and `Ctpl` are fixed
parameters. The geometric separation and `L ≤ s₀` remain explicit.
Source: the information conclusion of Proposition 9.6, `08-scanner.tex`,
lines 808--944, using Proposition 9.5, lines 681--805. -/
theorem exists_template_final_mutualInformation
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD₀ : 2 * R + 10 < D₀)
    {J Δ Ctpl : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCtpl : 24 ≤ Ctpl) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n s₀ : ℕ, N ≤ n →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Template Ctpl n s₀),
            T.IsSeparated D₀ (boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ ≤ s₀ →
            let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
            let X := A.filter fun x ↦ x.val ∈ T.points
            let S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T.points L
            let β := fun _ : Site Λ ↦ Fin q
            2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                C * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
              2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨Cbox, hCbox, hbox⟩ := exists_boxEntropy_le_boxError q R hq hJ hΔ
  exact exists_template_final_mutualInformation_of_boxEntropy q R D₀ hq
    (by omega) hJ hΔ hCtpl hCbox.le (hbox D₀ hD₀)

end TNLean.PEPS.AreaLaw.Scan
