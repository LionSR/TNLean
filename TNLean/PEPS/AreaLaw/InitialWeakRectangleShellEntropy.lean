/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialSafeRectangleEntropy
import TNLean.PEPS.AreaLaw.WeakRectangleShellEntropy

/-!
# Uniform weak-rectangle shell entropy at the initial exponent

The initial safe-rectangle estimate bounds the entropy of the actual shell
of the same ground vector. One nonnegative constant and one initial exponent
are chosen before every safety parameter, domain, Hamiltonian, energy,
vector, cut, parent rectangle and shell scale.

This is an auxiliary consequence at the initial existential exponent.
The pointwise safe-rectangle estimate is derived from the gapped-ground-state
hypothesis, and both the pointwise and shell estimates concern the original
vector. The arbitrary-exponent shell estimate and physical exponent
improvement remain separate results.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 590–604,
and the rectangle-shell entropy input in the proof of Proposition 9.5
(`prop:small-box`), `08-scanner.tex`, lines 717–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- One initial safe-box constant and exponent control all actual weak-rectangle
shells satisfying the cap and clearance conditions. The physical vector is the
original gapped ground vector throughout.
Source: `02-initial.tex`, lines 590–604, and `08-scanner.tex`, lines 717–729,
at the pinned manuscript revision stated above. -/
theorem exists_regionalEntropy_weak_rectangle_shell_le_rpow
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 ≤ C ∧ 0 < e₀ ∧ e₀ < 1 ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
            ∀ j L K : ℕ, j ≤ L → L ≤ Q.size →
              2 ^ K ≤ L → L < 2 ^ (K + 1) →
              D₀ * L + L ≤ D₀ * Q.size →
              regionalEntropy Λ q Ω
                (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
                C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) *
                  (Q.size : ℝ) * (L : ℝ) ^ e₀ := by
  obtain ⟨C, e₀, hC, he₀, he₀₁, hrect⟩ :=
    exists_regionalEntropy_safe_rect_le_rpow q R hq hJ hΔ
  refine ⟨C, e₀, hC, he₀, he₀₁, ?_⟩
  intro D₀ hD₀ Λ h E₀ Ω hgs A Q hsafe j L K hj hL hlo hhi hbudget
  exact IntRect.regionalEntropy_shell_le_of_safe_box
    Λ q D₀ Ω hgs.1 A Q hsafe j L K hj hL hlo hhi hbudget
    e₀ C he₀ hC (hrect D₀ hD₀ Λ h E₀ Ω hgs A)

end TNLean.PEPS.AreaLaw
