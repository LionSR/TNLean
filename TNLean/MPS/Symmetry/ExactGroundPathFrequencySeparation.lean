/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathGaussianFilter
import QICLean.ManyBody.Hamiltonian.NegativeFrequency

/-!
# Actual finite-ring correlations as negative-frequency commutators

For an exact MPS ground path, the actual Hamiltonian and ground-line
conditions give the negative-frequency identity for its ordinary connected
correlations. The original, unnormalized periodic MPS vector is used.
No correlation estimate, transfer bound or continuous minimal gauge is
assumed. The quantitative regularization and locality bound remain open.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6); applied to the physical-path argument of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953.
-/

open ManyBody Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- Ordinary connected correlations of the actual periodic MPS vector equal
the corresponding actual negative-frequency commutators. Ground energy,
least-energy ordering and the full ground line are derived from the
physical path. This is the exact spectral step of Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6); no exponential bound is
asserted without the remaining regularized time-integral argument. -/
theorem ExactMPSGroundPath.negativeFrequency_connected_identity
    (Q : ExactMPSGroundPath P) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (hN : 2 ≤ N) (A B : MPOTensor.ChainOperator d N) :
    haveI : NeZero N := ⟨by omega⟩
    let ψ := mpvState (Q.tensor γ) N
    let H := (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
    let hH : H.IsHermitian := Interaction.isHermitian_hamiltonian
      (Interaction.isHermitian_translationInvariant_term (P.hermitian γ hγ))
    ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A (toEuclideanCLM (𝕜 := ℂ) B ψ)⟫_ℂ -
        ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ *
          ⟪ψ, toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) =
      ⟪ψ, toEuclideanCLM (𝕜 := ℂ) (ManyBody.negativeFrequencyPart (H := H) hH A * B -
        B * ManyBody.negativeFrequencyPart hH A) ψ⟫_ℂ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  obtain ⟨E₀, hH, hline, hgap⟩ := hdata γ hγ N hN
  have hmin (i) : E₀ ≤ hH.eigenvalues i := by
    rcases hgap i with hi | hi
    · exact hi.ge
    · linarith
  apply ManyBody.inner_ground_connected_eq_negativeFrequency_commutator hH hmin A B
  rw [hline]

end MPSTensor
