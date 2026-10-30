/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Preparation.FiniteRingGaussianFilter
import TNLean.Lattice.GaussianFilteredGround

/-!
# Gaussian ground estimates derived from an exact physical path

One physical Hamiltonian gap supplies a single Gaussian decay constant at
every path parameter and ring length. The least energy supplied by the gap
condition agrees with the energy of the exact MPS ground line. Its spectral
gap and unique ground line therefore supply the hypotheses of the existing
Gaussian ground estimates, without assumptions on transfer operators or
continuous canonical representatives.

The first bound controls the excited component of the filtered observable
acting on the actual periodic MPS vector. The second controls a centered
observable by its Hamiltonian commutator. Both hold for the unnormalized MPS
vector, so no parameter-dependent normalization or phase is chosen.

These are necessary filter estimates for the physical-gap argument. They do
not convert a symmetric low-pass filter into an ordinary connected
correlation bound. Positive-frequency separation, exponential clustering
and the resulting uniform minimal-transfer spectral bound remain separate.

## References

* Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953,
  and Appendix C, lines 2653–2717: the exact MPS separation problem.
* Hastings, arXiv:cond-mat/0508554v3, equation `gs`, lines 237–243:
  suppression of the excited component of a Gaussian-filtered observable.
* Hastings, arXiv:0705.2024v4, equations `tighter` and `tighter2`, lines
  794–815: the centered ground-vector estimate through a commutator.
-/

open TNLean.Lattice Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The physical path's uniform gap and exact ground lines give a uniform
eigenvalue dichotomy at the actual MPS ground energy. The energy in the two
path conditions is identified by their least-energy properties.
Source: arXiv:1010.3732, Section II.F, lines 929–953; this is auxiliary
spectral data for the physical-gap argument, not its transfer conclusion. -/
theorem ExactMPSGroundPath.exists_uniform_ground_line_spectral_gap
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ E : ℝ, ∃ hH : (interactionHamiltonian (P.interaction γ) hN).IsHermitian,
        groundEigenspace (interactionHamiltonian (P.interaction γ) hN) E =
            Submodule.span ℂ {mpvState (Q.tensor γ) N} ∧
          ∀ k, hH.eigenvalues k = E ∨ E + Δ ≤ hH.eigenvalues k := by
  obtain ⟨Δ, hΔ, hgap⟩ := P.gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN
  obtain ⟨E, hEspec, hEmin, hline⟩ := Q.ground_line γ hγ N hN
  obtain ⟨E', hE'spec, hE'gap⟩ := hgap γ hγ N hN
  have hEE : E' = E := le_antisymm
    (by simpa using (hE'gap _ hEspec).1)
    (by simpa using hEmin _ hE'spec)
  subst E'
  let H := interactionHamiltonian (P.interaction γ) hN
  have hH : H.IsHermitian := interactionHamiltonian_isHermitian hN (P.hermitian γ hγ)
  refine ⟨E, hH, ?_, ?_⟩
  · have hker : groundEigenspace H E =
        LinearMap.ker (Matrix.toEuclideanLin (H - (E : ℂ) • 1)) := by
      ext x
      simp only [groundEigenspace, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
        map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Matrix.toLpLin_one,
        LinearMap.id_apply, sub_eq_zero]
    rw [hker]
    exact hline
  · intro k
    have hk : (hH.eigenvalues k : ℂ) ∈ spectrum ℂ H := by
      rw [hH.spectrum_eq_image_range]
      exact ⟨hH.eigenvalues k, ⟨k, rfl⟩, rfl⟩
    simpa using (hE'gap _ hk).2

/-- The physical gap of an exact MPS path implies Gaussian suppression of
excited ground-vector components and of centered observables, with the same
positive gap constant for every parameter and finite ring. The spectral
conditions are derived from the path; no transfer bound or clustering is
assumed. Source: Hastings, arXiv:cond-mat/0508554v3, equation `gs`, and
arXiv:0705.2024v4, equations `tighter` and `tighter2`; used as supporting
estimates for the SPC11 separation problem, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_gaussian_ground_bounds
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      ∀ (q : ℝ), 0 ≤ q → ∀ W : MPOTensor.ChainOperator d N,
        let H := interactionHamiltonian (P.interaction γ) hN
        let ψ := mpvState (Q.tensor γ) N
        let y := Matrix.toEuclideanLin (gaussianFilteredTerm q Δ H W) ψ
        ‖y - (Submodule.span ℂ {ψ}).starProjection y‖ ≤
            ‖W‖ * Real.exp (-q / 2) * ‖ψ‖ ∧
          (⟪ψ, Matrix.toEuclideanLin W ψ⟫_ℂ = 0 →
            ‖y‖ ≤ Δ⁻¹ * Real.exp (-q / 2) *
              ‖Matrix.toEuclideanLin (H * W - W * H) ψ‖) := by
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN q hq W
  obtain ⟨E, hH, hline, hgap⟩ := hdata γ hγ N hN
  let H := interactionHamiltonian (P.interaction γ) hN
  let ψ := mpvState (Q.tensor γ) N
  have hψ : ψ ∈ groundEigenspace H E := by
    rw [hline]
    exact Submodule.mem_span_singleton_self ψ
  constructor
  · simpa only [hline] using
      norm_sub_starProjection_gaussianFilteredTerm_le hq hΔ hH hgap W hψ
  · intro hcenter
    apply norm_gaussianFilteredTerm_apply_le_commutator hq hΔ hH hgap W hψ
    intro φ hφ
    rw [hline, Submodule.mem_span_singleton] at hφ
    obtain ⟨c, rfl⟩ := hφ
    rw [inner_smul_left, hcenter, mul_zero]

end MPSTensor
