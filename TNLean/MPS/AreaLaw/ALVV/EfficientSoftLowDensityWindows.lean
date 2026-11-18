/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.BufferedSpectralNormPerturbation
import QICLean.Analysis.NestedChebyshevViability
import QICLean.Analysis.MatrixTensorCoordinates
import QICLean.Analysis.ViableSubspaceErrorReduction

/-!
# Window comparisons through a soft Hamiltonian and its approximant

Three Hermitian matrices are compared: the original Hamiltonian `H`, the exact soft
Hamiltonian `G` and a represented approximant `B` with `‖G - B‖ ≤ ξ`. The two buffered
windowed comparisons of `G` with `H` and the norm perturbation from `G` to `B` compose into
two windows of `B` that bracket the original low-energy band of width `η` from both sides,
separated by `w - ρ`. A polynomial matrix decomposition of `B` then gives the nested
Chebyshev improvement between the two windows of `B`. These spectral auxiliaries support the
efficient low-density improving family of ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`,
lines 1424–1437, built from the low-density family of `t:aisgapless`, lines 1027–1041.
-/

open Matrix
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The loss of one norm-perturbation step at cutoff `c`, buffer `w / 2` and accuracy `ξ`,
for an exact Hamiltonian of norm `R`, as in the buffered spectral perturbation bound.
Numerical auxiliary to ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`,
lines 1446–1457. -/
noncomputable def softWindowPerturbationLoss (R xi w c : ℝ) : ℝ :=
  (⌈(c - min (c - 1) (-(R + xi))) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w / 2 + xi) ^ 2

/-- The perturbation loss is nonnegative. Numerical auxiliary to ALVV, arXiv:1602.08828v2,
`t:aisgaplessefficient`, lines 1446–1457. -/
theorem softWindowPerturbationLoss_nonneg (R xi w c : ℝ) :
    0 ≤ softWindowPerturbationLoss R xi w c := by
  unfold softWindowPerturbationLoss
  positivity

/-- **Bracketing the original band by two windows of the approximant.** Let `H` have the
complete eigenbasis `bH`, and suppose the soft Hamiltonian `G` satisfies the two buffered
comparisons with `H` at the bands of widths `η - 3 w` and `η - w / 2`, with buffer `w / 2`.
If `‖G - B‖ ≤ ξ`, the windows of `B` at `c₁ = μ + η - w` and `c₀ = μ + η - 2 w + ρ₁` satisfy
`B(c₁) ⊆ H(E + η)` and `H(E + η - 3 w) ⊆ B(c₀)` up to explicit losses. Spectral auxiliary
to ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1446–1457. -/
theorem soft_low_density_window_closeness {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G B : Matrix σ σ ℂ} (hG : G.IsHermitian) (hB : B.IsHermitian)
    (bH : OrthonormalBasis σ ℂ (EuclideanSpace ℂ σ)) (aH : σ → ℝ)
    (E mu eta w rho1 xi L1 L2 : ℝ) (hxi : 0 < xi) (hw : 0 < w) (hL2 : 0 ≤ L2)
    (herr : ‖G - B‖ ≤ xi)
    (hR1 : Submodule.IsCloseTo L1
      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues
        (mu + (eta - 3 * w) + rho1 + w / 2))
      (Submodule.spectralSpanLE bH aH (E + (eta - 3 * w))))
    (hR2 : Submodule.IsCloseTo L2
      (Submodule.spectralSpanLE bH aH (E + (eta - w / 2) + w / 2))
      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (mu + (eta - w / 2)))) :
    let c1 := mu + eta - w
    let c0 := mu + eta - 2 * w + rho1
    let R := ‖G‖
    Submodule.IsCloseTo (2 * (L2 + softWindowPerturbationLoss R xi w c1))
      (Submodule.spectralSpanLE bH aH (E + eta))
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c1) ∧
    Submodule.IsCloseTo (2 * (softWindowPerturbationLoss R xi w (c0 - w / 2) + L1))
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c0)
      (Submodule.spectralSpanLE bH aH (E + (eta - 3 * w))) := by
  intro c1 c0 R
  have hw2 : 0 < w / 2 := by positivity
  constructor
  · obtain ⟨-, hP⟩ := hG.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hB c1 xi (w / 2)
      hxi hw2 herr
    have hc : c1 + w / 2 = mu + (eta - w / 2) := by dsimp only [c1]; ring
    rw [hc] at hP
    have hE : E + (eta - w / 2) + w / 2 = E + eta := by ring
    rw [hE] at hR2
    exact hR2.trans hP hL2
  · obtain ⟨hP, -⟩ := hG.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hB (c0 - w / 2) xi
      (w / 2) hxi hw2 herr
    have hc : c0 - w / 2 + w / 2 = c0 := by ring
    rw [hc] at hP
    have hc' : mu + (eta - 3 * w) + rho1 + w / 2 = c0 - w / 2 := by dsimp only [c0]; ring
    rw [hc'] at hR1
    exact hP.trans hR1 (softWindowPerturbationLoss_nonneg _ _ _ _)

/-- **Nested Chebyshev improvement for a decomposed approximant.** If every polynomial of
degree at most `k` in a Hermitian matrix `B` is a Kronecker sum through a fixed family `W` of
middle matrices, then for cutoffs `c₀ < c₁ ≤ M` with `‖B‖ ≤ M`, the family `W` improves every
subspace viable for the window of `B` at `c₁` into one viable for the window at `c₀`, with
contraction `(2 e^{-2 k √((c₁ - c₀) / (M - c₀))})²`. Auxiliary to ALVV, arXiv:1602.08828v2,
`t:aisgaplessefficient`, lines 1424–1437, and `t:aisgapless`, lines 1037–1041. -/
theorem soft_low_density_chebyshev_viability
    {sigma mu nu : Type*} [Fintype sigma] [DecidableEq sigma]
    [Fintype mu] [Fintype nu] [DecidableEq nu] {n k : ℕ}
    (split : sigma ≃ mu × nu) (B : Matrix sigma sigma ℂ) (hB : B.IsHermitian)
    (W : Fin n → Matrix nu nu ℂ)
    (hpoly : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∃ M : Fin n → Matrix mu mu ℂ,
        Polynomial.aeval B Q = (∑ i, M i ⊗ₖ W i).submatrix split split)
    (c0 c1 M : ℝ) (hsep : c0 < c1) (hend : c1 ≤ M) (hNorm : ‖B‖ ≤ M) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
    let Phi := ((EuclideanSpace.basisFun mu ℂ).tensorProduct
      (EuclideanSpace.basisFun nu ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ mu) (EuclideanSpace ℂ nu))
    let A := fun i : Fin n ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := nu) (W i)
    let lower := (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c0).map
      Tm.toLinearEquiv.toLinearMap
    let higher := (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c1).map
      Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((c1 - c0) / (M - c0)))) ^ 2
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ nu)) (delta : ℝ),
      Submodule.IsViable (F := EuclideanSpace ℂ mu) delta S higher → delta < 1 →
      let grow := ⨆ i : Fin n, S.map (A i).toLinearMap
      Module.finrank ℂ grow ≤ n * Module.finrank ℂ S ∧
        Submodule.IsViable (F := EuclideanSpace ℂ mu) (Delta / (1 - delta) ^ 2) grow lower := by
  classical
  intro U Phi Tm A lower higher Delta
  have hTensorDecomp (Q : Polynomial ℂ) (hQ : Q.natDegree ≤ k) :
      ∃ M : Fin n → Matrix mu mu ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) (Polynomial.aeval B Q) ∘L
          Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ i, TensorProduct.mapL (A i)
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := mu) (M i)) := by
    obtain ⟨M, hM⟩ := hpoly Q hQ
    exact ⟨M, Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
      split M W (Polynomial.aeval B Q) hM⟩
  obtain ⟨_p, _hpdeg, _hpeval, _M, _hdec, hview⟩ :=
    Matrix.exists_chebyshev_nested_viability_of_polynomial_family (degree := k)
      B hB hB.eigenvectorBasis hB.eigenvalues hB.toEuclideanCLM_eigenvectorBasis
      W Tm hTensorDecomp c0 c1 M hsep hend hNorm
  exact hview

end TNLean.MPS.AreaLaw.ALVV
