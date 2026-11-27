/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalPolynomialTensorFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.PhysicalLowEnergyCloseness

import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.IndependentFiveRegionResidual

/-!
# A Chebyshev filter between nested spectral spaces

A common polynomial family that contains a Hamiltonian's Chebyshev filter gives,
on every viable subspace, one actual improving step from an upper spectral space to
a nested lower one. This is the filtering step of ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, used by the physical low-energy families
in `TNLean.MPS.AreaLaw.PhysicalLowEnergyFamily`.

**Local fix (closed cutoffs and filter sign):** The spectral estimates use
closed cutoffs; positivity of the unsquared Chebyshev filter is not claimed.
See the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

open ManyBody (interval)

open Matrix

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw


/-- A common polynomial family gives one actual Chebyshev filter and its
finite tensor decomposition before any viable subspace is chosen. It
improves viability from the upper closed spectral span to the lower one,
without assuming a gap between them. The polynomial family is an explicit
input to this auxiliary; the physical theorem constructs it separately.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1037–1041. -/
theorem exists_chebyshev_nested_viability_of_polynomial_family
    {σ ι m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
    {N degree : ℕ}
    (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis ι ℂ (EuclideanSpace ℂ σ)) (lam : ι → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)))
    (eta0 eta1 upper : ℝ) (hsep : eta0 < eta1) (hend : eta1 ≤ upper)
    (hnorm : ‖B‖ ≤ upper) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let lower := (Submodule.spectralSpanLE v lam eta0).map Tm.toLinearEquiv.toLinearMap
    let higher := (Submodule.spectralSpanLE v lam eta1).map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp
      (-2 * (degree : ℝ) * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    ∃ p : Polynomial ℝ, p.natDegree = degree ∧ p.eval eta0 = 1 ∧
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
              (Polynomial.aeval B (p.map (algebraMap ℝ ℂ))) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL (A r)
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)) ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ e) delta S higher → delta < 1 →
          let grow := ⨆ r : Fin N, S.map (A r).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ e)
              (Delta / (1 - delta) ^ 2) grow lower := by
  intro A lower higher Delta
  -- Coincident endpoints obtain only the canonical coordinates, without a gap.
  obtain ⟨hK, _htrivial, hupper, hmap⟩ :=
    Matrix.exists_canonical_isometric_spectral_data B hB v lam hv eta0 eta0 upper rfl hnorm Tm
  let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric := hK
  have hhigher : higher = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta1}) := hmap eta1
  have hlower : lower = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta0}) := hmap eta0
  obtain ⟨p, hdegree, hp0, hp⟩ :=
    Submodule.exists_isSpectralProjector_chebyshev Hm hHm rfl degree hsep hend hupper
  obtain ⟨M, hM⟩ := hdecomp (p.map (algebraMap ℝ ℂ))
    (Polynomial.natDegree_map_le.trans hdegree.le)
  have hfilter (Q : Polynomial ℂ) : Polynomial.aeval Hm Q =
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q)) :=
    (Polynomial.aeval_algHom_apply
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B) Q).trans
      (congrArg Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
        (Polynomial.aeval_algHom_apply
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)).toAlgEquiv.toAlgHom B Q))
  refine ⟨p, hdegree, hp0, M, hM, fun S delta hS hdelta ↦ ?_⟩
  rw [hhigher] at hS
  simpa only [hlower, Fintype.card_fin] using
    (Submodule.IsViable.spectralProjector_between_cutoffs
      (𝕜 := ℂ) (M := EuclideanSpace ℂ m) (R := EuclideanSpace ℂ e) hp hsep.le A
      (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r))
      ((hfilter _).trans hM) hS hdelta (sq_nonneg _))

end TNLean.MPS.AreaLaw
