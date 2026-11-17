/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.NestedChebyshevViability
import QICLean.Analysis.SpectralProjectorPower
import QICLean.Analysis.TensorOperatorPower

/-!
# Words of one Chebyshev filter between two nested spectral spaces

The nested Chebyshev filter improves viability for the upper closed spectral
space into viability for the lower one. Its power is again a filter of the
same kind, with the squared suppression raised to the same power and the
low eigenvalues still at least one; the power decomposes into ordered words
of the regional operators. Every word of length `a` therefore improves the
upper target to the lower one with suppression `Delta ^ a`.

This is the repeated application of one filter in each merge, ALVV,
arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1817, for the nested
targets of Theorem `t:aisgapless`, lines 1037–1041, as used by Theorem
`t:alg2`, lines 1869–1878. The polynomial-family decomposition is an
explicit hypothesis, as in the single-filter statement.
-/

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Words of length one in a finite family of operators have the same images
as the operators themselves. Supporting ALVV, arXiv:1602.08828v2, `l:er`,
lines 597–622. -/
theorem _root_.Submodule.iSup_map_ofFn_prod_fin_one {M ι : Type*} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (A : ι → M →L[ℂ] M) (S : Submodule ℂ M) :
    (⨆ w : Fin 1 → ι, S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[ℂ] M)) =
      ⨆ i, S.map (A i : M →ₗ[ℂ] M) := by
  rw [← (Equiv.funUnique (Fin 1) ι).symm.iSup_comp]
  simp only [Equiv.funUnique_symm_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, uniqueElim_const]

/-- A common polynomial family gives one actual Chebyshev filter and its
finite tensor decomposition before any viable subspace is chosen. Every
word of length `a` in the family improves viability from the upper closed
spectral span to the lower one with the suppression raised to the power `a`,
without assuming a gap between the two cutoffs. This is the repeated
application of one filter in the merge step of ALVV, arXiv:1602.08828v2,
Theorem `t:alg1`, lines 1777–1817, to the nested targets of Theorem
`t:aisgapless`, lines 1037–1041, as used in Theorem `t:alg2`,
lines 1869–1878. The polynomial family is an explicit input here. -/
theorem exists_chebyshev_nested_word_viability_of_polynomial_family
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
        ∀ (a : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ e) delta S higher → delta < 1 →
          let grow := ⨆ w : Fin a → Fin N,
            S.map ((List.ofFn (fun j ↦ A (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ N ^ a * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ e)
              (Delta ^ a / (1 - delta) ^ 2) grow lower := by
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
  refine ⟨p, hdegree, hp0, M, hM, fun a S delta hS hdelta ↦ ?_⟩
  rw [hhigher] at hS
  have hpower : (Polynomial.aeval Hm (p.map (algebraMap ℝ ℂ))) ^ a =
      ∑ w : Fin a → Fin N, TensorProduct.mapL (List.ofFn (fun j ↦ A (w j))).prod
        (List.ofFn (fun j ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M (w j)))).prod := by
    rw [(hfilter _).trans hM, TensorProduct.pow_sum_mapL_eq_sum_words]
  simpa only [hlower, Fintype.card_fun, Fintype.card_fin] using
    (Submodule.IsViable.spectralProjector_between_cutoffs
      (𝕜 := ℂ) (M := EuclideanSpace ℂ m) (R := EuclideanSpace ℂ e) (hp.pow a) hsep.le
      (fun w : Fin a → Fin N ↦ (List.ofFn (fun j ↦ A (w j))).prod)
      (fun w : Fin a → Fin N ↦
        (List.ofFn (fun j ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M (w j)))).prod)
      hpower hS hdelta (pow_nonneg (sq_nonneg _) a))



end TNLean.MPS.AreaLaw
