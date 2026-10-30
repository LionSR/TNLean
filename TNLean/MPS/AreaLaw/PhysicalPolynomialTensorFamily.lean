/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowPolynomialMPOFamily
import QICLean.Analysis.MatrixTensorCoordinates

/-!
# Tensor decompositions of a common physical polynomial family

A fixed physical middle family represents every polynomial through the
prescribed degree cutoff. Its matrix identity induces an identity of
continuous operators under the canonical tensor-coordinate isometry.
Exchanging the factors places the retained interval first. The same
family precedes every supported exterior operator and every polynomial.

The family retains its cardinality bound and coarse open bond bound.
The source-sharp bond estimate and running time are separate questions.

## References

Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333.
-/

open Matrix QuantumCircuit
open TNLean.Lattice.Sheet
open scoped BigOperators Matrix Kronecker TensorProduct

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The common physical polynomial family gives both its literal whole-chain
matrix identity and its continuous tensor-action identity under one fixed
coordinate isometry. That isometry first separates exterior and middle
coordinates and then applies the inverse product orthonormal basis. The
same middle family precedes all supported exterior operators and every
polynomial through degree `k`. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333, with the square-derived open bond bound;
no source-sharp bond, spectral contraction or running-time assertion is made. -/
private theorem exists_common_physical_aeval_mpo_clm_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  let β := fun _ : Fin L ↦ Fin q
  let tau := (FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration β Jᶜ) ℂ).tensorProduct
    (EuclideanSpace.basisFun (FiniteProduct.Configuration β J) ℂ)).repr
  let T := U.trans Phi.symm
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ((Jᶜ : Finset (Fin L)) → Fin q) ((Jᶜ : Finset (Fin L)) → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) ∧
            T.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) =
              (∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β Jᶜ) (M r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β J) (W r))) ∘L
                T.toContinuousLinearEquiv.toContinuousLinearMap := by
  let J := interval L (a + ell) (b + ell + 1)
  let β := fun _ : Fin L ↦ Fin q
  let tau := (FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)
  obtain ⟨N, W, hN, hW, _hTrace, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, ?_⟩
  intro PL PR hPL hPR F P hP
  obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR P hP
  refine ⟨M, hM, ?_⟩
  rw [hM]
  exact Matrix.toEuclideanCLM_reindexed_kronecker_sum_intertwining tau M W

/-- The same common physical family gives a middle-first tensor decomposition
of the conjugated polynomial filter. Its fixed coordinate isometry first
separates exterior and middle, applies the inverse product orthonormal basis,
and exchanges the two tensor factors. The original matrix identity is retained.
The family and its count and natural open bond bounds precede every supported
exterior operator and polynomial choice. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, with the square-derived
bond bound; no spectral contraction, tradeoff or running-time assertion is made. -/
theorem exists_common_physical_aeval_mpo_middleFirst_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  let β := fun _ : Fin L ↦ Fin q
  let tau := (FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration β Jᶜ) ℂ).tensorProduct
    (EuclideanSpace.basisFun (FiniteProduct.Configuration β J) ℂ)).repr
  let T : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (FiniteProduct.Configuration β Jᶜ) ⊗[ℂ]
        EuclideanSpace ℂ (FiniteProduct.Configuration β J)) := U.trans Phi.symm
  let Tm : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (FiniteProduct.Configuration β J) ⊗[ℂ]
        EuclideanSpace ℂ (FiniteProduct.Configuration β Jᶜ)) :=
    T.trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (FiniteProduct.Configuration β Jᶜ))
    (EuclideanSpace ℂ (FiniteProduct.Configuration β J)))
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ((Jᶜ : Finset (Fin L)) → Fin q) ((Jᶜ : Finset (Fin L)) → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) ∧
            (Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) =
              (∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β J) (W r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β Jᶜ) (M r))) ∘L
                Tm.toContinuousLinearEquiv.toContinuousLinearMap) ∧
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β J) (W r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := FiniteProduct.Configuration β Jᶜ) (M r)) := by
  intro Ksites eK Mphys Pmid J eJ D β tau U Phi T Tm
  obtain ⟨N, W, hN, hW, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_clm_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, ?_⟩
  intro PL PR hPL hPR F P hP
  obtain ⟨M, hM, hT⟩ := hdecomp PL PR hPL hPR P hP
  refine ⟨M, hM, ?_⟩
  exact TensorProduct.intertwining_sum_mapL_commIsometry
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q))
    (L := EuclideanSpace ℂ (FiniteProduct.Configuration β Jᶜ))
    (R := EuclideanSpace ℂ (FiniteProduct.Configuration β J)) (ι := Fin N) T
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Polynomial.aeval (∑ a, F a) P))
    (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := FiniteProduct.Configuration β Jᶜ) (M r))
    (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := FiniteProduct.Configuration β J) (W r)) hT

end TNLean.MPS.AreaLaw
