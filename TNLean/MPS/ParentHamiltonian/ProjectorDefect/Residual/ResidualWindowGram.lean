/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowCoordinates
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGram

/-!
# Gram operators of the two residual windows

For a full interval of length \((K+M)L+r\), the left window is the
aligned prefix of length \((K+M)L\) and the right window has length
\(ML+r\). Their common interval contains \(M\) blocked sites.
The right window Gram is the direct sum of correlated residual Grams
indexed by the blocked prefix configurations. The left window Gram is
the direct sum of ordinary prefix Grams indexed by the original tail.

Consequently, neither spectator increases a boundary-map norm or a Gram
error. The right error has coefficient one when the correlated tail is
contractive, as follows from its derived cyclic support projection.
The operator factorizations require no normalization or injectivity;
the error bounds themselves require no primitivity. No three-interval
projector defect estimate or all-residue spectral gap is asserted here.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius
namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D E L : ℕ}

/-- The right window Gram is the finite direct sum, over the blocked prefix,
of the correlated residual Gram. This exact identity includes empty
configuration sets and zero lengths. Source: the boundary contraction in
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem residualWindowRightMapES_adjoint_comp_self
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    (residualWindowRightMapES A B V K M r).adjoint.comp
        (residualWindowRightMapES A B V K M r) =
      ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
        ((blockedResidualBoundaryMapES A L B V M r).adjoint.comp
          (blockedResidualBoundaryMapES A L B V M r)) := by
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.inner_eq_sum_inner_rightFiber y]
  simp_rw [ContinuousLinearMap.rightFiber_rightFiberwiseMap]
  simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change ⟪residualWindowRightMapES A B V K M r y,
      residualWindowRightMapES A B V K M r x⟫_ℂ =
    ∑ u, ⟪blockedResidualBoundaryMapES A L B V M r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) (rectangularBoundaryFamilyFiberₗ u y)),
      blockedResidualBoundaryMapES A L B V M r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) (rectangularBoundaryFamilyFiberₗ u x))⟫_ℂ
  simp_rw [inner_blockedResidualBoundaryMapES_eq_sum_groundSpaceMapES, PiLp.inner_apply]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr₂ fun τ _ v _ => ?_
  change ⟪Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
      Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u y),
    Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
      Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u x)⟫_ℂ =
    ⟪Matrix.trace (Kraus.evalWord B (List.ofFn v) *
      (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u y)),
    Matrix.trace (Kraus.evalWord B (List.ofFn v) *
      (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x))⟫_ℂ
  simp only [Matrix.mul_assoc]

/-- The left window Gram is the finite direct sum, over the original tail,
of the ordinary blocked-prefix Gram at length \(K+M\).
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii). -/
theorem residualWindowLeftMapES_adjoint_comp_self
    (B : MPTensor (Fin L → α) (Fin E)) (K M r : ℕ) :
    (residualWindowLeftMapES B K M r).adjoint.comp
        (residualWindowLeftMapES B K M r) =
      boundaryFiberwiseMap (Fin r → α) (groundSpaceGram B (K + M)) := by
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_boundaryFiberwiseMap]
  simp_rw [groundSpaceGram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.appendEquiv K M) _ _ fun p => ?_
  change ⟪Matrix.trace ((Kraus.evalWord B (List.ofFn p.1) *
      Kraus.evalWord B (List.ofFn p.2)) * boundaryFamilyEquiv (Fin r → α) y τ),
    Matrix.trace ((Kraus.evalWord B (List.ofFn p.1) *
      Kraus.evalWord B (List.ofFn p.2)) * boundaryFamilyEquiv (Fin r → α) x τ)⟫_ℂ =
    ⟪Matrix.trace (Kraus.evalWord B (List.ofFn (Fin.append p.1 p.2)) *
      boundaryFamilyEquiv (Fin r → α) y τ),
    Matrix.trace (Kraus.evalWord B (List.ofFn (Fin.append p.1 p.2)) *
      boundaryFamilyEquiv (Fin r → α) x τ)⟫_ℂ
  simp only [List.ofFn_fin_append, Kraus.evalWord_append]

/-- Prefix spectators do not increase the norm of the residual boundary map.
The bound is uniform in the prefix length and includes zero lengths. -/
theorem norm_residualWindowRightMapES_le
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    ‖residualWindowRightMapES A B V K M r‖ ≤ ‖blockedResidualBoundaryMapES A L B V M r‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, sq,
    ← ContinuousLinearMap.norm_adjoint_comp_self, residualWindowRightMapES_adjoint_comp_self]
  exact ContinuousLinearMap.norm_rightFiberwiseMap_le _

/-- Original-tail spectators do not increase the norm of the aligned boundary
map. The bound is uniform in the tail length and includes zero lengths. -/
theorem norm_residualWindowLeftMapES_le
    (B : MPTensor (Fin L → α) (Fin E)) (K M r : ℕ) :
    ‖residualWindowLeftMapES B K M r‖ ≤ ‖groundSpaceMapES B (K + M)‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, sq,
    ← ContinuousLinearMap.norm_adjoint_comp_self, residualWindowLeftMapES_adjoint_comp_self]
  exact norm_boundaryFiberwiseMap_le _ _

/-- The full residual window contraction factors through the left window
by the correlated tail map, as an equality of operators. No injectivity
or normalization is required. Source: DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem residualWindowLeftMapES_comp_correlatedTailMapES
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    (residualWindowLeftMapES B K M r).comp (correlatedTailMapES A V r) =
      residualWindowMapES A B V K M r := by
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  exact residualWindowLeftMapES_correlatedTailFamily A B V K M r Y

/-- A contractive correlated tail and arbitrary prefix spectators preserve
the coefficient-one primitive Gram error bound. No factor depends on
the prefix or original-tail length. Source: the Gram comparison underlying
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii). -/
theorem norm_residualWindowRightMapES_gram_sub_limit_le
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (K M r : ℕ)
    (hC : ‖correlatedTailMapES A V r‖ ≤ 1) :
    ‖(residualWindowRightMapES A B V K M r).adjoint.comp
        (residualWindowRightMapES A B V K M r) -
      ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
        (residualBoundaryGramLimit A V ρ htr r)‖ ≤
      ‖groundSpaceGram B M - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ := by
  rw [residualWindowRightMapES_adjoint_comp_self, ← ContinuousLinearMap.rightFiberwiseMap_sub]
  exact (ContinuousLinearMap.norm_rightFiberwiseMap_le _).trans
    (norm_blockedResidualBoundaryMapES_gram_sub_limit_le A B V ρ htr M r hC)

/-- Original-tail spectators preserve the coefficient-one ordinary prefix
Gram error bound. No primitivity or fixed-point equation is needed for
this direct-sum inequality. Source: the Gram comparison underlying
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii). -/
theorem norm_residualWindowLeftMapES_gram_sub_limit_le
    (B : MPTensor (Fin L → α) (Fin E)) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (K M r : ℕ) :
    ‖(residualWindowLeftMapES B K M r).adjoint.comp
        (residualWindowLeftMapES B K M r) -
      boundaryFiberwiseMap (Fin r → α) (Matrix.gramReshuffle (fixedPointProj ρ htr))‖ ≤
      ‖groundSpaceGram B (K + M) - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ := by
  rw [residualWindowLeftMapES_adjoint_comp_self, ← boundaryFiberwiseMap_sub]
  exact norm_boundaryFiberwiseMap_le _ _

/-- Physical reindexing preserves the full residual window Gram.
Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451; this identity supplies the full supported inverse in
Nachtergaele's commutation (ii), equation (3.15), lines 1567--1574. -/
theorem residualWindowMapES_adjoint_comp_self
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    (residualWindowMapES A B V K M r).adjoint.comp (residualWindowMapES A B V K M r) =
      (blockedResidualBoundaryMapES A L B V (K + M) r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V (K + M) r) := by
  rw [residualWindowMapES_eq_reindex_blockedResidualBoundaryMapES,
    ContinuousLinearMap.adjoint_comp]
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residualWindowConfigEquiv L K M r).symm
  have hU : U.toContinuousLinearMap.adjoint.comp U.toContinuousLinearMap = 1 :=
    U.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp U.norm_map
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc U.toContinuousLinearMap.adjoint
    U.toContinuousLinearMap, hU]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
end MPSTensor
