/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LimitingGramMetric
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Mixed Gram of overlapping spectator boundary maps

This file computes the mixed Gram between the tail and left spectator boundary
maps in the common ambient space used by Nachtergaele's martingale condition C3.
The calculation is exact: after fixing the prefix spectator \(u\) and final-site
spectator \(j\), the overlap is the length-\(l\) MPS Gram pairing of the two virtual
matrices obtained at the ends of the overlap.

The identity below is reconstructed directly from the boundary-map definitions,
word factorization, and trace cyclicity. It is not stated in this form by FNW or
Nachtergaele. The sourced target is the projector defect in Nachtergaele,
arXiv:cond-mat/9410110, equation (2.4); the rational numerical estimate is quoted
after that equation and in Section 6, equation (6.1). No numerical estimate is
asserted here.

## Main results

* `inner_tailBoundaryMapES_adjoint_leftBoundaryMapES`
* `inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_centered`
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

open scoped Matrix.Norms.Frobenius

/-- Three consecutive configuration blocks are equivalent to a configuration on
their concatenated chain. -/
private def cfgAppendThreeEquiv (d K l R : ℕ) :
    Cfg d K × (Cfg d l × Cfg d R) ≃ Cfg d (K + (l + R)) :=
  (Equiv.prodCongr (Equiv.refl (Cfg d K)) (Fin.appendEquiv l R)).trans
    (Fin.appendEquiv K (l + R))

@[simp]
private theorem cfgAppendThreeEquiv_apply (d K l R : ℕ)
    (u : Cfg d K) (τ : Cfg d l) (j : Cfg d R) :
    cfgAppendThreeEquiv d K l R (u, (τ, j)) = Fin.append u (Fin.append τ j) := rfl

/-- Exact mixed-Gram identity for the overlapping windows in Nachtergaele's C3
geometry (arXiv:cond-mat/9410110, equation (2.4)).

For a prefix spectator \(u\) and a one-site spectator \(j\), the tail boundary
matrix entering the \(l\)-site overlap is \(A^j X_u\), while the left boundary
matrix is \(Z_j A^u\). Thus the mixed Gram is a sum of length-\(l\) ground-space
Gram pairings with exactly this multiplication order.

This is an algebraic identity reconstructed from the definitions, not the FNW
contraction estimate quoted by Nachtergaele after equation (2.4) and in equation
(6.1). -/
theorem inner_tailBoundaryMapES_adjoint_leftBoundaryMapES
    (A : MPSTensor d D) (K l : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (y : BoundaryFamilySpace (D := D) (Cfg d 1)) :
    inner ℂ x ((tailBoundaryMapES A K (l + 1)).adjoint
      (leftBoundaryMapES A (K + l) 1 y)) =
      ∑ u : Cfg d K, ∑ j : Cfg d 1,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          (groundSpaceGram A l
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
              (boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u)))) := by
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  trans ∑ p : Cfg d K × (Cfg d l × Cfg d 1),
      inner ℂ
        ((tailBoundaryMapES A K (l + 1) x) (cfgAppendThreeEquiv d K l 1 p))
        ((leftBoundaryMapES A (K + l) 1 y) (cfgAppendThreeEquiv d K l 1 p))
  · symm
    apply Fintype.sum_equiv (cfgAppendThreeEquiv d K l 1)
    intro p
    rfl
  · simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [groundSpaceGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right,
      groundSpaceMapES_frobeniusEquivEuclidean_apply,
      groundSpaceMapES_frobeniusEquivEuclidean_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro τ _
    have hTailPrefix :
        Fin.append u (Fin.append τ j) ∘ Fin.castAdd (l + 1) = u := by
      ext i
      simp [Fin.append_left]
    have hTailSuffix :
        Fin.append u (Fin.append τ j) ∘ Fin.natAdd K = Fin.append τ j := by
      ext i
      simp [Fin.append_right]
    have hLeftPrefix :
        Fin.append u (Fin.append τ j) ∘ Fin.castAdd 1 = Fin.append u τ := by
      ext i
      have hi := congrFun (Fin.append_assoc u τ j) (Fin.castAdd 1 i)
      apply congrArg Fin.val
      simpa using hi.symm
    have hLeftSuffix :
        Fin.append u (Fin.append τ j) ∘ Fin.natAdd (K + l) = j := by
      ext i
      have hi := congrFun (Fin.append_assoc u τ j) (Fin.natAdd (K + l) i)
      apply congrArg Fin.val
      simpa using hi.symm
    have hTailTrace :
        Matrix.trace
            (evalWord A (List.ofFn (Fin.append τ j)) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u) =
          Matrix.trace
            (evalWord A (List.ofFn τ) *
              (evalWord A (List.ofFn j) *
                boundaryFamilyEquiv (D := D) (Cfg d K) x u)) := by
      rw [List.ofFn_fin_append, evalWord_append]
      simp only [Matrix.mul_assoc]
    have hLeftTrace :
        Matrix.trace
            (evalWord A (List.ofFn (Fin.append u τ)) *
              boundaryFamilyEquiv (D := D) (Cfg d 1) y j) =
          Matrix.trace
            (evalWord A (List.ofFn τ) *
              (boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u))) := by
      rw [List.ofFn_fin_append, evalWord_append]
      symm
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle
        (evalWord A (List.ofFn τ))
        (boundaryFamilyEquiv (D := D) (Cfg d 1) y j)
        (evalWord A (List.ofFn u))
    simp only [tailBoundaryMapES_apply, WithLp.linearEquiv_symm_apply,
      AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      WithLp.addEquiv_symm_apply, cfgAppendThreeEquiv_apply,
      tailBoundaryMap_apply, List.ofFn_succ, evalWord_cons,
      boundaryFamilyEquiv_apply_apply,
      leftBoundaryMapES_apply, leftBoundaryMap_apply, RCLike.inner_apply,
      Fin.isValue, List.ofFn_zero, evalWord_nil, Matrix.mul_one,
      groundSpaceMap_apply, hTailPrefix, hTailSuffix, hLeftPrefix, hLeftSuffix]
    simp only [boundaryFamilyEquiv_apply_apply] at hTailTrace hLeftTrace
    rw [hLeftTrace]
    have hEvalAppend :
        A (Fin.append τ j 0) *
            evalWord A (List.ofFn fun i => Fin.append τ j i.succ) =
          evalWord A (List.ofFn (Fin.append τ j)) := by
      rw [List.ofFn_succ, evalWord_cons]
    rw [hEvalAppend, hTailTrace]
    simp only [List.ofFn_succ, List.ofFn_zero, evalWord_cons, evalWord_nil,
      Matrix.mul_one]

/-- Exact centering of the overlapping mixed Gram at the nonidentity limiting
Gram metric.

The limiting term acts by right multiplication: on the fiber indexed by
\((u,j)\), it sends \(Y_jA^u\) to
\((\operatorname{tr}\rho)^{-1}Y_jA^u\rho\). Hence subtracting this term leaves
exactly the same mixed pairing with the finite Gram operator minus its limiting
metric.

This identity is reconstructed algebraically from the mixed-Gram formula and
the limiting-metric computation. It is not attributed to FNW or Nachtergaele,
and it asserts no convergence or norm estimate. -/
theorem inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_centered
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ ≠ 0)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (y : BoundaryFamilySpace (D := D) (Cfg d 1)) :
    inner ℂ x ((tailBoundaryMapES A K (l + 1)).adjoint
        (leftBoundaryMapES A (K + l) 1 y)) -
      ∑ u : Cfg d K, ∑ j : Cfg d 1,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            ((Matrix.trace ρ)⁻¹ •
              ((boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u)) * ρ))) =
      ∑ u : Cfg d K, ∑ j : Cfg d 1,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          ((groundSpaceGram A l -
              Matrix.gramReshuffle (fixedPointProj ρ htr))
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
              (boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u)))) := by
  rw [inner_tailBoundaryMapES_adjoint_leftBoundaryMapES]
  simp_rw [sub_apply, inner_sub_right,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    Finset.sum_sub_distrib]

end MPSTensor
