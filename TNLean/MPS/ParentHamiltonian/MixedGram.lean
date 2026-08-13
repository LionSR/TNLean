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
maps in the common ambient spaces used by Nachtergaele's martingale conditions
C3 and C3'. The calculation is exact: after fixing the prefix spectator \(u\)
and the arbitrary-increment spectator \(j\), the overlap is the length-\(l\) MPS
Gram pairing of the two virtual matrices obtained at the ends of the overlap.

The identities below are reconstructed directly from the boundary-map definitions,
word factorization, and trace cyclicity. They are not stated in this form by FNW
or Nachtergaele. The sourced targets are the projector defects in Nachtergaele,
arXiv:cond-mat/9410110, equations (2.4)--(2.5); the rational numerical estimate is
quoted after equation (2.4) and in Section 6, equation (6.1). No numerical estimate
is asserted here.

## Main results

* `inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_q`
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

/-- Exact arbitrary-increment mixed-Gram identity for the overlapping windows in
Nachtergaele's C3' geometry (arXiv:cond-mat/9410110, equation (2.5)).

For a prefix spectator \(u\) and a \(q\)-site increment spectator \(j\), the tail
boundary matrix entering the \(l\)-site overlap is \(A^j X_u\), while the left
boundary matrix is \(Z_j A^u\). Thus the mixed Gram is a sum of length-\(l\)
ground-space Gram pairings with exactly this multiplication order. The canonical
reindexing only identifies \(K+(l+q)\) with \((K+l)+q\).

This is an algebraic identity reconstructed from the definitions. It is not the
analytic C3' norm estimate in equation (2.5), and it asserts no contraction or
uniformity in the increment. -/
theorem inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_q
    (A : MPSTensor d D) (K l q : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (y : BoundaryFamilySpace (D := D) (Cfg d q)) :
    inner ℂ x ((tailBoundaryMapES A K (l + q)).adjoint
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K l q)) (Equiv.refl (Fin d))))
        (leftBoundaryMapES A (K + l) q y))) =
      ∑ u : Cfg d K, ∑ j : Cfg d q,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          (groundSpaceGram A l
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
              (boundaryFamilyEquiv (D := D) (Cfg d q) y j *
                evalWord A (List.ofFn u)))) := by
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  trans ∑ p : Cfg d K × (Cfg d l × Cfg d q),
      inner ℂ
        ((tailBoundaryMapES A K (l + q) x) (cfgAppendThreeEquiv d K l q p))
        ((leftBoundaryMapES A (K + l) q y)
          ((Equiv.arrowCongr (finCongr (Nat.add_assoc K l q))
            (Equiv.refl (Fin d))).symm (cfgAppendThreeEquiv d K l q p)))
  · symm
    apply Fintype.sum_equiv (cfgAppendThreeEquiv d K l q)
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
        Fin.append u (Fin.append τ j) ∘ Fin.castAdd (l + q) = u := by
      ext i
      simp [Fin.append_left]
    have hTailSuffix :
        Fin.append u (Fin.append τ j) ∘ Fin.natAdd K = Fin.append τ j := by
      ext i
      simp [Fin.append_right]
    have hAssoc :
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K l q))
          (Equiv.refl (Fin d))).symm (Fin.append u (Fin.append τ j)) =
            Fin.append (Fin.append u τ) j := by
      rw [Equiv.arrowCongr_symm]
      ext i
      rw [Equiv.arrowCongr_apply]
      simp only [Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply,
        finCongr_symm, finCongr_apply]
      apply congrArg Fin.val
      exact congrFun (Fin.append_assoc u τ j).symm i
    have hLeftPrefix :
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K l q))
            (Equiv.refl (Fin d))).symm (Fin.append u (Fin.append τ j)) ∘
              Fin.castAdd q = Fin.append u τ := by
      rw [hAssoc]
      ext i
      simp [Fin.append_left]
    have hLeftSuffix :
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K l q))
            (Equiv.refl (Fin d))).symm (Fin.append u (Fin.append τ j)) ∘
              Fin.natAdd (K + l) = j := by
      rw [hAssoc]
      ext i
      simp [Fin.append_right]
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
              boundaryFamilyEquiv (D := D) (Cfg d q) y j) =
          Matrix.trace
            (evalWord A (List.ofFn τ) *
              (boundaryFamilyEquiv (D := D) (Cfg d q) y j *
                evalWord A (List.ofFn u))) := by
      rw [List.ofFn_fin_append, evalWord_append]
      symm
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle
        (evalWord A (List.ofFn τ))
        (boundaryFamilyEquiv (D := D) (Cfg d q) y j)
        (evalWord A (List.ofFn u))
    simp only [tailBoundaryMapES_apply, WithLp.linearEquiv_symm_apply,
      AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      WithLp.addEquiv_symm_apply, cfgAppendThreeEquiv_apply,
      tailBoundaryMap_apply, boundaryFamilyEquiv_apply_apply,
      leftBoundaryMapES_apply, leftBoundaryMap_apply, RCLike.inner_apply,
      groundSpaceMap_apply, hTailPrefix, hTailSuffix, hLeftPrefix, hLeftSuffix]
    simp only [boundaryFamilyEquiv_apply_apply] at hTailTrace hLeftTrace
    rw [hLeftTrace]
    rw [hTailTrace]

-- A formulation that first reassociates the tail map into the left-associated
-- ambient space should derive from this theorem by adjoint composition with the
-- same unitary coordinate reassociation, rather than repeat the coordinate proof.

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
  convert inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_q A K l 1 x y using 1
  apply congrArg (fun z => inner ℂ x ((tailBoundaryMapES A K (l + 1)).adjoint z))
  apply PiLp.ext
  intro σ
  rfl

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
