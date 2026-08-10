/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GramInverseConvergence
import TNLean.MPS.ParentHamiltonian.MixedGram

/-!
# Cancellation in the overlapping-window projector residual

This file isolates the finite-volume Gram errors in the virtual residual that
appears in the exact C3 projector factorization.  The center is the nonidentity
limiting Gram metric
\[
  K_\infty=\operatorname{gramReshuffle}(\operatorname{fixedPointProj}(\rho)).
\]
No physical projector is identified with the transfer fixed-point projection.

The decomposition is reconstructed algebraically from the exact projector
factorization.  It is not the FNW numerical estimate quoted by Nachtergaele,
arXiv:cond-mat/9410110, after equation (2.4) and in equation (6.1).

## Main results

* `c3_virtualResidual_eq_centered_sub_gramErrors`
* `inner_limitingMixedGramIntertwining`
* `inner_c3_centeredVirtualResidual_eq_gramError`
* `c3_injectiveRangeProjector_residual_eq_centered_sub_gramErrors`
-/

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- The virtual residual inside the exact C3 projector factorization, expanded
around the limiting Gram metric.  The three correction terms isolate,
respectively, the errors at lengths \(l+1\), \(K+l+1\) after inversion, and
\(K+l\).  The leading centered mixed Gram is the remaining length-\(l\) error
characterized by
`inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_centered` once its explicit
limiting pairing is identified with the displayed limiting product.

This is an exact telescoping identity.  Positive definiteness is used only to
supply the invertible center \(K_\infty\); no rational contraction coefficient
is asserted. -/
theorem c3_virtualResidual_eq_centered_sub_gramErrors [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (l + 1))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
      (groundSpaceGram A (K + l))
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    let Iinf := Ring.inverse Kinf
    let Jtail := tailVirtualMapES A K
    let JleftAdj := (leftVirtualMapES A 1).adjoint
    (tailBoundaryMapES A K (l + 1)).adjoint.comp
          (leftBoundaryMapES A (K + l) 1) -
        Ktail.comp (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) =
      ((tailBoundaryMapES A K (l + 1)).adjoint.comp
          (leftBoundaryMapES A (K + l) 1) -
        Kinftail.comp (Jtail.comp (Iinf.comp (JleftAdj.comp Kinfleft)))) -
      (Ktail - Kinftail).comp
        (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp ((Ifull - Iinf).comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp (Iinf.comp (JleftAdj.comp (Kleft - Kinfleft)))) := by
  dsimp only
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

/-- Exact limiting mixed-Gram intertwining in the tail-after-left C3
orientation.  The limiting Gram acts by normalized right multiplication by
\(ρ\); its inverse cancels that right multiplication after the adjoint of the
left virtual word map has summed the left-adjointed one-site words.

No transfer fixed-point equation is needed for this zeroth-order identity: the
only data used are positive definiteness, which supplies the nonsingular
right-multiplication metric, and the explicit Frobenius adjoint formulas. -/
theorem inner_limitingMixedGramIntertwining [NeZero D]
    (A : MPSTensor d D) (K : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (y : BoundaryFamilySpace (D := D) (Cfg d 1)) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
    let Iinf := Ring.inverse Kinf
    inner ℂ x
        (Kinftail.comp ((tailVirtualMapES A K).comp
          (Iinf.comp ((leftVirtualMapES A 1).adjoint.comp Kinfleft))) y) =
      ∑ u : Cfg d K, ∑ j : Cfg d 1,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            ((Matrix.trace ρ)⁻¹ •
              ((boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u)) * ρ))) := by
  dsimp only
  simp only [ContinuousLinearMap.comp_apply]
  have hKfiber (j : Cfg d 1) :
      boundaryFamilyEquiv (D := D) (Cfg d 1)
          (boundaryFiberwiseMap (D := D) (Cfg d 1)
            (Matrix.gramReshuffle
              (fixedPointProj ρ (ne_of_gt hρ.trace_pos))) y) j =
        (Matrix.trace ρ)⁻¹ •
          (boundaryFamilyEquiv (D := D) (Cfg d 1) y j * ρ) := by
    rw [boundaryFamilyEquiv_boundaryFiberwiseMap_apply,
      Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  rw [leftVirtualMapES_adjoint_apply]
  have hsum :
      (∑ j : Cfg d 1, (evalWord A (List.ofFn j))ᴴ *
        boundaryFamilyEquiv (D := D) (Cfg d 1)
          (boundaryFiberwiseMap (D := D) (Cfg d 1)
            (Matrix.gramReshuffle
              (fixedPointProj ρ (ne_of_gt hρ.trace_pos))) y) j) =
        ∑ j : Cfg d 1, (evalWord A (List.ofFn j))ᴴ *
          ((Matrix.trace ρ)⁻¹ •
            (boundaryFamilyEquiv (D := D) (Cfg d 1) y j * ρ)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hKfiber j]
  rw [hsum]
  rw [Matrix.inverse_gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply
    (hρ := hρ)]
  simp only [Finset.sum_mul, Finset.smul_sum, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hρ.trace_pos),
    Matrix.mul_assoc,
    Matrix.mul_nonsing_inv ρ (ρ.isUnit_iff_isUnit_det.mp hρ.isUnit),
    Matrix.mul_one, one_smul]
  rw [inner_boundaryFiberwiseMap]
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  simp_rw [Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply]
  simp_rw [boundaryFamilyEquiv_tailVirtualMapES_apply]
  simp only [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_smul, Finset.smul_sum,
    Matrix.trace_sum,
    Matrix.inner_frobeniusEquivEuclidean, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- Reduction of the leading centered operator to the length-\(l\) Gram
error.  The limiting product is identified by
`inner_limitingMixedGramIntertwining`; subtracting it from the exact mixed Gram
therefore leaves precisely the finite length-\(l\) Gram error. -/
theorem inner_c3_centeredVirtualResidual_eq_gramError [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (y : BoundaryFamilySpace (D := D) (Cfg d 1)) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
    let Iinf := Ring.inverse Kinf
    inner ℂ x
        (((tailBoundaryMapES A K (l + 1)).adjoint.comp
            (leftBoundaryMapES A (K + l) 1) -
          Kinftail.comp ((tailVirtualMapES A K).comp
            (Iinf.comp ((leftVirtualMapES A 1).adjoint.comp Kinfleft)))) y) =
      ∑ u : Cfg d K, ∑ j : Cfg d 1,
        inner ℂ
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (evalWord A (List.ofFn j) *
              boundaryFamilyEquiv (D := D) (Cfg d K) x u))
          ((groundSpaceGram A l - Kinf)
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
              (boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
                evalWord A (List.ofFn u)))) := by
  dsimp only
  rw [sub_apply, inner_sub_right,
    inner_limitingMixedGramIntertwining A K ρ hρ x y]
  exact inner_tailBoundaryMapES_adjoint_leftBoundaryMapES_centered
    A K l ρ (ne_of_gt hρ.trace_pos) x y

/-- The exact C3 projector defect with the virtual residual replaced by the
centered telescoping decomposition above.  The tail inverse Gram is the
fiberwise inverse at length \(l+1\), the left inverse Gram is the fiberwise
inverse at length \(K+l\), and the full inverse Gram occurs only through its
difference from \(K_\infty^{-1}\).

The order is the C3 tail projector after the left projector.  This statement is
purely algebraic and asserts no uniform norm bound. -/
theorem c3_injectiveRangeProjector_residual_eq_centered_sub_gramErrors [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective
      A K (l + 1) hLocalTail
    let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
      A (K + l) 1 hLocalLeft
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (l + 1))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
      (groundSpaceGram A (K + l))
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
    let IlocalTail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail
    let IlocalLeft := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l)) hLocalLeft
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    let Iinf := Ring.inverse Kinf
    let Jtail := tailVirtualMapES A K
    let JleftAdj := (leftVirtualMapES A 1).adjoint
    let centeredErrors :=
      ((tailBoundaryMapES A K (l + 1)).adjoint.comp
          (leftBoundaryMapES A (K + l) 1) -
        Kinftail.comp (Jtail.comp (Iinf.comp (JleftAdj.comp Kinfleft)))) -
      (Ktail - Kinftail).comp
        (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp ((Ifull - Iinf).comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp (Iinf.comp (JleftAdj.comp (Kleft - Kinfleft))))
    (ContinuousLinearMap.injectiveRangeProjector
        (tailBoundaryMapES A K (l + 1)) hTail).comp
        (ContinuousLinearMap.injectiveRangeProjector
          (leftBoundaryMapES A (K + l) 1) hLeft) -
      ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES A (K + l + 1)) hFull =
      (tailBoundaryMapES A K (l + 1)).comp
        ((boundaryFiberwiseMap (D := D) (Cfg d K) IlocalTail).comp
          (centeredErrors.comp
            ((boundaryFiberwiseMap (D := D) (Cfg d 1) IlocalLeft).comp
              (leftBoundaryMapES A (K + l) 1).adjoint))) := by
  dsimp only
  rw [c3_injectiveRangeProjector_residual_eq]
  rw [inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram,
    inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram,
    tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
    leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
    c3_virtualResidual_eq_centered_sub_gramErrors A K l ρ hρ hFull]

end MPSTensor
