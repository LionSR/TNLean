/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CenteredOverlapFactor

/-!
# Finite-Gram correction bounds in the C3 projector residual

This file factors the three finite-Gram correction sandwiches in the exact C3
projector-residual telescope.  The formulas are reconstructed from TNLean's
boundary-map and Gram identities.  They are not quoted from FNW,
Nachtergaele, or CPGSV21.

The orientation is always the tail projector after the left projector.  The
limiting Gram \(K_\infty\) is the nonidentity operator
\(\operatorname{gramReshuffle}(\operatorname{fixedPointProj}(\rho))\), and
positive definiteness of \(\rho\) is kept explicit.

## Main definitions

* `c3TailFiniteGramCorrectionES`
* `c3FullInverseGramCorrectionES`
* `c3LeftFiniteGramCorrectionES`

## Main results

* `inverseGram_sub_limitingInverse_eq_resolvent`
* `leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
* `c3TailFiniteGramCorrectionES_eq_factored`
* `c3FullInverseGramCorrectionES_eq_factored`
* `c3LeftFiniteGramCorrectionES_eq_factored`
* `c3TailFiniteGramCorrectionES_norm_le`
* `c3FullInverseGramCorrectionES_norm_le`
* `c3LeftFiniteGramCorrectionES_norm_le`
-/

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- Fiberwise lifting preserves subtraction. -/
theorem boundaryFiberwiseMap_sub (S : Type*) [Fintype S]
    (G H : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D)) :
    boundaryFiberwiseMap (D := D) S (G - H) =
      boundaryFiberwiseMap (D := D) S G - boundaryFiberwiseMap (D := D) S H := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  rfl

/-- Injectivity of the finite-volume ground-space map makes its Gram a unit. -/
theorem groundSpaceGram_isUnit_of_groundSpaceMapES_injective
    {A : MPSTensor d D} {n : ℕ}
    (h : Function.Injective (groundSpaceMapES A n)) :
    IsUnit (groundSpaceGram A n) := by
  have hinj : Function.Injective (groundSpaceGram A n) := by
    rw [groundSpaceGram]
    exact (groundSpaceMapES A n).adjoint_comp_self_injective_iff.mpr h
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

/-- The right-oriented finite/limiting resolvent identity.  This orientation
keeps the finite inverse next to the finite boundary-map adjoint. -/
theorem inverseGram_sub_limitingInverse_eq_resolvent [NeZero D]
    (A : MPSTensor d D) (n : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (h : Function.Injective (groundSpaceMapES A n)) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ifin := ContinuousLinearMap.inverseGram (groundSpaceMapES A n) h
    let Iinf := Ring.inverse Kinf
    Ifin - Iinf = Iinf.comp
      ((Kinf - groundSpaceGram A n).comp Ifin) := by
  dsimp only
  rw [ContinuousLinearMap.inverseGram_eq_ringInverse]
  simp only [groundSpaceGram]
  let Kfin := groundSpaceGram A n
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  change Ring.inverse Kfin - Ring.inverse Kinf =
    (Ring.inverse Kinf).comp ((Kinf - Kfin).comp (Ring.inverse Kfin))
  have hfin : IsUnit Kfin := by
    simpa only [Kfin] using groundSpaceGram_isUnit_of_groundSpaceMapES_injective h
  have hinf : IsUnit Kinf := by
    simpa only [Kinf] using Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hres : Ring.inverse Kinf - Ring.inverse Kfin =
      (Ring.inverse Kinf).comp ((Kfin - Kinf).comp (Ring.inverse Kfin)) := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      Ring.inverse_sub_inverse (a := Kinf) (b := Kfin) (by simp [hfin, hinf])
  calc
    Ring.inverse Kfin - Ring.inverse Kinf =
        -(Ring.inverse Kinf - Ring.inverse Kfin) := by abel
    _ = -((Ring.inverse Kinf).comp
        ((Kfin - Kinf).comp (Ring.inverse Kfin))) := by rw [hres]
    _ = (Ring.inverse Kinf).comp
        ((Kinf - Kfin).comp (Ring.inverse Kfin)) := by
      ext x
      simp

/-- The tail finite-Gram correction sandwich, before taking norms. -/
noncomputable def c3TailFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    EuclideanSpace ℂ (Cfg d (K + l + 1)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + l + 1)) :=
  let Ttail := tailBoundaryMapES A K (l + 1)
  let Tleft := leftBoundaryMapES A (K + l) 1
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (l + 1)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l)) hLocalLeft
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l + 1)) hFull
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K)
    (groundSpaceGram A (l + 1))
  let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Kleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
    (groundSpaceGram A (K + l))
  Ttail.comp ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
    ((Ktail - Kinftail).comp ((tailVirtualMapES A K).comp
      (Ifull.comp ((leftVirtualMapES A 1).adjoint.comp
        (Kleft.comp ((boundaryFiberwiseMap (D := D) (Cfg d 1) Ileft).comp
          Tleft.adjoint)))))))

/-- The full inverse-Gram correction sandwich, before taking norms. -/
noncomputable def c3FullInverseGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    EuclideanSpace ℂ (Cfg d (K + l + 1)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + l + 1)) :=
  let Ttail := tailBoundaryMapES A K (l + 1)
  let Tleft := leftBoundaryMapES A (K + l) 1
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (l + 1)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l)) hLocalLeft
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l + 1)) hFull
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Kleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
    (groundSpaceGram A (K + l))
  Ttail.comp ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
    (Kinftail.comp ((tailVirtualMapES A K).comp
      ((Ifull - Iinf).comp ((leftVirtualMapES A 1).adjoint.comp
        (Kleft.comp ((boundaryFiberwiseMap (D := D) (Cfg d 1) Ileft).comp
          Tleft.adjoint)))))))

/-- The left finite-Gram correction sandwich, before taking norms. -/
noncomputable def c3LeftFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l))) :
    EuclideanSpace ℂ (Cfg d (K + l + 1)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + l + 1)) :=
  let Ttail := tailBoundaryMapES A K (l + 1)
  let Tleft := leftBoundaryMapES A (K + l) 1
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (l + 1)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l)) hLocalLeft
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Kleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
    (groundSpaceGram A (K + l))
  let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
  Ttail.comp ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
    (Kinftail.comp ((tailVirtualMapES A K).comp
      (Iinf.comp ((leftVirtualMapES A 1).adjoint.comp
        ((Kleft - Kinfleft).comp
          ((boundaryFiberwiseMap (D := D) (Cfg d 1) Ileft).comp
            Tleft.adjoint)))))))

/-- The left fiberwise finite Gram cancels its inverse before the boundary
adjoint, and the remaining virtual/boundary composition reconstructs the
adjoint of the full ground-space map. -/
theorem leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A K)) :
    (leftVirtualMapES A L).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d L)
        (groundSpaceGram A K)).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d L)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A K) h)).comp
        (leftBoundaryMapES A K L).adjoint)) =
      (groundSpaceMapES A (K + L)).adjoint := by
  have hcancel : (boundaryFiberwiseMap (D := D) (Cfg d L)
      (groundSpaceGram A K)).comp
      (boundaryFiberwiseMap (D := D) (Cfg d L)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A K) h)) =
      ContinuousLinearMap.id ℂ _ := by
    rw [boundaryFiberwiseMap_comp, groundSpaceGram,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  change ((leftVirtualMapES A L).adjoint.comp
    ((boundaryFiberwiseMap (D := D) (Cfg d L)
      (groundSpaceGram A K)).comp
    (boundaryFiberwiseMap (D := D) (Cfg d L)
      (ContinuousLinearMap.inverseGram (groundSpaceMapES A K) h)))).comp
      (leftBoundaryMapES A K L).adjoint = _
  rw [hcancel, ContinuousLinearMap.comp_id,
    ← ContinuousLinearMap.adjoint_comp,
    leftBoundaryMapES_comp_leftVirtualMapES]

/-- Exact factorization of the tail finite-Gram correction.  Both exterior
pseudoinverse factors remain adjacent to their boundary maps. -/
theorem c3TailFiniteGramCorrectionES_eq_factored [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective
      A K (l + 1) hLocalTail
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    c3TailFiniteGramCorrectionES A K l ρ hρ hLocalTail hLocalLeft hFull =
      ((tailBoundaryMapES A K (l + 1)).comp
        (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1)) hTail)).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K)
        (groundSpaceGram A (l + 1) - Kinf)).comp
      ((tailVirtualMapES A K).comp
        (Ifull.comp (groundSpaceMapES A (K + l + 1)).adjoint))) := by
  dsimp only
  simp only [c3TailFiniteGramCorrectionES]
  rw [inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram
    A K (l + 1) hLocalTail]
  rw [boundaryFiberwiseMap_sub]
  rw [leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    A (K + l) 1 hLocalLeft]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Exact factorization of the full inverse-Gram correction using the
right-oriented resolvent identity. -/
theorem c3FullInverseGramCorrectionES_eq_factored [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective
      A K (l + 1) hLocalTail
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    c3FullInverseGramCorrectionES A K l ρ hρ hLocalTail hLocalLeft hFull =
      ((tailBoundaryMapES A K (l + 1)).comp
        (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1)) hTail)).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
      ((tailVirtualMapES A K).comp
      (Iinf.comp
      ((Kinf - groundSpaceGram A (K + l + 1)).comp
        (Ifull.comp (groundSpaceMapES A (K + l + 1)).adjoint))))) := by
  dsimp only
  simp only [c3FullInverseGramCorrectionES]
  rw [inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram
    A K (l + 1) hLocalTail]
  rw [inverseGram_sub_limitingInverse_eq_resolvent A (K + l + 1) ρ hρ hFull]
  rw [leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    A (K + l) 1 hLocalLeft]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Exact factorization of the left finite-Gram correction.  The inverse Gram
of the left spectator boundary map stays adjacent to its adjoint. -/
theorem c3LeftFiniteGramCorrectionES_eq_factored [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l))) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective
      A K (l + 1) hLocalTail
    let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
      A (K + l) 1 hLocalLeft
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    c3LeftFiniteGramCorrectionES A K l ρ hρ hLocalTail hLocalLeft =
      ((tailBoundaryMapES A K (l + 1)).comp
        (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1)) hTail)).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
      ((tailVirtualMapES A K).comp
      (Iinf.comp
      ((leftVirtualMapES A 1).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d 1)
        (groundSpaceGram A (K + l) - Kinf)).comp
      ((ContinuousLinearMap.inverseGram
        (leftBoundaryMapES A (K + l) 1) hLeft).comp
          (leftBoundaryMapES A (K + l) 1).adjoint)))))) := by
  dsimp only
  simp only [c3LeftFiniteGramCorrectionES]
  rw [inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram
    A K (l + 1) hLocalTail]
  rw [inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
    A (K + l) 1 hLocalLeft]
  rw [boundaryFiberwiseMap_sub]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The tail spectator pseudoinverse factor is controlled by the inverse
finite Gram, with no spectator-cardinality factor. -/
theorem norm_tailBoundaryMapES_comp_inverseGram_le_sqrt
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A L)) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K L h
    ‖(tailBoundaryMapES A K L).comp
      (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K L) hTail)‖ ≤
      Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A L) h‖ := by
  dsimp only
  rw [ContinuousLinearMap.norm_T_comp_inverseGram_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram A K L h]
  exact norm_boundaryFiberwiseMap_le _ _

/-- The adjoint-side left spectator pseudoinverse factor is controlled by the
inverse finite Gram, with no spectator-cardinality factor. -/
theorem norm_inverseGram_comp_leftBoundaryMapES_adjoint_le_sqrt
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A K)) :
    let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective A K L h
    ‖(ContinuousLinearMap.inverseGram (leftBoundaryMapES A K L) hLeft).comp
      (leftBoundaryMapES A K L).adjoint‖ ≤
      Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A K) h‖ := by
  dsimp only
  rw [ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram A K L h]
  exact norm_boundaryFiberwiseMap_le _ _

/-- Raw operator-norm bound for the tail finite-Gram correction. -/
theorem c3TailFiniteGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    ‖c3TailFiniteGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft hFull‖ ≤
      Real.sqrt ‖Itail‖ * ‖groundSpaceGram A (l + 1) - Kinf‖ *
        ‖tailVirtualMapES A K‖ * Real.sqrt ‖Ifull‖ := by
  dsimp only
  rw [c3TailFiniteGramCorrectionES_eq_factored A K l ρ hρ
    hLocalTail hLocalLeft hFull]
  let Ptail := (tailBoundaryMapES A K (l + 1)).comp
    (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1))
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
        A K (l + 1) hLocalTail))
  let E := boundaryFiberwiseMap (D := D) (Cfg d K)
    (groundSpaceGram A (l + 1) - Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
  let J := tailVirtualMapES A K
  let Pfull := (ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l + 1)) hFull).comp
      (groundSpaceMapES A (K + l + 1)).adjoint
  change ‖Ptail.comp (E.comp (J.comp Pfull))‖ ≤ _
  calc
    ‖Ptail.comp (E.comp (J.comp Pfull))‖ ≤
        ‖Ptail‖ * ‖E.comp (J.comp Pfull)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖E‖ * ‖J.comp Pfull‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖E‖ * (‖J‖ * ‖Pfull‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖E‖ * ‖J‖ * ‖Pfull‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ *
        ‖groundSpaceGram A (l + 1) - Matrix.gramReshuffle
          (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ *
        ‖tailVirtualMapES A K‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l + 1)) hFull‖ := by
      dsimp only [Ptail, E, J, Pfull]
      rw [ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt]
      gcongr
      · exact norm_tailBoundaryMapES_comp_inverseGram_le_sqrt
          A K (l + 1) hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
    _ = _ := by ring

/-- Raw operator-norm bound for the full inverse-Gram correction. -/
theorem c3FullInverseGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull
    ‖c3FullInverseGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft hFull‖ ≤
      Real.sqrt ‖Itail‖ * ‖Kinf‖ * ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
        ‖groundSpaceGram A (K + l + 1) - Kinf‖ * Real.sqrt ‖Ifull‖ := by
  dsimp only
  rw [c3FullInverseGramCorrectionES_eq_factored A K l ρ hρ
    hLocalTail hLocalLeft hFull]
  let Ptail := (tailBoundaryMapES A K (l + 1)).comp
    (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1))
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
        A K (l + 1) hLocalTail))
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let J := tailVirtualMapES A K
  let Iinf := Ring.inverse Kinf
  let Efull := Kinf - groundSpaceGram A (K + l + 1)
  let Pfull := (ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l + 1)) hFull).comp
      (groundSpaceMapES A (K + l + 1)).adjoint
  change ‖Ptail.comp (Ktail.comp (J.comp (Iinf.comp
    (Efull.comp Pfull))))‖ ≤ _
  calc
    _ ≤ ‖Ptail‖ * ‖Ktail.comp (J.comp (Iinf.comp
          (Efull.comp Pfull)))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * ‖J.comp (Iinf.comp
          (Efull.comp Pfull))‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * ‖Iinf.comp
          (Efull.comp Pfull)‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * (‖Iinf‖ *
          ‖Efull.comp Pfull‖))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * (‖Iinf‖ *
          (‖Efull‖ * ‖Pfull‖)))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖Ktail‖ * ‖J‖ * ‖Iinf‖ * ‖Efull‖ * ‖Pfull‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ * ‖Kinf‖ *
        ‖tailVirtualMapES A K‖ * ‖Ring.inverse Kinf‖ *
        ‖groundSpaceGram A (K + l + 1) - Kinf‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l + 1)) hFull‖ := by
      dsimp only [Ptail, Ktail, J, Iinf, Efull, Pfull]
      -- Reverse the Gram difference only inside its norm to match the stated error.
      rw [norm_sub_rev, ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt]
      gcongr
      · exact norm_tailBoundaryMapES_comp_inverseGram_le_sqrt
          A K (l + 1) hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
    _ = _ := by ring

/-- Raw operator-norm bound for the left finite-Gram correction. -/
theorem c3LeftFiniteGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail
    let Ileft := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l)) hLocalLeft
    ‖c3LeftFiniteGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft‖ ≤
      Real.sqrt ‖Itail‖ * ‖Kinf‖ * ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
        ‖leftVirtualMapES A 1‖ * ‖groundSpaceGram A (K + l) - Kinf‖ *
          Real.sqrt ‖Ileft‖ := by
  dsimp only
  rw [c3LeftFiniteGramCorrectionES_eq_factored A K l ρ hρ
    hLocalTail hLocalLeft]
  let Ptail := (tailBoundaryMapES A K (l + 1)).comp
    (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1))
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
        A K (l + 1) hLocalTail))
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Jtail := tailVirtualMapES A K
  let Iinf := Ring.inverse Kinf
  let JleftAdj := (leftVirtualMapES A 1).adjoint
  let Eleft := boundaryFiberwiseMap (D := D) (Cfg d 1)
    (groundSpaceGram A (K + l) - Kinf)
  let Pleft := (ContinuousLinearMap.inverseGram
    (leftBoundaryMapES A (K + l) 1)
      (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
        A (K + l) 1 hLocalLeft)).comp
          (leftBoundaryMapES A (K + l) 1).adjoint
  change ‖Ptail.comp (Ktail.comp (Jtail.comp (Iinf.comp
    (JleftAdj.comp (Eleft.comp Pleft)))))‖ ≤ _
  calc
    _ ≤ ‖Ptail‖ * ‖Ktail.comp (Jtail.comp (Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft))))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * ‖Jtail.comp (Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft)))‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * ‖Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft))‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          ‖JleftAdj.comp (Eleft.comp Pleft)‖))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          (‖JleftAdj‖ * ‖Eleft.comp Pleft‖)))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          (‖JleftAdj‖ * (‖Eleft‖ * ‖Pleft‖))))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖Ktail‖ * ‖Jtail‖ * ‖Iinf‖ * ‖JleftAdj‖ *
        ‖Eleft‖ * ‖Pleft‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ * ‖Kinf‖ *
        ‖tailVirtualMapES A K‖ * ‖Ring.inverse Kinf‖ *
        ‖leftVirtualMapES A 1‖ * ‖groundSpaceGram A (K + l) - Kinf‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l)) hLocalLeft‖ := by
      dsimp only [Ptail, Ktail, Jtail, Iinf, JleftAdj, Eleft, Pleft]
      rw [LinearIsometryEquiv.norm_map
        (ContinuousLinearMap.adjoint (𝕜 := ℂ))]
      gcongr
      · exact norm_tailBoundaryMapES_comp_inverseGram_le_sqrt
          A K (l + 1) hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
      · exact norm_boundaryFiberwiseMap_le _ _
      · exact norm_inverseGram_comp_leftBoundaryMapES_adjoint_le_sqrt
          A (K + l) 1 hLocalLeft
    _ = _ := by ring



/-- The overlap-factor limiting product agrees with the virtual-word limiting
product for an arbitrary suffix increment. -/
theorem wholeIncrement_limitingOverlapProduct_eq [NeZero D]
    (A : MPSTensor d D) (K Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    (wholeIncrementLeftOverlapFactorES A K Q).adjoint.comp
        ((boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d Q) Kinf).comp
          (wholeIncrementRightOverlapFactorES A K Q)) =
      (boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
        ((tailVirtualMapES A K).comp
          ((Ring.inverse Kinf).comp
            ((leftVirtualMapES A Q).adjoint.comp
              (boundaryFiberwiseMap (D := D) (Cfg d Q) Kinf)))) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [inner_boundaryFiberwiseMap]
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  rw [Fintype.sum_prod_type]
  change (∑ u : Cfg d K, ∑ j : Cfg d Q,
      inner ℂ
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d Q)
            (wholeIncrementLeftOverlapFactorES A K Q x) (u, j)))
        ((Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d Q)
              (wholeIncrementRightOverlapFactorES A K Q y) (u, j))))) = _
  simp_rw [boundaryFamilyEquiv_wholeIncrementLeftOverlapFactorES_apply,
    boundaryFamilyEquiv_wholeIncrementRightOverlapFactorES_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply]
  rw [leftVirtualMapES_adjoint_apply]
  simp_rw [boundaryFamilyEquiv_boundaryFiberwiseMap_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
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
    Matrix.trace_sum, Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ### Whole-increment finite-Gram corrections -/

/-- Reassociation does not change the tail boundary Gram. -/
theorem reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram
    (A : MPSTensor d D) (K L Q : ℕ) :
    (reassocTailBoundaryMapES A K L Q).adjoint.comp
        (reassocTailBoundaryMapES A K L Q) =
      boundaryFiberwiseMap (D := D) (Cfg d K) (groundSpaceGram A (L + Q)) := by
  have hreassoc :
      (physicalReassocES (d := d) K L Q).toContinuousLinearMap.adjoint.comp
        (physicalReassocES (d := d) K L Q).toContinuousLinearMap = 1 :=
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K L Q).symm)
          (Equiv.refl (Fin d)))).isometry
  rw [reassocTailBoundaryMapES, ContinuousLinearMap.adjoint_comp]
  have hcomp := congrArg (fun X =>
      (tailBoundaryMapES A K (L + Q)).adjoint.comp
        (X.comp (tailBoundaryMapES A K (L + Q)))) hreassoc
  simp only [ContinuousLinearMap.comp_assoc] at hcomp
  rw [ContinuousLinearMap.comp_assoc, hcomp]
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram A K (L + Q)

/-- The inverse Gram of the reassociated tail map remains fiberwise. -/
theorem inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
        ((physicalReassocES (d := d) K L Q).injective.comp
          (tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K (L + Q) h)) =
      boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h) := by
  rw [ContinuousLinearMap.inverseGram_eq_inverse]
  apply ContinuousLinearMap.inverse_eq
  · rw [reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  · rw [reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.inverseGram_comp_adjoint_comp_self,
      boundaryFiberwiseMap_id]

/-- The left finite Gram cancels its inverse for an arbitrary suffix increment. -/
theorem wholeIncrementLeftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (K + L))) :
    (leftVirtualMapES A Q).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d Q)
        (groundSpaceGram A (K + L))).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d Q)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (K + L)) h)).comp
        (leftBoundaryMapES A (K + L) Q).adjoint)) =
      (groundSpaceMapES A (K + L + Q)).adjoint := by
  simpa only using leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    A (K + L) Q h

/-- The reassociated tail finite Gram cancels its inverse. -/
theorem wholeIncrementTailFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    (tailVirtualMapES A K).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K)
        (groundSpaceGram A (L + Q))).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)).comp
        (reassocTailBoundaryMapES A K L Q).adjoint)) =
      (groundSpaceMapES A (K + L + Q)).adjoint := by
  have hcancel : (boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)) =
      ContinuousLinearMap.id ℂ _ := by
    rw [boundaryFiberwiseMap_comp, groundSpaceGram,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  change ((tailVirtualMapES A K).adjoint.comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))).comp
    (boundaryFiberwiseMap (D := D) (Cfg d K)
      (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)))).comp
      (reassocTailBoundaryMapES A K L Q).adjoint = _
  rw [hcancel, ContinuousLinearMap.comp_id, ← ContinuousLinearMap.adjoint_comp,
    reassocTailBoundaryMapES_comp_tailVirtualMapES]

/-- Tail finite-Gram correction for a suffix increment of length `Q`. -/
noncomputable def wholeIncrementTailFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q) - Kinf)).comp
    ((tailVirtualMapES A K).comp
      (Ifull.comp (groundSpaceMapES A (K + L + Q)).adjoint)))

/-- Full inverse-Gram correction for a suffix increment of length `Q`. -/
noncomputable def wholeIncrementFullInverseGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
    ((tailVirtualMapES A K).comp
    ((Ifull - Iinf).comp (groundSpaceMapES A (K + L + Q)).adjoint)))

/-- Left finite-Gram correction for a suffix increment of length `Q`. -/
noncomputable def wholeIncrementLeftFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
    A (K + L) Q hLocalLeft
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
    ((tailVirtualMapES A K).comp
    (Iinf.comp
    ((leftVirtualMapES A Q).adjoint.comp
    ((boundaryFiberwiseMap (D := D) (Cfg d Q)
      (groundSpaceGram A (K + L) - Kinf)).comp
    ((ContinuousLinearMap.inverseGram
      (leftBoundaryMapES A (K + L) Q) hLeft).comp
        (leftBoundaryMapES A (K + L) Q).adjoint))))))

/-- The reassociated tail pseudoinverse has the same square-root bound as the
unreassociated tail map. -/
theorem norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    let hTail := (physicalReassocES (d := d) K L Q).injective.comp
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K (L + Q) h)
    ‖(reassocTailBoundaryMapES A K L Q).comp
      (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q) hTail)‖ ≤
      Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h‖ := by
  dsimp only
  rw [ContinuousLinearMap.norm_T_comp_inverseGram_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram A K L Q h]
  exact norm_boundaryFiberwiseMap_le _ _



/-- Exact whole-increment virtual telescope around the limiting Gram metric. -/
theorem wholeIncrement_virtualResidual_eq_centered_sub_gramErrors [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kleft := boundaryFiberwiseMap (D := D) (Cfg d Q)
      (groundSpaceGram A (K + L))
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d Q) Kinf
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L + Q)) hFull
    let Iinf := Ring.inverse Kinf
    let Jtail := tailVirtualMapES A K
    let JleftAdj := (leftVirtualMapES A Q).adjoint
    (reassocTailBoundaryMapES A K L Q).adjoint.comp
          (leftBoundaryMapES A (K + L) Q) -
        Ktail.comp (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) =
      wholeIncrementCenteredResidualES A K L Q ρ (ne_of_gt hρ.trace_pos) -
      (Ktail - Kinftail).comp
        (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp ((Ifull - Iinf).comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp (Iinf.comp (JleftAdj.comp (Kleft - Kinfleft)))) := by
  dsimp only
  rw [wholeIncrementCenteredResidualES,
    wholeIncrement_limitingOverlapProduct_eq A K Q ρ hρ]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

/-- The physical sandwich containing the centered residual for a suffix increment
of length `Q`. -/
noncomputable def wholeIncrementCenteredProjectorResidualES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (L + Q)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L)) hLocalLeft
  (reassocTailBoundaryMapES A K L Q).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
      ((wholeIncrementCenteredResidualES A K L Q ρ
        (ne_of_gt hρ.trace_pos)).comp
        ((boundaryFiberwiseMap (D := D) (Cfg d Q) Ileft).comp
          (leftBoundaryMapES A (K + L) Q).adjoint)))



end MPSTensor
