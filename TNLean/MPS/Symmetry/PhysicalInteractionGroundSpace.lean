/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalInteractionGap

/-!
# Ground spaces under isometric physical inclusions

A physical inclusion transports the ground space of a commuting projection
parent Hamiltonian into the enlarged chain. The added local energy on unused
states prevents additional zero modes. The proof uses the product of local
ground projections and its support on the included physical space.

Source context: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Sections II.D.2
and II.F.2, equation eq:1d-sym:jointsym. The finite support calculation also
appears in arXiv:1606.00608, Appendix C.2, equations PjKiPj and generateMPDO,
lines 1733–1770.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

/-- The range of an isometrically conjugated matrix is the isometric
image of its original range. -/
theorem range_toEuclideanLin_singleKrausMap_of_isometry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1) (M : Matrix ι ι ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (singleKrausMap V M)) =
      (LinearMap.range (Matrix.toEuclideanLin M)).map (Matrix.toEuclideanLin V) := by
  have hSurj : Function.Surjective (Matrix.toEuclideanLin Vᴴ) := fun x =>
    ⟨Matrix.toEuclideanLin V x, by
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg (fun A => Matrix.toEuclideanLin A x) hV⟩
  simpa only [singleKrausMap_apply, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
    (LinearMap.range_comp_of_range_eq_top
      (Matrix.toEuclideanLin V ∘ₗ Matrix.toEuclideanLin M)
      (LinearMap.range_eq_top.mpr hSurj)).trans (LinearMap.range_comp _ _)

end Matrix

namespace MPSTensor

/-- For commuting local parent projections, the product of their
complements has range equal to the periodic ground space.
Source context: arXiv:1010.3732, Section II.D.2, the independent-bond
parent Hamiltonian. -/
theorem interactionHamiltonian_ker_eq_range_groundProduct {d N : ℕ}
    (A : MPOTensor.ChainOperator d 2) (hA : IsStarProjection A)
    (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A)) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) =
      LinearMap.range (Matrix.toEuclideanLin
        (List.ofFn fun i : Fin N => 1 - MPOTensor.embedLocalOperator 2 N hN i A).prod) := by
  let P (i : Fin N) := (bondMatrixEquiv d N).symm
    (MPOTensor.embedLocalOperator 2 N hN i A)
  have hP (i : Fin N) : (P i).IsSymmetricProjection :=
    bondMatrixEquiv_symm_isSymmetricProjection _
      (MPOTensor.embedLocalOperator_isStarProjection 2 N hN i hA)
  have hPC (i j : Fin N) : Commute (P i) (P j) :=
    (hcomm i j).map (bondMatrixEquiv d N).symm
  have h := (LinearMap.range_listProd_one_sub_eq_ker_sum P hP hPC).symm
  have hProd : (bondMatrixEquiv d N).symm
      (List.ofFn fun i : Fin N => 1 - MPOTensor.embedLocalOperator 2 N hN i A).prod =
      (List.ofFn fun i : Fin N => 1 - P i).prod := by
    simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_sub, map_one, P]
  rw [← hProd] at h
  simpa only [P, ← map_sum, bondMatrixEquiv_symm_eq_toEuclideanLin,
    interactionHamiltonian] using h

/-- Extending a local parent projection through a physical isometry and
penalizing unused physical states again gives an orthogonal projection.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem isometricInteractionExtension_isStarProjection {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : IsStarProjection A) :
    IsStarProjection (isometricInteractionExtension E A) := by
  apply IsStarProjection.one_sub
  refine ⟨?_, (Matrix.isHermitian_mul_mul_conjTranspose
    (MPOTensor.sitewisePhysicalMatrix E 2)
    hA.one_sub.isSelfAdjoint.isHermitian).isSelfAdjoint⟩
  exact (Matrix.singleKrausMap_mul_of_isometry
    (MPOTensor.sitewisePhysicalMatrix E 2)
    (MPOTensor.sitewisePhysicalMatrix_isometry E hE 2) (1 - A) (1 - A)).symm.trans
      (congrArg (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2))
        hA.one_sub.isIdempotentElem.eq)

/-- The product of local ground projections of an isometric extension is
the isometric image of the original product, whenever the enlarged local
terms commute. Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem isometricInteractionExtension_groundProduct {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : A.IsHermitian) (hN : 2 ≤ N)
    (hcomm : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A))
        (MPOTensor.embedLocalOperator 2 N hN j (isometricInteractionExtension E A))) :
    (List.ofFn fun i : Fin N =>
      1 - MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A)).prod =
      singleKrausMap (MPOTensor.sitewisePhysicalMatrix E N)
        (List.ofFn fun i : Fin N => 1 - MPOTensor.embedLocalOperator 2 N hN i A).prod := by
  have hLift (i : Fin N) :
      MPOTensor.embedLocalOperator 2 N hN i
          (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)) =
        1 - MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A) := by
    change (MPOTensor.embedLocalOperatorAlgHom (d := m) 2 N hN i)
        (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)) =
      1 - (MPOTensor.embedLocalOperatorAlgHom (d := m) 2 N hN i)
        (1 - singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A))
    simp only [map_sub, map_one, sub_sub_cancel]
  have hLiftComm (i j : Fin N) :
      Commute (MPOTensor.embedLocalOperator 2 N hN i
          (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A)))
        (MPOTensor.embedLocalOperator 2 N hN j
          (singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - A))) := by
    rw [hLift i, hLift j]
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hcomm i j))
  have hOld (i : Fin N) : MPOTensor.embedLocalOperator 2 N hN i (1 - A) =
      1 - MPOTensor.embedLocalOperator 2 N hN i A := by
    change (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i) (1 - A) =
      1 - (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i) A
    simp only [map_sub, map_one]
  have hImage := MPOTensor.singleKrausMap_bondProduct_of_isometry E hE (1 - A)
    (Matrix.isHermitian_one.sub hA) hN hLiftComm
  simpa only [hLift, hOld] using hImage.symm

/-- The ground space of an isometrically extended commuting projection
Hamiltonian is exactly the isometric image of the original ground space.
In particular, unused physical states introduce no additional zero modes.
Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem isometricInteractionExtension_ker_eq_map {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcommOld : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A))
    (hcommNew : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A))
        (MPOTensor.embedLocalOperator 2 N hN j (isometricInteractionExtension E A))) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) =
      (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN))).map
        (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)) := by
  rw [interactionHamiltonian_ker_eq_range_groundProduct _
    (isometricInteractionExtension_isStarProjection E hE A hA) hN hcommNew]
  rw [isometricInteractionExtension_groundProduct E hE A
    hA.isSelfAdjoint.isHermitian hN hcommNew]
  rw [Matrix.range_toEuclideanLin_singleKrausMap_of_isometry _
    (MPOTensor.sitewisePhysicalMatrix_isometry E hE N)]
  rw [interactionHamiltonian_ker_eq_range_groundProduct A hA hN hcommOld]

/-- A ground space generated by a single vector extends to the span of
its physical image. Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem isometricInteractionExtension_ker_eq_span {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPOTensor.ChainOperator d 2) (hA : IsStarProjection A) (hN : 2 ≤ N)
    (hcommOld : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A))
    (hcommNew : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A))
        (MPOTensor.embedLocalOperator 2 N hN j (isometricInteractionExtension E A)))
    (ψ : EuclideanSpace ℂ (Fin N → Fin d))
    (hground : LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) =
      Submodule.span ℂ {ψ}) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) =
      Submodule.span ℂ {Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) ψ} := by
  rw [isometricInteractionExtension_ker_eq_map E hE A hA hN hcommOld hcommNew,
    hground, Submodule.map_span, Set.image_singleton]

end MPSTensor
