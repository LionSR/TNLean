/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OwnerOutputCoordinates
import TNLean.PEPS.Approximation.SeparatedPhysicalDensity

/-!
# Actual output coordinates of the separated source calculation

The canonical party partition identifies the original physical/discard
coordinates with the coordinates of the two actual local outputs. The local
Schmidt expansion supplies the vector equality; the result introduces no
additional output identification, normalization, or contraction premise.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–480.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-separatedoutputcoordinates-01
TNLean.PEPS.PairEffect.Layout.mapOwner_mapOwner_coordinates_eq_separated
Provenance-ID: 8769-source-resource-separatedoutputcoordinates-02
TNLean.PEPS.PairEffect.Layout.partition_coordinates_eq_separated
Provenance-ID: 8769-source-resource-separatedoutputcoordinates-03
TNLean.PEPS.PairEffect.Layout.regionalOutputIso
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Word

end TNLean.PEPS.PairEffect.Word
namespace TNLean.PEPS.PairEffect.Layout
variable {P X Y d e I T : Type} [Fintype X] [Fintype Y] [Fintype d] [Fintype e]
    [Fintype I] [Fintype T]

/-- The physical/discard isometry for a regional output with its actual concatenation cast. -/
def regionalOutputIso (f : P → Bool) (a b L : Layout P) (h : L = a ++ b)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a))) :
    Mem (restrict f L) ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] Mem (restrict f b) :=
  (memCongr (congrArg (restrict f) h)).trans (partitionOutputIso f a b bA)

/-- The regional output isometry identifies the actual physical and discarded coordinates. -/
private theorem regionalOutputIso_coordinates (f : P → Bool) (a b L : Layout P)
    (h : L = a ++ b) (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (z : Mem (restrict f L)) (x : X) (i : d) :
    ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).repr
      (regionalOutputIso f a b L h bA z) (x, i) =
      ((partitionAppendBasis f a b bA bD).map
        (memCongr (congrArg (restrict f) h)).symm).repr z (x, i) := by
  exact partitionOutputIso_coordinates f a b bA bD
    (memCongr (congrArg (restrict f) h) z) x i

/-- A Schmidt expansion through the two local words gives precisely the
separated physical coordinates in the original product basis. -/
theorem partition_coordinates_eq_separated (f : P → Bool) (a b L : Layout P)
    (h : L = a ++ b)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bE : OrthonormalBasis Y ℂ (Mem (restrict (fun p ↦ !f p) a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (bF : OrthonormalBasis e ℂ (Mem (restrict (fun p ↦ !f p) b)))
    {c c' : Layout P} (v : Word c (restrict f L))
    (v' : Word c' (restrict (fun p ↦ !f p) L))
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem c)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c') (tau : T → ℝ)
    (z : Mem L) (k : I)
    (hz : partitionIso f L z = ∑ t, (Real.sqrt (tau t) : ℂ) •
      (v.eval (F (EuclideanSpace.basisFun (I × T) ℂ (k, t))) ⊗ₜ[ℂ]
        v'.eval (G (EuclideanSpace.basisFun T ℂ t))))
    (x : X) (y : Y) (i : d) (j : e) :
    ((partitionBasis f a bA bE).tensorProduct (partitionBasis f b bD bF)).repr
        (appendIso a b (memCongr h z)) ((x, y), (i, j)) =
      Word.separatedPhysicalCoordinates (regionalOutputIso f a b L h bA) v F tau
        (regionalOutputIso (fun p ↦ !f p) a b L h bE) v' G bD bF k
          ((x, y), (i, j)) := by
  rw [partitionBasis_coordinates_of_eq, hz]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  unfold Word.separatedPhysicalCoordinates Word.separatedSchmidtOutput
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Word.physicalComponent, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [Word.repr_effectMap, regionalOutputIso_coordinates, regionalOutputIso_coordinates]

/-- For the two actual owner maps, the original physical/discard coordinates
are exactly the separated coordinates of the local Schmidt outputs. The only
vector premise is the local-word expansion supplied by the circuit factorization. -/
theorem mapOwner_mapOwner_coordinates_eq_separated {Q R : Type}
    (q : P → Q) (r : Q → R) (f : R → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f (mapOwner r (mapOwner q a)))))
    (bE : OrthonormalBasis Y ℂ
      (Mem (restrict (fun p ↦ !f p) (mapOwner r (mapOwner q a)))))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f (mapOwner r (mapOwner q b)))))
    (bF : OrthonormalBasis e ℂ
      (Mem (restrict (fun p ↦ !f p) (mapOwner r (mapOwner q b)))))
    {c c' : Layout R} (v : Word c (restrict f (mapOwner r (mapOwner q (a ++ b)))))
    (v' : Word c' (restrict (fun p ↦ !f p) (mapOwner r (mapOwner q (a ++ b)))))
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem c)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c') (tau : T → ℝ)
    (z : Mem (a ++ b)) (k : I)
    (hz : partitionIso f (mapOwner r (mapOwner q (a ++ b)))
        (mapOwnerIso r (mapOwner q (a ++ b)) (mapOwnerIso q (a ++ b) z)) =
      ∑ t, (Real.sqrt (tau t) : ℂ) •
        (v.eval (F (EuclideanSpace.basisFun (I × T) ℂ (k, t))) ⊗ₜ[ℂ]
          v'.eval (G (EuclideanSpace.basisFun T ℂ t))))
    (x : X) (y : Y) (i : d) (j : e) :
    let a' := mapOwner r (mapOwner q a)
    let b' := mapOwner r (mapOwner q b)
    let L := mapOwner r (mapOwner q (a ++ b))
    let h : L = a' ++ b' := (congrArg (mapOwner r) (mapOwner_append q a b)).trans
      (mapOwner_append r (mapOwner q a) (mapOwner q b))
    ((((partitionBasis f a' bA bE).map (mapOwnerIso r (mapOwner q a)).symm).map
      (mapOwnerIso q a).symm).tensorProduct
      (((partitionBasis f b' bD bF).map (mapOwnerIso r (mapOwner q b)).symm).map
        (mapOwnerIso q b).symm)).repr (appendIso a b z) ((x, y), (i, j)) =
      Word.separatedPhysicalCoordinates (regionalOutputIso f a' b' L h bA) v F tau
        (regionalOutputIso (fun p ↦ !f p) a' b' L h bE) v' G bD bF k
          ((x, y), (i, j)) := by
  intro a' b' L h
  rw [mapOwner_mapOwner_tensorBasis_coordinates]
  exact partition_coordinates_eq_separated f a' b' L h bA bE bD bF
    v v' F G tau _ k hz x y i j

end TNLean.PEPS.PairEffect.Layout
