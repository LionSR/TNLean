/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyPartitionAppend
import TNLean.PEPS.Approximation.LayoutOwnerMap
import TNLean.PEPS.Approximation.LayoutEqualityCoordinates

/-!
# Physical and discarded coordinates adapted to a party partition

The physical and discarded bases are independently adapted to the same party
partition. Their joint coordinates coincide with the coordinates obtained by
first gathering all affected registers and all exterior registers. Every
identification is the canonical one for the actual register lists.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
variable {P X Y d e : Type} [Fintype X] [Fintype Y] [Fintype d] [Fintype e]

/-- The product of the two regional bases, transported to the original memory. -/
def partitionBasis (f : P → Bool) (a : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bE : OrthonormalBasis Y ℂ (Mem (restrict (fun p ↦ !f p) a))) :
    OrthonormalBasis (X × Y) ℂ (Mem a) :=
  (bA.tensorProduct bE).map (partitionIso f a).symm

/-- Physical and discarded coordinates on the selected part of a concatenated layout. -/
def partitionAppendBasis (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b))) :
    OrthonormalBasis (X × d) ℂ (Mem (restrict f (a ++ b))) :=
  (bA.tensorProduct bD).map
    ((appendIso (restrict f a) (restrict f b)).symm.trans
      (memCongr (restrict_append f a b).symm))

/-- The physical/discard product basis agrees with the affected/exterior product
basis after the actual register partition, with the four indices in the indicated order. -/
theorem partitionIso_partitionBasis_tmul (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bE : OrthonormalBasis Y ℂ (Mem (restrict (fun p ↦ !f p) a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (bF : OrthonormalBasis e ℂ (Mem (restrict (fun p ↦ !f p) b)))
    (x : X) (y : Y) (i : d) (j : e) :
    partitionIso f (a ++ b) ((appendIso a b).symm
      (partitionBasis f a bA bE (x, y) ⊗ₜ[ℂ] partitionBasis f b bD bF (i, j))) =
      partitionAppendBasis f a b bA bD (x, i) ⊗ₜ[ℂ]
        partitionAppendBasis (fun p ↦ !f p) a b bE bF (y, j) := by
  apply eq_of_heq
  have h := partitionIso_append_tmul f a b
    (partitionBasis f a bA bE (x, y)) (partitionBasis f b bD bF (i, j))
  simp only [partitionBasis, OrthonormalBasis.map_apply, OrthonormalBasis.tensorProduct_apply,
    LinearIsometryEquiv.apply_symm_apply, appendPartitionIso_tmul] at h
  simp only [partitionBasis, partitionAppendBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, LinearIsometryEquiv.trans_apply]
  apply h.trans
  exact (memCongr_tmul_heq (restrict_append f a b).symm
    (restrict_append (fun p ↦ !f p) a b).symm _ _).symm

/-- Joint physical/discard coordinates are the two local output coordinates,
with affected and exterior indices grouped separately. -/
theorem partitionBasis_coordinates (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bE : OrthonormalBasis Y ℂ (Mem (restrict (fun p ↦ !f p) a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (bF : OrthonormalBasis e ℂ (Mem (restrict (fun p ↦ !f p) b)))
    (z : Mem (a ++ b)) (x : X) (y : Y) (i : d) (j : e) :
    ((partitionBasis f a bA bE).tensorProduct (partitionBasis f b bD bF)).repr
        (appendIso a b z) ((x, y), (i, j)) =
      ((partitionAppendBasis f a b bA bD).tensorProduct
        (partitionAppendBasis (fun p ↦ !f p) a b bE bF)).repr
          (partitionIso f (a ++ b) z) ((x, i), (y, j)) := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  simp only [OrthonormalBasis.tensorProduct_apply]
  rw [← partitionIso_partitionBasis_tmul, LinearIsometryEquiv.inner_map_map]
  exact ((appendIso a b).symm.inner_map_eq_flip _ z).symm

/-- The canonical physical/discard identification of one regional output memory. -/
def partitionOutputIso (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a))) :
    Mem (restrict f (a ++ b)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ X ⊗[ℂ] Mem (restrict f b) :=
  ((memCongr (restrict_append f a b)).trans
    (appendIso (restrict f a) (restrict f b))).trans
      (TensorProduct.congrIsometry bA.repr (LinearIsometryEquiv.refl ℂ _))

/-- The regional product basis is sent to the standard physical coordinates
and the original discarded basis. -/
theorem partitionOutputIso_basis (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b))) (x : X) (i : d) :
    partitionOutputIso f a b bA (partitionAppendBasis f a b bA bD (x, i)) =
      EuclideanSpace.basisFun X ℂ x ⊗ₜ[ℂ] bD i := by
  simp only [partitionOutputIso, partitionAppendBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, LinearIsometryEquiv.trans_apply]
  have h (L K : Layout P) (he : L = K) (z : Mem L) :
      memCongr he.symm (memCongr he z) = z := by
    cases he
    rfl
  rw [h, LinearIsometryEquiv.apply_symm_apply]
  change bA.repr (bA x) ⊗ₜ[ℂ] bD i = _
  classical
  simp only [OrthonormalBasis.repr_self, EuclideanSpace.basisFun_apply]

/-- The regional physical/discard isometry preserves the indicated joint coordinates. -/
theorem partitionOutputIso_coordinates (f : P → Bool) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (z : Mem (restrict f (a ++ b))) (x : X) (i : d) :
    ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).repr
        (partitionOutputIso f a b bA z) (x, i) =
      (partitionAppendBasis f a b bA bD).repr z (x, i) := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.tensorProduct_apply, ← partitionOutputIso_basis,
    LinearIsometryEquiv.inner_map_map]

/-- Changing only owner labels preserves physical/discard product coordinates
in the bases transported by the actual owner-memory isometries. -/
theorem mapOwner_tensorBasis_coordinates {Q : Type} (q : P → Q) (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (mapOwner q a)))
    (bD : OrthonormalBasis d ℂ (Mem (mapOwner q b)))
    (z : Mem (a ++ b)) (x : X) (i : d) :
    ((bA.map (mapOwnerIso q a).symm).tensorProduct
      (bD.map (mapOwnerIso q b).symm)).repr (appendIso a b z) (x, i) =
      (bA.tensorProduct bD).repr
        (appendIso (mapOwner q a) (mapOwner q b)
          (memCongr (mapOwner_append q a b) (mapOwnerIso q (a ++ b) z))) (x, i) := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  simp only [OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.map_apply]
  let J := (mapOwnerIso q (a ++ b)).trans (memCongr (mapOwner_append q a b))
  have hJ : J ((appendIso a b).symm
      ((mapOwnerIso q a).symm (bA x) ⊗ₜ[ℂ] (mapOwnerIso q b).symm (bD i))) =
      (appendIso (mapOwner q a) (mapOwner q b)).symm (bA x ⊗ₜ[ℂ] bD i) := by
    simpa only [J, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      using mapOwnerIso_append_tmul q a b
        ((mapOwnerIso q a).symm (bA x)) ((mapOwnerIso q b).symm (bD i))
  calc
    _ = inner ℂ ((appendIso a b).symm
        ((mapOwnerIso q a).symm (bA x) ⊗ₜ[ℂ] (mapOwnerIso q b).symm (bD i))) z :=
      ((appendIso a b).symm.inner_map_eq_flip _ z).symm
    _ = inner ℂ (J ((appendIso a b).symm
        ((mapOwnerIso q a).symm (bA x) ⊗ₜ[ℂ] (mapOwnerIso q b).symm (bD i)))) (J z) :=
      (J.inner_map_map _ _).symm
    _ = _ := by
      rw [hJ]
      exact (appendIso (mapOwner q a) (mapOwner q b)).symm.inner_map_eq_flip _ _

/-- The same coordinate identity for an output register list identified with
its physical/discard concatenation by a specified layout equality. -/
theorem partitionBasis_coordinates_of_eq (f : P → Bool) (a b L : Layout P)
    (h : L = a ++ b)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f a)))
    (bE : OrthonormalBasis Y ℂ (Mem (restrict (fun p ↦ !f p) a)))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f b)))
    (bF : OrthonormalBasis e ℂ (Mem (restrict (fun p ↦ !f p) b)))
    (z : Mem L) (x : X) (y : Y) (i : d) (j : e) :
    ((partitionBasis f a bA bE).tensorProduct (partitionBasis f b bD bF)).repr
        (appendIso a b (memCongr h z)) ((x, y), (i, j)) =
      (((partitionAppendBasis f a b bA bD).map
        (memCongr (congrArg (restrict f) h)).symm).tensorProduct
        ((partitionAppendBasis (fun p ↦ !f p) a b bE bF).map
          (memCongr (congrArg (restrict (fun p ↦ !f p)) h)).symm)).repr
          (partitionIso f L z) ((x, i), (y, j)) := by
  cases h
  exact partitionBasis_coordinates f a b bA bE bD bF z x y i j

end TNLean.PEPS.PairEffect.Layout
