/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OutputPartitionCoordinates

/-!
# Physical coordinates after successive owner identifications

The physical and discarded bases are transported by the two actual owner maps.
Their product coordinates therefore agree with the regional output coordinates
of the twice-relabeled word. The only register equalities used are distribution
of each owner map over concatenation.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-owneroutputcoordinates-01
TNLean.PEPS.PairEffect.Layout.mapOwner_mapOwner_partitionBasis_coordinates
Provenance-ID: 8769-source-resource-owneroutputcoordinates-02
TNLean.PEPS.PairEffect.Layout.mapOwner_mapOwner_tensorBasis_coordinates
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
variable {P Q R X d : Type} [Fintype X] [Fintype d]

/-- Relabelling owners commutes with the identification of equal register lists. -/
private theorem mapOwnerIso_memCongr (q : P → Q) {a b : Layout P} (h : a = b)
    (x : Mem a) :
    mapOwnerIso q b (memCongr h x) =
      memCongr (congrArg (mapOwner q) h) (mapOwnerIso q a x) := by
  cases h
  rfl

/-- Successive identifications of register lists compose. -/
private theorem memCongr_trans_apply {a b c : Layout P} (h : a = b) (k : b = c)
    (x : Mem a) : memCongr k (memCongr h x) = memCongr (h.trans k) x := by
  cases h
  cases k
  rfl

/-- Two owner identifications preserve the physical/discard coordinates in the
successively transported endpoint bases. -/
theorem mapOwner_mapOwner_tensorBasis_coordinates (q : P → Q) (r : Q → R)
    (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (mapOwner r (mapOwner q a))))
    (bD : OrthonormalBasis d ℂ (Mem (mapOwner r (mapOwner q b))))
    (z : Mem (a ++ b)) (x : X) (i : d) :
    (((bA.map (mapOwnerIso r (mapOwner q a)).symm).map (mapOwnerIso q a).symm).tensorProduct
      ((bD.map (mapOwnerIso r (mapOwner q b)).symm).map (mapOwnerIso q b).symm)).repr
        (appendIso a b z) (x, i) =
      (bA.tensorProduct bD).repr
        (appendIso (mapOwner r (mapOwner q a)) (mapOwner r (mapOwner q b))
          (memCongr ((congrArg (mapOwner r) (mapOwner_append q a b)).trans
            (mapOwner_append r (mapOwner q a) (mapOwner q b)))
              (mapOwnerIso r (mapOwner q (a ++ b)) (mapOwnerIso q (a ++ b) z))))
                (x, i) := by
  rw [mapOwner_tensorBasis_coordinates, mapOwner_tensorBasis_coordinates,
    mapOwnerIso_memCongr, memCongr_trans_apply]

/-- The actual twice-relabeled output has the regional coordinates of the
original physical/discard vector in successively transported, partition-adapted bases. -/
theorem mapOwner_mapOwner_partitionBasis_coordinates {Y e : Type}
    [Fintype Y] [Fintype e] (q : P → Q) (r : Q → R) (f : R → Bool)
    (a b : Layout P)
    (bA : OrthonormalBasis X ℂ (Mem (restrict f (mapOwner r (mapOwner q a)))))
    (bE : OrthonormalBasis Y ℂ
      (Mem (restrict (fun p ↦ !f p) (mapOwner r (mapOwner q a)))))
    (bD : OrthonormalBasis d ℂ (Mem (restrict f (mapOwner r (mapOwner q b)))))
    (bF : OrthonormalBasis e ℂ
      (Mem (restrict (fun p ↦ !f p) (mapOwner r (mapOwner q b)))))
    (z : Mem (a ++ b)) (x : X) (y : Y) (i : d) (j : e) :
    let a' := mapOwner r (mapOwner q a)
    let b' := mapOwner r (mapOwner q b)
    let L := mapOwner r (mapOwner q (a ++ b))
    let h : L = a' ++ b' := (congrArg (mapOwner r) (mapOwner_append q a b)).trans
      (mapOwner_append r (mapOwner q a) (mapOwner q b))
    ((((partitionBasis f a' bA bE).map (mapOwnerIso r (mapOwner q a)).symm).map
      (mapOwnerIso q a).symm).tensorProduct
      (((partitionBasis f b' bD bF).map (mapOwnerIso r (mapOwner q b)).symm).map
        (mapOwnerIso q b).symm)).repr (appendIso a b z) ((x, y), (i, j)) =
      (((partitionAppendBasis f a' b' bA bD).map
        (memCongr (congrArg (restrict f) h)).symm).tensorProduct
        ((partitionAppendBasis (fun p ↦ !f p) a' b' bE bF).map
          (memCongr (congrArg (restrict (fun p ↦ !f p)) h)).symm)).repr
            (partitionIso f L
              (mapOwnerIso r (mapOwner q (a ++ b)) (mapOwnerIso q (a ++ b) z)))
                ((x, i), (y, j)) := by
  intro a' b' L h
  rw [mapOwner_mapOwner_tensorBasis_coordinates]
  exact partitionBasis_coordinates_of_eq f a' b' L h bA bE bD bF _ x y i j

end TNLean.PEPS.PairEffect.Layout
