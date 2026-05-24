import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic

/-!
# Region decompositions for PEPS injectivity arguments

The finite-region decomposition used in the proof that the union of two
injective PEPS regions is injective consists of four canonical parts.

For two regions \(A\) and \(B\), the source proof partitions the vertex set into
four parts:

* \(A \setminus B\),
* \(A \cap B\),
* \(B \setminus A\),
* \((A \cup B)^c\).

The elementary identities below are used in the tensor-level proof of the
injective-union lemma.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma lem:injective_union](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [DecidableEq V]

/-! ### Four-region decomposition for two finite regions -/

/-- The part of the left region outside the right region. -/
def regionOnlyLeft (A B : Finset V) : Finset V :=
  A \ B

/-- The overlap of two regions. -/
def regionOverlap (A B : Finset V) : Finset V :=
  A ∩ B

/-- The part of the right region outside the left region. -/
def regionOnlyRight (A B : Finset V) : Finset V :=
  B \ A

/-- The complement of the union of two regions. -/
def regionOutsideUnion [Fintype V] (A B : Finset V) : Finset V :=
  Finset.univ \ (A ∪ B)

@[simp] theorem mem_regionOnlyLeft (A B : Finset V) (v : V) :
    v ∈ regionOnlyLeft A B ↔ v ∈ A ∧ v ∉ B := by
  simp [regionOnlyLeft]

@[simp] theorem mem_regionOverlap (A B : Finset V) (v : V) :
    v ∈ regionOverlap A B ↔ v ∈ A ∧ v ∈ B := by
  simp [regionOverlap]

@[simp] theorem mem_regionOnlyRight (A B : Finset V) (v : V) :
    v ∈ regionOnlyRight A B ↔ v ∈ B ∧ v ∉ A := by
  simp [regionOnlyRight]

@[simp] theorem mem_regionOutsideUnion [Fintype V] (A B : Finset V) (v : V) :
    v ∈ regionOutsideUnion A B ↔ v ∉ A ∧ v ∉ B := by
  simp [regionOutsideUnion, not_or]

/-- The left-only and overlap regions reconstruct the left region. -/
theorem regionOnlyLeft_union_overlap (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B = A := by
  simpa [regionOnlyLeft, regionOverlap] using Finset.sdiff_union_inter A B

/-- The overlap and right-only regions reconstruct the right region. -/
theorem regionOverlap_union_onlyRight (A B : Finset V) :
    regionOverlap A B ∪ regionOnlyRight A B = B := by
  simpa [regionOverlap, regionOnlyRight, Finset.union_comm, Finset.inter_comm] using
    Finset.sdiff_union_inter B A

/-- The three regions inside `A ∪ B` reconstruct the union. -/
theorem regionThreePart_union (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B = A ∪ B := by
  calc
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B =
        A ∪ regionOnlyRight A B := by rw [regionOnlyLeft_union_overlap]
    _ = A ∪ B := by
      simp [regionOnlyRight, Finset.union_sdiff_self_eq_union]

/-- The four regions form a decomposition of the whole finite vertex set. -/
theorem regionFourPart_union [Fintype V] (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B ∪
      regionOutsideUnion A B = Finset.univ := by
  calc
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B ∪
        regionOutsideUnion A B =
        (A ∪ B) ∪ (Finset.univ \ (A ∪ B)) := by
          rw [regionThreePart_union, regionOutsideUnion]
    _ = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ (A ∪ B))

/-- The left-only region is disjoint from the overlap. -/
theorem regionOnlyLeft_disjoint_overlap (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOverlap A B) := by
  simpa [regionOnlyLeft, regionOverlap] using Finset.disjoint_sdiff_inter A B

/-- The right-only region is disjoint from the overlap. -/
theorem regionOnlyRight_disjoint_overlap (A B : Finset V) :
    Disjoint (regionOnlyRight A B) (regionOverlap A B) := by
  simpa [regionOnlyRight, regionOverlap, Finset.inter_comm] using
    Finset.disjoint_sdiff_inter B A

/-- The left-only and right-only regions are disjoint. -/
theorem regionOnlyLeft_disjoint_onlyRight (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOnlyRight A B) := by
  simpa [regionOnlyLeft, regionOnlyRight] using
    (disjoint_sdiff_sdiff : Disjoint (A \ B) (B \ A))

/-- The outside region is disjoint from the union of the three inside regions. -/
theorem regionInside_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B)
      (regionOutsideUnion A B) := by
  rw [regionThreePart_union]
  simpa [regionOutsideUnion] using
    (disjoint_sdiff_self_right :
      Disjoint (A ∪ B) ((Finset.univ : Finset V) \ (A ∪ B)))

end PEPS
end TNLean
