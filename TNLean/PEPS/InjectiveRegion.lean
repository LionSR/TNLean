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

/-- An abstract predicate assigning injectivity to finite vertex regions.

This is the region-level injectivity hypothesis used in the normal PEPS
blocking argument of arXiv:1804.04964, Section 3.  It is distinct from
one-vertex injectivity, since the source proof applies injectivity to blocked
regions such as \(R\), \(S\), \(T\), and their complements.
Source: arXiv:1804.04964, Section 3, lines 1407--1545 of
`Papers/1804.04964/paper_normal.tex`. -/
structure RegionInjectivityData (V : Type*) where
  /-- The assertion that a finite vertex region is injective after blocking. -/
  IsInjective : Finset V → Prop

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

/-- The complement of a finite region in the ambient vertex set. -/
def regionComplement [Fintype V] (R : Finset V) : Finset V :=
  Finset.univ \ R

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

@[simp] theorem mem_regionComplement [Fintype V] (R : Finset V) (v : V) :
    v ∈ regionComplement R ↔ v ∉ R := by
  simp [regionComplement]

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

/-- Every vertex belongs to one of the four regions in the decomposition. -/
theorem regionFourPart_cases [Fintype V] (A B : Finset V) (v : V) :
    v ∈ regionOnlyLeft A B ∨ v ∈ regionOverlap A B ∨
      v ∈ regionOnlyRight A B ∨ v ∈ regionOutsideUnion A B := by
  by_cases hvA : v ∈ A
  · by_cases hvB : v ∈ B
    · exact Or.inr <| Or.inl <| by simp [regionOverlap, hvA, hvB]
    · exact Or.inl <| by simp [regionOnlyLeft, hvA, hvB]
  · by_cases hvB : v ∈ B
    · exact Or.inr <| Or.inr <| Or.inl <| by simp [regionOnlyRight, hvA, hvB]
    · exact Or.inr <| Or.inr <| Or.inr <| by
        simp [regionOutsideUnion, hvA, hvB]

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

/-- The left-only region is disjoint from the outside region. -/
theorem regionOnlyLeft_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.1 <|
    (mem_regionOnlyLeft A B v).mp hvLeft |>.1

/-- The overlap is disjoint from the outside region. -/
theorem regionOverlap_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOverlap A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvOverlap hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.1 <|
    (mem_regionOverlap A B v).mp hvOverlap |>.1

/-- The right-only region is disjoint from the outside region. -/
theorem regionOnlyRight_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyRight A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvRight hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.2 <|
    (mem_regionOnlyRight A B v).mp hvRight |>.1

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
