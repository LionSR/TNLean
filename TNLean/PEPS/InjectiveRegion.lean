import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

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

/-- The union-closure assertion for region injectivity.

This is the formal hypothesis supplied by the tensor-level
union-of-injective-regions lemma.  It is recorded separately so later
coordinate arguments may use the source lemma without repeating its proof.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`. -/
structure RegionInjectivityUnionClosure (κ : RegionInjectivityData V) : Prop where
  /-- The union of two injective finite vertex regions is injective. -/
  union_injective :
    ∀ {A B : Finset V}, κ.IsInjective A → κ.IsInjective B → κ.IsInjective (A ∪ B)

/-- A nonempty finite union of injective regions is injective under union closure.

This is the finite iteration of the source lemma used when the displayed
regions \(R\), \(S\), and \(T\) are described as unions of smaller injective
rectangles.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and the
examples following it, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem RegionInjectivityUnionClosure.biUnion_injective
    {ι : Type*} {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {s : Finset ι} (hs : s.Nonempty) (R : ι → Finset V)
    (hR : ∀ i ∈ s, κ.IsInjective (R i)) :
    κ.IsInjective (s.biUnion R) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using hR i (by simp)
  | cons i s hi _ ih =>
      rw [Finset.cons_eq_insert, Finset.biUnion_insert]
      exact hUnion.union_injective (hR i (by simp)) (ih fun j hj => hR j (by simp [hj]))

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

/-- The outside block in the four-region decomposition is the complement of
`A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the fourth region in the blocked proof is written as
`(A ∪ B)ᶜ`. -/
theorem regionOutsideUnion_eq_regionComplement_union [Fintype V]
    (A B : Finset V) :
    regionOutsideUnion A B = regionComplement (A ∪ B) := by
  rfl

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

/-- The four regions, indexed in the order
\(A\setminus B\), \(A\cap B\), \(B\setminus A\), \((A\cup B)^c\). -/
def regionUnionPart [Fintype V] (A B : Finset V) (i : Fin 4) : Finset V :=
  if i = 0 then
    regionOnlyLeft A B
  else if i = 1 then
    regionOverlap A B
  else if i = 2 then
    regionOnlyRight A B
  else
    regionOutsideUnion A B

@[simp] theorem regionUnionPart_zero [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 = regionOnlyLeft A B := by
  simp [regionUnionPart]

@[simp] theorem regionUnionPart_one [Fintype V] (A B : Finset V) :
    regionUnionPart A B 1 = regionOverlap A B := by
  simp [regionUnionPart]

@[simp] theorem regionUnionPart_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 2 = regionOnlyRight A B := by
  simp [regionUnionPart]

@[simp] theorem regionUnionPart_three [Fintype V] (A B : Finset V) :
    regionUnionPart A B 3 = regionOutsideUnion A B := by
  simp [regionUnionPart, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide]

/-- The fourth indexed region is the complement of `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the tensor called `X` is attached to `(A ∪ B)ᶜ`, the fourth
piece of the blocked four-region picture. -/
theorem regionUnionPart_three_eq_regionComplement_union [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 3 = regionComplement (A ∪ B) := by
  rw [regionUnionPart_three, regionOutsideUnion_eq_regionComplement_union]

/-- The first two indexed regions reconstruct `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the source proof identifies `A` with the union of
`A \ B` and `A ∩ B` before applying injectivity of `A`. -/
theorem regionUnionPart_zero_union_one [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 = A := by
  simpa using regionOnlyLeft_union_overlap A B

/-- The subfamily of indexed regions `0,1` reconstructs `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inverse is applied to
\(A=(A\setminus B)\cup(A\cap B)\). -/
theorem regionUnionPart_biUnion_zero_one [Fintype V] (A B : Finset V) :
    ({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B) = A := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_zero_union_one A B

/-- The middle two indexed regions reconstruct `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap tensor, the source proof identifies
`B` with the union of `A ∩ B` and `B \ A`. -/
theorem regionUnionPart_one_union_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 1 ∪ regionUnionPart A B 2 = B := by
  simpa using regionOverlap_union_onlyRight A B

/-- The subfamily of indexed regions `1,2` reconstructs `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap tensor, the second inverse is
applied to \(B=(A\cap B)\cup(B\setminus A)\). -/
theorem regionUnionPart_biUnion_one_two [Fintype V] (A B : Finset V) :
    ({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B) = B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_one_union_two A B

/-- The first three indexed regions reconstruct `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the region whose injectivity is being proved is the union of the
three inside parts of the four-region decomposition. -/
theorem regionUnionPart_zero_union_one_union_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2 =
      A ∪ B := by
  simpa using regionThreePart_union A B

/-- The subfamily of indexed regions `0,1,2` reconstructs `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the injectivity conclusion is for the union of the three inside
indexed regions. -/
theorem regionUnionPart_biUnion_zero_one_two [Fintype V] (A B : Finset V) :
    ({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B) = A ∪ B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion, Finset.union_assoc] using
    regionUnionPart_zero_union_one_union_two A B

/-- Convenience form of `Finset.singleton_biUnion` for the outside indexed
region. -/
theorem regionUnionPart_biUnion_three [Fintype V] (A B : Finset V) :
    ({3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionUnionPart A B 3 := by
  rw [Finset.singleton_biUnion]

/-- The selected subfamily `3` is the complement of the selected inside
subfamily `0,1,2`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the proof starts with the three inside indexed blocks and a
boundary tensor on their complement. -/
theorem regionUnionPart_biUnion_three_eq_regionComplement_zero_one_two [Fintype V]
    (A B : Finset V) :
    ({3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_three, regionUnionPart_biUnion_zero_one_two,
    regionUnionPart_three_eq_regionComplement_union]

/-- The fourth indexed region is the intersection of the complements of `A`
and `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of `A` and then `B` are applied, the remaining
tensor is supported on the outside region \((A \cup B)^c=A^c\cap B^c\). -/
theorem regionUnionPart_three_eq_regionComplement_left_inter_right [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 3 = regionComplement A ∩ regionComplement B := by
  ext v
  simp [regionComplement]

/-- The right-only indexed region together with the outside region reconstructs
the complement of `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after applying injectivity of `A`, the remaining diagram contains
the `B \ A` block and the outside block. -/
theorem regionUnionPart_two_union_three_eq_regionComplement_left [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 2 ∪ regionUnionPart A B 3 = regionComplement A := by
  ext v
  simp only [regionUnionPart_two, regionUnionPart_three, Finset.mem_union,
    mem_regionOnlyRight, mem_regionOutsideUnion, mem_regionComplement]
  tauto

/-- The indexed subfamily `2,3` reconstructs the complement of `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of `A` is applied, the remaining diagram is
carried by `B \ A` and the outside block. -/
theorem regionUnionPart_biUnion_two_three_eq_regionComplement_left [Fintype V]
    (A B : Finset V) :
    ({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement A := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_two_union_three_eq_regionComplement_left A B

/-- The selected subfamily `2,3` is the complement of the selected subfamily
`0,1`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after applying injectivity of \(A\), the remaining indexed blocks
are precisely the complement of the two blocks forming \(A\). -/
theorem regionUnionPart_biUnion_two_three_eq_regionComplement_zero_one [Fintype V]
    (A B : Finset V) :
    ({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_two_three_eq_regionComplement_left,
    regionUnionPart_biUnion_zero_one]

/-- The left-only indexed region together with the outside region reconstructs
the complement of `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after the overlap is reinserted and injectivity of `B` is applied,
the remaining outside tensor is attached to the complement of `B`. -/
theorem regionUnionPart_zero_union_three_eq_regionComplement_right [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 3 = regionComplement B := by
  ext v
  simp only [regionUnionPart_zero, regionUnionPart_three, Finset.mem_union,
    mem_regionOnlyLeft, mem_regionOutsideUnion, mem_regionComplement]
  tauto

/-- The indexed subfamily `0,3` reconstructs the complement of `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of `B`, the
remaining diagram is carried by `A \ B` and the outside block. -/
theorem regionUnionPart_biUnion_zero_three_eq_regionComplement_right [Fintype V]
    (A B : Finset V) :
    ({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_zero_union_three_eq_regionComplement_right A B

/-- The selected subfamily `0,3` is the complement of the selected subfamily
`1,2`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of \(B\),
the remaining indexed blocks are precisely the complement of the two blocks
forming \(B\). -/
theorem regionUnionPart_biUnion_zero_three_eq_regionComplement_one_two [Fintype V]
    (A B : Finset V) :
    ({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_three_eq_regionComplement_right,
    regionUnionPart_biUnion_one_two]

/-- The right-only and outside indexed regions form the complement of the
first two indexed regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of \(A=(A\setminus B)\cup(A\cap B)\) is applied,
the remaining diagram is carried by the two complementary indexed pieces. -/
theorem regionUnionPart_two_union_three_eq_regionComplement_zero_union_one [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 2 ∪ regionUnionPart A B 3 =
      regionComplement (regionUnionPart A B 0 ∪ regionUnionPart A B 1) := by
  rw [regionUnionPart_two_union_three_eq_regionComplement_left,
    regionUnionPart_zero_union_one]

/-- The left-only and outside indexed regions form the complement of the middle
two indexed regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of
\(B=(A\cap B)\cup(B\setminus A)\), the remaining diagram is carried by the
two complementary indexed pieces. -/
theorem regionUnionPart_zero_union_three_eq_regionComplement_one_union_two [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 3 =
      regionComplement (regionUnionPart A B 1 ∪ regionUnionPart A B 2) := by
  rw [regionUnionPart_zero_union_three_eq_regionComplement_right,
    regionUnionPart_one_union_two]

/-- The first two indexed regions are the complement of the right-only and
outside regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inversion step uses injectivity of the region
`A = (A \ B) ∪ (A ∩ B)`, whose complement is the remaining two indexed
pieces. -/
theorem regionUnionPart_zero_union_one_eq_regionComplement_two_union_three [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 =
      regionComplement (regionUnionPart A B 2 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_zero_union_one, regionUnionPart_two_union_three_eq_regionComplement_left]
  ext v
  simp [regionComplement]

/-- The middle two indexed regions are the complement of the left-only and
outside regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the second inversion step uses injectivity of the region
`B = (A ∩ B) ∪ (B \ A)`, whose complement is the remaining two indexed
pieces. -/
theorem regionUnionPart_one_union_two_eq_regionComplement_zero_union_three [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 1 ∪ regionUnionPart A B 2 =
      regionComplement (regionUnionPart A B 0 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_one_union_two, regionUnionPart_zero_union_three_eq_regionComplement_right]
  ext v
  simp [regionComplement]

/-- The indexed four regions cover the whole finite vertex set. -/
theorem regionUnionPart_biUnion [Fintype V] (A B : Finset V) :
    Finset.univ.biUnion (regionUnionPart A B) = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    simp
  · intro _
    rcases regionFourPart_cases A B v with hv | hv | hv | hv
    · exact Finset.mem_biUnion.mpr ⟨0, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨2, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨3, by simp, by simpa using hv⟩

/-- Each vertex belongs to exactly one indexed part of the four-region
decomposition.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the proof blocks the tensor network into the four disjoint
regions `A \ B`, `A ∩ B`, `B \ A`, and `(A ∪ B)ᶜ`. -/
theorem regionUnionPart_exists_unique [Fintype V] (A B : Finset V) (v : V) :
    ∃! i : Fin 4, v ∈ regionUnionPart A B i := by
  by_cases hvA : v ∈ A
  · by_cases hvB : v ∈ B
    · refine ⟨1, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
    · refine ⟨0, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
  · by_cases hvB : v ∈ B
    · refine ⟨2, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
    · refine ⟨3, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢

/-- The source union-closure assertion, applied to the selected indexed
subregions forming \(A\) and \(B\), makes the three inside indexed regions
injective.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404.  In the source proof, injectivity of
\((A\setminus B)\cup(A\cap B)\) and of
\((A\cap B)\cup(B\setminus A)\) gives injectivity of their union, namely the
three inside blocks \(A\setminus B\), \(A\cap B\), and \(B\setminus A\). -/
theorem RegionInjectivityUnionClosure.regionUnionPart_inside_injective [Fintype V]
    {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {A B : Finset V}
    (hA : κ.IsInjective (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B)))
    (hB : κ.IsInjective (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B))) :
    κ.IsInjective (({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_one] at hA
  rw [regionUnionPart_biUnion_one_two] at hB
  rw [regionUnionPart_biUnion_zero_one_two]
  exact hUnion.union_injective hA hB

/-- Binary-union form of the four-region injectivity step.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404.  The source proof first uses injectivity of
\((A\setminus B)\cup(A\cap B)\), then reinserts the overlap and uses
injectivity of \((A\cap B)\cup(B\setminus A)\).  The remaining inside region
is \((A\setminus B)\cup(A\cap B)\cup(B\setminus A)=A\cup B\). -/
theorem RegionInjectivityUnionClosure.regionUnionPart_inside_binary_injective [Fintype V]
    {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {A B : Finset V}
    (hA : κ.IsInjective (regionUnionPart A B 0 ∪ regionUnionPart A B 1))
    (hB : κ.IsInjective (regionUnionPart A B 1 ∪ regionUnionPart A B 2)) :
    κ.IsInjective
      (regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2) := by
  rw [regionUnionPart_zero_union_one] at hA
  rw [regionUnionPart_one_union_two] at hB
  rw [regionUnionPart_zero_union_one_union_two]
  exact hUnion.union_injective hA hB

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

/-- The indexed region \(A=(A\setminus B)\cup(A\cap B)\) is disjoint from the
two indexed pieces forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: in the first inversion step, the tensor over \(A\) is removed and
the remaining diagram lives on the complementary indexed pieces. -/
theorem regionUnionPart_zero_one_disjoint_two_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 0 ∪ regionUnionPart A B 1)
      (regionUnionPart A B 2 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_zero_union_one, regionUnionPart_two_union_three_eq_regionComplement_left]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint A ((Finset.univ : Finset V) \ A))

/-- The indexed subfamily forming `A` is disjoint from the indexed subfamily
forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inverse step separates the tensor over \(A\) from the
two complementary indexed blocks. -/
theorem regionUnionPart_biUnion_zero_one_disjoint_two_three [Fintype V]
    (A B : Finset V) :
    Disjoint (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B))
      (({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_one,
    regionUnionPart_biUnion_two_three_eq_regionComplement_left]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint A ((Finset.univ : Finset V) \ A))

/-- The indexed region \(B=(A\cap B)\cup(B\setminus A)\) is disjoint from the
two indexed pieces forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: in the second inversion step, the tensor over \(B\) is removed and
only the complementary indexed pieces remain. -/
theorem regionUnionPart_one_two_disjoint_zero_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 1 ∪ regionUnionPart A B 2)
      (regionUnionPart A B 0 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_one_union_two, regionUnionPart_zero_union_three_eq_regionComplement_right]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint B ((Finset.univ : Finset V) \ B))

/-- The indexed subfamily forming `B` is disjoint from the indexed subfamily
forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the second inverse step separates the tensor over \(B\) from the
two complementary indexed blocks. -/
theorem regionUnionPart_biUnion_one_two_disjoint_zero_three [Fintype V]
    (A B : Finset V) :
    Disjoint (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B))
      (({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_one_two,
    regionUnionPart_biUnion_zero_three_eq_regionComplement_right]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint B ((Finset.univ : Finset V) \ B))

/-- The union of the three inside indexed regions is disjoint from the outside
indexed region.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the tensor called `X` in the proof is attached to the outside
block, separated from the three blocks inside `A ∪ B`. -/
theorem regionUnionPart_inside_disjoint_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2)
      (regionUnionPart A B 3) := by
  simpa using regionInside_disjoint_outside A B

/-- The indexed four regions are pairwise disjoint. -/
theorem regionUnionPart_pairwise_disjoint [Fintype V] (A B : Finset V) :
    Pairwise fun i j : Fin 4 =>
      Disjoint (regionUnionPart A B i) (regionUnionPart A B j) := by
  classical
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa using regionOnlyLeft_disjoint_overlap A B
  · simpa using regionOnlyLeft_disjoint_onlyRight A B
  · simpa using regionOnlyLeft_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_overlap A B).symm
  · exact (hij rfl).elim
  · simpa using (regionOnlyRight_disjoint_overlap A B).symm
  · simpa using regionOverlap_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_onlyRight A B).symm
  · simpa using regionOnlyRight_disjoint_overlap A B
  · exact (hij rfl).elim
  · simpa using regionOnlyRight_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_outside A B).symm
  · simpa using (regionOverlap_disjoint_outside A B).symm
  · simpa using (regionOnlyRight_disjoint_outside A B).symm
  · exact (hij rfl).elim

end PEPS
end TNLean
