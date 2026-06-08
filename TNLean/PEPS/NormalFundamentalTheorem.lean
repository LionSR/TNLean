import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.FundamentalTheorem

/-!
# Fundamental Theorem for normal PEPS

This file assembles the region-level ingredients for the normal PEPS Fundamental
Theorem (arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`).

The injective Fundamental Theorem (`TNLean.PEPS.fundamentalTheorem_PEPS`) compares
a single vertex against its complement. The normal theorem replaces the single
vertex by an arbitrary injective region: blocking the lattice into three injective
regions around every edge, and comparing two one-site-different injective regions
with injective complements. The region-level insertion machinery
(`regionInsertedCoeff`, `regionTwoBlock`, `regionComplementTwoBlock`,
`sameTwoBlockInsertions_of_regionInsertedCoeff_eq`) plays the role that the
edge-centred insertion chain plays in the injective case.

This file builds, from the bottom up:

* `assembleRegionσ`, `stateCoeff_eq_regionComplement`: the region/complement
  decomposition of the closed state coefficient, the region analogue of
  `stateCoeff_eq_vertexComplement`.
* `regionInsertedCoeff_identity`, `regionInsertedCoeff_identity_eq_stateCoeff`,
  `SameState.regionInsertedCoeff_identity_eq`: inserting the identity on a
  boundary edge of a region recovers the closed state coefficient, so equal
  states give equal identity-inserted region coefficients. These are the region
  analogues of `edgeInsertedCoeff_identity`, `edgeInsertedCoeff_identity_eq_stateCoeff`,
  and `SameState.edgeInsertedCoeff_identity_eq`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, theorem
  labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Region/complement decomposition of the closed state coefficient

The closed state coefficient splits at an arbitrary region `R`, as a contraction
of the blocked-region weight on `R` against the blocked-region weight on the set
complement `univ \ R`, summed over the boundary configuration on the edges
crossing the boundary of `R`. This is the region analogue of
`stateCoeff_eq_vertexComplement`, where the single vertex `v` is replaced by the
region `R` and its complement `V \ {v}` by `univ \ R`. -/

/-- Glue a physical configuration on the region `R` and a physical configuration
on the set complement `univ \ R` into a global physical configuration on all
vertices. -/
def assembleRegionσ (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : V → Fin d :=
  fun w => if h : w ∈ R then σ ⟨w, h⟩ else τ ⟨w, by simp [h]⟩

omit [DecidableRel G.Adj] in
@[simp] theorem assembleRegionσ_mem (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (w : {w : V // w ∈ R}) :
    assembleRegionσ (V := V) (d := d) R σ τ w.1 = σ w := by
  simp [assembleRegionσ, w.2]

omit [DecidableRel G.Adj] in
@[simp] theorem assembleRegionσ_notMem (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (w : {w : V // w ∈ Finset.univ \ R}) :
    assembleRegionσ (V := V) (d := d) R σ τ w.1 = τ w := by
  have hw : w.1 ∉ R := by
    have := w.2
    rw [Finset.mem_sdiff] at this
    exact this.2
  rw [assembleRegionσ, dif_neg hw]

end PEPS
end TNLean
