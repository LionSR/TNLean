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

/-- An edge is incident to the region `R` when at least one endpoint lies in `R`.
The vertex product over `R` reads a global virtual configuration only at the
edges incident to `R`. -/
def IsRegionIncidentEdge (R : Finset V) (e : Edge G) : Prop :=
  e.1.1 ∈ R ∨ e.1.2 ∈ R

instance (R : Finset V) (e : Edge G) : Decidable (IsRegionIncidentEdge (G := G) R e) := by
  unfold IsRegionIncidentEdge; infer_instance

omit [Fintype V] in
/-- The vertex product over `R` reads a global virtual configuration only through
the edges incident to `R`: two configurations agreeing on every `R`-incident edge
give the same product. -/
theorem regionProd_congr (R : Finset V) (σ : V → Fin d) {ζ ζ' : VirtualConfig A}
    (h : ∀ e : Edge G, IsRegionIncidentEdge (G := G) R e → ζ e = ζ' e) :
    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w.1)) =
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ' ie.1) (σ w.1) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  refine h ie.1 ?_
  -- An edge incident to `w ∈ R` is incident to `R`.
  rcases ie.2 with hie | hie
  · exact Or.inl (by rw [hie]; exact w.2)
  · exact Or.inr (by rw [hie]; exact w.2)

/-! ### Identity insertion on a region boundary edge

Inserting the identity matrix on a boundary edge `f` of `R` collapses the doubled
boundary-configuration sum of `regionInsertedCoeff` to its diagonal: the identity
forces the two endpoint values on `f` to agree, and `SameAwayFromBond` forces
agreement on every other boundary bond, so the two boundary configurations
coincide. The result is the single-sum region/complement contraction. This is the
region analogue of `edgeInsertedCoeff_identity`. -/

open scoped Classical in
/-- **Identity region insertion.** Inserting the identity matrix on a boundary
edge `f` of `R` collapses `regionInsertedCoeff` to the single-sum region/complement
contraction over the shared boundary configuration. -/
theorem regionInsertedCoeff_identity (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A R μ σ *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ := by
  classical
  rw [regionInsertedCoeff_eq]
  -- Inner sum over `ν`: the identity matrix `1 (μ f) (ν f)` is `1` iff `μ f = ν f`,
  -- and `SameAwayFromBond f μ ν` forces `μ c = ν c` away from `f`; together
  -- `μ = ν`, so the inner sum collapses to the diagonal term `ν = μ`.
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.sum_eq_single μ]
  · -- Diagonal term: `SameAwayFromBond f μ μ` holds and `1 (μ f) (μ f) = 1`.
    have hdiag : SameAwayFromBond f μ μ := fun c _ => rfl
    rw [if_pos hdiag, Matrix.one_apply_eq, one_mul]
  · -- Off-diagonal `ν ≠ μ`: the summand vanishes.
    intro ν _ hνμ
    rw [mul_eq_zero, mul_eq_zero]
    left; left
    split_ifs with hsame
    · -- `SameAwayFromBond f μ ν` holds, so `ν` agrees with `μ` away from `f`.
      -- The identity entry forces `μ f = ν f`, hence `ν = μ`, contradicting `ν ≠ μ`.
      rw [Matrix.one_apply]
      split_ifs with hf
      · exact absurd (funext (fun c => by
          by_cases hc : c = f
          · subst hc; exact hf.symm
          · exact (hsame c hc).symm)) hνμ
      · rfl
    · rfl
  · intro hμ; exact absurd (Finset.mem_univ μ) hμ

end PEPS
end TNLean
