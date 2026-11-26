/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.Insertion
import TNLean.PEPS.FundamentalTheorem.Injective.FundamentalTheorem
import TNLean.PEPS.Tensor.Region.RegionConfigSplit
import TNLean.PEPS.Tensor.Region.ConfigurationCalculus

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

This file supplies `regionInsertedCoeff_identity`, the identity-insertion formula
at a boundary edge of a region, the region analogue of `edgeInsertedCoeff_identity`.
The map `assembleRegionσ`, which glues a physical configuration on a region to one
on its complement, lives in `TNLean.PEPS.Tensor.Region.RegionConfigSplit`.

Inserting the identity on a boundary edge reads the closed state coefficient times the
interior bond product (`regionInsertedCoeff_identity_eq_doubleSum`,
`regionInsertedCoeff_one_eq_stateCoeff`). The region/complement decomposition of the
closed state coefficient it rests on (`stateCoeff_eq_regionComplement`) is a statement
about the tensor and its regions, in `TNLean/PEPS/Tensor/Region/ConfigurationCalculus.lean`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, theorem
  labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)

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

omit [Fintype V] in
/-- The vertex product over `R` reads a global virtual configuration only through
its `R`-incident edges. -/
theorem regionProd_congr {A : Tensor G d} (R : Finset V) (σ : V → Fin d)
    {ζ ζ' : VirtualConfig A}
    (h : ∀ e : Edge G, ManyBody.IsRegionIncidentEdge (G := G) R e → ζ e = ζ' e) :
    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w.1)) =
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ' ie.1) (σ w.1) := by
  exact regionProd_subtype_congr R (fun w => σ w.1) h

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
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
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
    rw [ite_eq_left hdiag, Matrix.one_apply_eq, one_mul]
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

/-! ### Vertex-injective specialization of the normal Fundamental Theorem

The general normal theorem of arXiv:1804.04964, Section 3 (theorem labelled
`normal`, lines 1576--1583) replaces single-vertex injectivity by region
injectivity: blocking into three injective regions around every edge and
comparing one-site-different injective regions with injective complements. The
per-edge gauge in that setting comes from applying the source insertion-algebra
isomorphism (`lem:inj_isomorph`) to the *blocked-region* three-site chain, which
requires a region-level Skolem--Noether step that is not yet formalized
(remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`).

The statement below records the vertex-injective specialization. When the two
tensors are already vertex injective, the injective Fundamental Theorem
(`fundamentalTheorem_PEPS`) supplies the gauge directly, so the normal blocking
hypotheses are not used in the proof; they document the normal framing of the
hypothesis bundle. -/

/-- **Vertex-injective specialization of the normal-PEPS Fundamental Theorem.**

For injective PEPS tensors `A`, `B` (`Tensor.IsInjective`) on a connected
graph, if `A` satisfies the normal blocking hypotheses and the two tensors
generate the same state, then their defining tensors are gauge equivalent.

**Scope restriction (vertex injectivity):** This is the vertex-injective
specialization of the general normal theorem of arXiv:1804.04964, Section 3
(theorem labelled `normal`, lines 1576--1583 of
`Papers/1804.04964/paper_normal.tex`). The general theorem assumes only region
injectivity (blocking into three injective regions around every edge, and
one-site-different injective regions with injective complements), not
single-vertex injectivity. Under vertex injectivity the gauge follows from the
injective Fundamental Theorem `fundamentalTheorem_PEPS`, so the region blocking
hypotheses are not used. The general region-injective theorem remains open: the
missing step is the region-level insertion-algebra isomorphism that produces the
per-edge gauge after blocking, recorded as remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem fundamentalTheorem_normalPEPS_of_vertexInjective (A B : Tensor G d)
    (hA : A.IsInjective) (hB : B.IsInjective)
    (hAB : SameState A B)
    (hconn : G.Connected)
    (_h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) :
    GaugeEquiv A B :=
  fundamentalTheorem_PEPS A B hA hB hAB hconn

/-! ### The boundary-agreement form of the identity region insertion

Summing the product of the blocked-region weight on `R` against the blocked-region
weight on `univ \ R` over the boundary configuration collapses the two boundary
filters into a single constraint: the two global virtual configurations agree on
every edge crossing the boundary of `R`. This is the double-global-sum form of
`regionInsertedCoeff_identity`, the starting point for the multiplicity collapse
to the closed state coefficient. -/

open scoped Classical in
/-- The identity-inserted region coefficient, in its double-global-configuration
form: a sum over pairs of global virtual configurations agreeing on the boundary
of `R`, of the region vertex product against the complement vertex product. -/
theorem regionInsertedCoeff_identity_eq_doubleSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
        (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
          ∏ w : {w : V // w ∈ Finset.univ \ R},
            A.component w.1 (fun ie => p.2 ie.1) (τ w) := by
  classical
  rw [regionInsertedCoeff_identity]
  -- Expand each blocked-region weight as a filtered sum over global configurations.
  simp only [regionBlockedWeight]
  -- Distribute the products of filtered sums and identify the combined filter.
  rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
        (∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
                regionComplementBoundaryConfig (G := G) A R μ),
            ∏ w : {w : V // w ∈ Finset.univ \ R},
              A.component w.1 (fun ie => ξ ie.1) (τ w)) =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = μ),
            (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w) from ?_]
  · -- Reindex the triple sum (μ, ζ, ξ) onto the boundary-agreement pair sum.
    simp only [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A R ζ)]
    · rw [ite_eq_left rfl]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases heq : regionBoundaryLabel (G := G) A R ζ = regionBoundaryLabel (G := G) A R ξ
      · rw [ite_eq_left heq.symm, ite_eq_left heq]
      · rw [ite_eq_right (fun h => heq h.symm), ite_eq_right heq]
    · intro μ _ hμ
      rw [ite_eq_right (fun h => hμ h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- The complement filter matches the region filter after the boundary-edge identification,
    -- and the product of sums is the doubled sum.
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    refine Finset.sum_congr ?_ (fun ξ _ => rfl)
    ext ξ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ

open scoped Classical in
/-- **Identity insertion reads the closed state coefficient.** Inserting the
identity matrix on a boundary edge `f` of `R` equals the bond-dimension product
over the edges not crossing the boundary of `R`, times the closed state
coefficient of the assembled physical configuration. This combines the
double-global-sum form of the identity insertion with the cardinality collapse.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_one_eq_stateCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  rw [regionInsertedCoeff_identity_eq_doubleSum (G := G) A R f σ τ,
    stateCoeff_eq_regionComplement (G := G) A R σ τ]

end PEPS
end TNLean
