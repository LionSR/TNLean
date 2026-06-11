import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.FundamentalTheorem.EdgeInsertion

/-!
# Region-level gauge absorption on the region-inserted coefficient

This file ports the open-edge gauge cancellation
(`edgeInsertedCoeff_applyGauge`) to the region granularity: applying an oriented
edge-gauge family to a PEPS tensor and reading the region-inserted coefficient on a
boundary edge `f` of a region `R` equals reading the ungauged region-inserted
coefficient with the inserted matrix conjugated by the transpose of the open-edge
gauge `X f`.

The bridge factors through the general-matrix region-to-edge factorization
`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`: a region-inserted coefficient on a
boundary edge `f` of `R` equals the bond-dimension product over the edges not
crossing the boundary of `R` (the overcounting multiplicity `regionInteriorBondProd`)
times the edge-inserted coefficient on `f` of the assembled physical configuration.
Because gauge absorption preserves bond dimensions, that multiplicity is unchanged
by the gauge, so the region bridge reduces to the edge bridge
`edgeInsertedCoeff_applyGauge`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--586 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The general-matrix double-global-configuration form

The region-inserted coefficient with an arbitrary matrix `M` inserted on the
boundary edge `f`, in its double-global-configuration form: a sum over pairs of
global virtual configurations agreeing on every boundary edge of `R` other than
`f`, weighted by the matrix entry `M` on the two `f`-values. This generalizes
`regionInsertedCoeff_identity_eq_doubleSum`, which is the `M = 1` case after the
identity forces agreement on `f` too. -/

open scoped Classical in
/-- A boundary-fibered double sum collapses to a single sum reading the boundary
label: summing first over a boundary configuration `μ`, then over the global
configurations whose region boundary label is `μ`, is the same as summing over all
global configurations and reading the boundary label off each one. -/
private theorem sum_regionBoundary_fiber (A : Tensor G d) (R : Finset V)
    (F : RegionBoundaryConfig (G := G) A R → VirtualConfig A → ℂ) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
        F μ ζ) =
      ∑ ζ : VirtualConfig A, F (regionBoundaryLabel (G := G) A R ζ) ζ := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A R ζ)]
  · rw [if_pos rfl]
  · intro μ _ hμ; rw [if_neg (fun h => hμ h.symm)]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped Classical in
/-- The region-inserted coefficient with inserted matrix `M`, as a double sum over
pairs of global virtual configurations agreeing on every boundary edge of `R`
other than `f`, weighted by `M` on the two `f`-values. -/
theorem regionInsertedCoeff_eq_doubleSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig A × VirtualConfig A =>
            ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
              p.1 c.1 = p.2 c.1),
        M (p.1 f.1) (p.2 f.1) *
          (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
            ∏ w : {w : V // w ∈ Finset.univ \ R},
              A.component w.1 (fun ie => p.2 ie.1) (τ w) := by
  classical
  rw [regionInsertedCoeff_eq]
  -- Expand each blocked-region weight as a filtered sum over global configurations.
  simp only [regionBlockedWeight]
  -- Pull each inner pair of weight sums into the (μ, ν) double sum.
  rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ν : RegionBoundaryConfig (G := G) A R,
          (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
            (∑ ζ ∈ Finset.univ.filter
                (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
              ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
            ∑ ξ ∈ Finset.univ.filter
              (fun ξ : VirtualConfig A =>
                regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
                  regionComplementBoundaryConfig (G := G) A R ν),
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w)) =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ν : RegionBoundaryConfig (G := G) A R,
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
            ∑ ξ ∈ Finset.univ.filter
              (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = ν),
              (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
                (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
                  ∏ w : {w : V // w ∈ Finset.univ \ R},
                    A.component w.1 (fun ie => ξ ie.1) (τ w) from ?_]
  · -- Reindex the quadruple sum (μ, ν, ζ, ξ) onto the agreeing-off-`f` pair sum.
    -- Collapse the μ-filter (forcing μ = label ζ) and the ν-filter (forcing ν = label ξ),
    -- leaving a plain (ζ, ξ) double sum with the coupling read at the boundary labels.
    rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
          ∑ ν : RegionBoundaryConfig (G := G) A R,
            ∑ ζ ∈ Finset.univ.filter
                (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
              ∑ ξ ∈ Finset.univ.filter
                (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = ν),
                (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
                  (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
                    ∏ w : {w : V // w ∈ Finset.univ \ R},
                      A.component w.1 (fun ie => ξ ie.1) (τ w)) =
        ∑ ζ : VirtualConfig A, ∑ ξ : VirtualConfig A,
          (if SameAwayFromBond f (regionBoundaryLabel (G := G) A R ζ)
              (regionBoundaryLabel (G := G) A R ξ) then
            M (regionBoundaryLabel (G := G) A R ζ f) (regionBoundaryLabel (G := G) A R ξ f)
            else 0) *
            (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w) from ?_]
    · -- Now `(ζ, ξ)` against the agreeing-off-`f` filter; the predicate matches.
      -- Convert the right-hand filtered pair sum into the `(ζ, ξ)` double sum.
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simp only [SameAwayFromBond, regionBoundaryLabel_apply]
      refine Finset.sum_congr rfl (fun ζ _ => ?_)
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases hsame : ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
          ζ c.1 = ξ c.1
      · rw [if_pos hsame, if_pos hsame]
      · rw [if_neg hsame, if_neg hsame, zero_mul, zero_mul]
    · -- Carry out the (μ, ν) collapse using the boundary-fiber lemma twice. First swap
      -- the `ν`-sum inside the `ζ`-filtered sum so that `(μ, ζ)` are adjacent.
      rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
            ∑ ν : RegionBoundaryConfig (G := G) A R,
              ∑ ζ ∈ Finset.univ.filter
                  (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
                ∑ ξ ∈ Finset.univ.filter
                  (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = ν),
                  (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
                    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
                      ∏ w : {w : V // w ∈ Finset.univ \ R},
                        A.component w.1 (fun ie => ξ ie.1) (τ w)) =
          ∑ μ : RegionBoundaryConfig (G := G) A R,
            ∑ ζ ∈ Finset.univ.filter
                (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
              ∑ ν : RegionBoundaryConfig (G := G) A R,
                ∑ ξ ∈ Finset.univ.filter
                  (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = ν),
                  (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
                    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
                      ∏ w : {w : V // w ∈ Finset.univ \ R},
                        A.component w.1 (fun ie => ξ ie.1) (τ w) from
        Finset.sum_congr rfl (fun μ _ => (Finset.sum_comm).symm)]
      -- Collapse the `(μ, ζ)` fiber, then the `(ν, ξ)` fiber.
      rw [sum_regionBoundary_fiber A R
        (fun μ ζ => ∑ ν : RegionBoundaryConfig (G := G) A R,
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = ν),
            (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
              (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
                ∏ w : {w : V // w ∈ Finset.univ \ R},
                  A.component w.1 (fun ie => ξ ie.1) (τ w))]
      refine Finset.sum_congr rfl (fun ζ _ => ?_)
      rw [sum_regionBoundary_fiber A R
        (fun ν ξ =>
          (if SameAwayFromBond f (regionBoundaryLabel (G := G) A R ζ) ν then
            M (regionBoundaryLabel (G := G) A R ζ f) (ν f) else 0) *
            (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w))]
  · -- Distribute each `(μ, ν)` weight factor into the two inner filtered sums.
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    -- Reassociate the coupling out, distribute the product of sums, then push it back in.
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' id id ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R ν ξ).mp hξ
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R ν ξ).mpr hξ
    · intro ξ _; simp only [id_eq]; ring

end PEPS
end TNLean
