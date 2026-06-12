import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.FundamentalTheorem.EdgeInsertion

/-!
# General-matrix double-global-configuration form of the region-inserted coefficient

This file gives the general-matrix double-global-configuration form of the
region-inserted coefficient (`regionInsertedCoeff_eq_doubleSum`): inserting a matrix
`M` on a boundary edge `f` of a region `R` and contracting `R` against its set
complement equals a sum over pairs of global virtual configurations agreeing on every
boundary edge of `R` other than `f`, weighted by the matrix entry of `M` on the two
`f`-values.

This generalizes `regionInsertedCoeff_identity_eq_doubleSum`, the `M = 1` case where
the identity forces agreement on `f` too. It is the region-granularity analogue of
the open-bond expansion `edgeInsertedCoeff_eq_pairSum`, and the starting point for
porting the open-edge gauge cancellation `edgeInsertedCoeff_applyGauge` to the region
granularity: the two boundary configurations decouple only on `f`, where the gauge
on the open edge survives and conjugates the inserted matrix, while every other
boundary edge and every interior edge cancels pairwise.

The file proves the corresponding gauge-absorption equality.  The region weight of a gauged tensor
against the complement weight of an agreeing pair is one global gauge-vertex product over all
vertices (`regionComplProd_gauge_eq`), reading the first configuration on the region and the
second on the complement (`pairOuter`), with the physical legs assembled.  The region/complement
contraction is the single-bond cut at the boundary edge `f`, up to the non-boundary
bond-dimension multiplicity that is gauge-invariant; this is the region-to-edge identity
`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`, proved by the `pairOuter` fiber collapse
(`pairOuterFiber_card`, `sum_pairOuter_fiber_collapse`).  The edge gauge cancellation
`edgeInsertedCoeff_applyGauge` then transports across, giving the edgewise region
gauge-absorption equality `regionInsertedCoeff_applyGauge`: every interior edge and every boundary
edge other than `f` cancels its gauge pairwise, while the two endpoint gauges on `f` conjugate
the inserted matrix (transposed per the orientation convention of `edgeGaugeAt`, recorded by
`regionEdgeOrient`).

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

/-! ### Global-product form of the gauged region weight

The region-inserted coefficient of a gauged tensor `applyGauge B Z`, in its
double-global-configuration form, expands each region and complement vertex weight as a
gauge-vertex sum.  Collecting the per-vertex inner configurations into one global local
configuration `ξ`, the gauge factors `edgeGaugeAt` over all vertices factor edgewise: every
interior edge of `R` and of its complement cancels to a consistency delta on `ξ`, while the
two endpoints of the single boundary edge `f` survive and conjugate the inserted matrix.  This
is the region-granularity port of `edgeInsertedCoeff_applyGauge`. -/

/-- The outer reading at a vertex of an agreeing pair: the region side reads the first
configuration, the complement side reads the second.  This is the global outer configuration
whose gauge factors cancel against the per-vertex inner configurations. -/
noncomputable def pairOuter (B : Tensor G d) (R : Finset V)
    (p : VirtualConfig B × VirtualConfig B) :
    OpenLocalConfig (G := G) B :=
  fun v _ie => if v ∈ R then p.1 _ie.1 else p.2 _ie.1

omit [Fintype V] in
/-- A region vertex reads the first configuration in `pairOuter`. -/
theorem pairOuter_mem (B : Tensor G d) (R : Finset V)
    (p : VirtualConfig B × VirtualConfig B) {v : V} (hv : v ∈ R)
    (ie : IncidentEdge G v) : pairOuter (G := G) B R p v ie = p.1 ie.1 := by
  simp [pairOuter, hv]

omit [Fintype V] in
/-- A complement vertex reads the second configuration in `pairOuter`. -/
theorem pairOuter_not_mem (B : Tensor G d) (R : Finset V)
    (p : VirtualConfig B × VirtualConfig B) {v : V} (hv : v ∉ R)
    (ie : IncidentEdge G v) : pairOuter (G := G) B R p v ie = p.2 ie.1 := by
  simp [pairOuter, hv]

open scoped Classical in
/-- The region weight against the complement weight of an agreeing pair, with the gauged
tensor, expands as a single global gauge-vertex product over all vertices: the region side
reads the first configuration, the complement side the second, and the physical legs assemble.

This is the first step of the region-granularity gauge-absorption equality: it brings the
double-global-configuration form of the gauged region-inserted coefficient
(`regionInsertedCoeff_eq_doubleSum`) into the single global gauge-vertex product whose
`edgeGaugeAt` factors cancel edgewise.  The remaining stage --- summing the gauge factors over
the agreeing pair, so that interior edges of `R` and of its complement cancel to consistency
deltas while the two endpoints of the boundary edge `f` conjugate the inserted matrix --- is
the open obligation recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem regionComplProd_gauge_eq (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (p : VirtualConfig B × VirtualConfig B) :
    (∏ w : {w : V // w ∈ R}, (applyGauge B Z).component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          (applyGauge B Z).component w.1 (fun ie => p.2 ie.1) (τ w) =
      ∏ v : V, gaugeVertex B Z v (pairOuter (G := G) B R p v)
        (assembleRegionσ (V := V) (d := d) R σ τ v) := by
  classical
  rw [← Finset.prod_sdiff (Finset.subset_univ R), mul_comm]
  congr 1
  · rw [Finset.prod_subtype (Finset.univ \ R)
      (p := fun w => w ∈ Finset.univ \ R) (fun w => Iff.rfl)
      (fun w => gaugeVertex B Z w (pairOuter (G := G) B R p w)
        (assembleRegionσ (V := V) (d := d) R σ τ w))]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hw : w.1 ∉ R := by have := w.2; rw [Finset.mem_sdiff] at this; exact this.2
    change gaugeVertex B Z w.1 _ _ = _
    rw [assembleRegionσ_notMem]
    congr 1
    funext ie
    exact (pairOuter_not_mem (G := G) B R p hw ie).symm
  · rw [Finset.prod_subtype R (p := fun w => w ∈ R) (fun w => Iff.rfl)
      (fun w => gaugeVertex B Z w (pairOuter (G := G) B R p w)
        (assembleRegionσ (V := V) (d := d) R σ τ w))]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    change gaugeVertex B Z w.1 _ _ = _
    rw [assembleRegionσ_mem]
    congr 1
    funext ie
    exact (pairOuter_mem (G := G) B R p w.2 ie).symm

open scoped Classical in
/-- The ungauged region weight against the complement weight of an agreeing pair is one global
vertex product over all vertices, reading the first configuration on the region and the second
on the complement.  This is the gauge-free special case of `regionComplProd_gauge_eq`. -/
theorem regionComplProd_eq (B : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (p : VirtualConfig B × VirtualConfig B) :
    (∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          B.component w.1 (fun ie => p.2 ie.1) (τ w) =
      ∏ v : V, B.component v (pairOuter (G := G) B R p v)
        (assembleRegionσ (V := V) (d := d) R σ τ v) := by
  classical
  rw [← Finset.prod_sdiff (Finset.subset_univ R), mul_comm]
  congr 1
  · rw [Finset.prod_subtype (Finset.univ \ R)
      (p := fun w => w ∈ Finset.univ \ R) (fun w => Iff.rfl)
      (fun w => B.component w (pairOuter (G := G) B R p w)
        (assembleRegionσ (V := V) (d := d) R σ τ w))]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hw : w.1 ∉ R := by have := w.2; rw [Finset.mem_sdiff] at this; exact this.2
    rw [assembleRegionσ_notMem]
    congr 1
    funext ie
    exact (pairOuter_not_mem (G := G) B R p hw ie).symm
  · rw [Finset.prod_subtype R (p := fun w => w ∈ R) (fun w => Iff.rfl)
      (fun w => B.component w (pairOuter (G := G) B R p w)
        (assembleRegionσ (V := V) (d := d) R σ τ w))]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [assembleRegionσ_mem]
    congr 1
    funext ie
    exact (pairOuter_mem (G := G) B R p w.2 ie).symm

/-! ### The double-global-configuration single-vertex-product forms

Combining the general-matrix double-global-configuration form
`regionInsertedCoeff_eq_doubleSum` with the agreeing-pair products
`regionComplProd_gauge_eq` and `regionComplProd_eq` brings both the gauged and the
ungauged region-inserted coefficients to a sum, over pairs of global virtual
configurations agreeing off the boundary edge `f`, of one global (gauge-)vertex
product over all vertices.  The two products share the outer reading `pairOuter`,
so the gauge-cancellation argument compares them at this single granularity. -/

open scoped Classical in
/-- The gauged region-inserted coefficient as a double sum over agreeing pairs of a
single global gauge-vertex product over all vertices, reading the first configuration
on the region and the second on the complement.

This combines the general-matrix double-global-configuration form
`regionInsertedCoeff_eq_doubleSum` with the agreeing-pair gauge-vertex product
`regionComplProd_gauge_eq`. -/
theorem regionInsertedCoeff_applyGauge_eq_doubleSum (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) (applyGauge B Z) R f M σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig B × VirtualConfig B =>
            ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
              p.1 c.1 = p.2 c.1),
        M (p.1 f.1) (p.2 f.1) *
          ∏ v : V, gaugeVertex B Z v (pairOuter (G := G) B R p v)
            (assembleRegionσ (V := V) (d := d) R σ τ v) := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum (applyGauge B Z) R f M σ τ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_assoc]
  congr 1
  exact regionComplProd_gauge_eq B R Z σ τ p

open scoped Classical in
/-- The ungauged region-inserted coefficient as a double sum over agreeing pairs of a
single global vertex product over all vertices, reading the first configuration on the
region and the second on the complement.

This combines the general-matrix double-global-configuration form
`regionInsertedCoeff_eq_doubleSum` with the agreeing-pair vertex product
`regionComplProd_eq`. -/
theorem regionInsertedCoeff_eq_doubleSum_vertex (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) B R f N σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig B × VirtualConfig B =>
            ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
              p.1 c.1 = p.2 c.1),
        N (p.1 f.1) (p.2 f.1) *
          ∏ v : V, B.component v (pairOuter (G := G) B R p v)
            (assembleRegionσ (V := V) (d := d) R σ τ v) := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum B R f N σ τ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_assoc]
  congr 1
  exact regionComplProd_eq B R σ τ p

/-! ### Toward the edgewise gauge cancellation

The double-sum single-vertex-product form factors each gauged vertex into the gauge
matrices times the ungauged vertex.  Collecting the inner local configurations into one
global inner configuration `ω` and swapping the inner/outer order isolates the gauge
factors into one inner-fibered sum: the global B-vertex product against `ω`, times the
sum over agreeing pairs of the inserted matrix and the gauge factors coupling the outer
reading `pairOuter` to `ω`.

The outer reading `pairOuter` of an agreeing pair is consistent off the boundary edge `f`
(`pairOuter_isConsistentOff`): on every interior edge and on every boundary edge other than
`f` the two endpoints carry the same index, so only `f` keeps its two distinct endpoint
indices, which the inserted matrix couples. -/

omit [Fintype V] in
/-- The outer reading `pairOuter` of an agreeing pair is consistent off the boundary edge
`f`: every interior edge has both endpoints on the same side, and every boundary edge other
than `f` carries equal indices on its two endpoints by the agreeing-pair hypothesis, so only
`f` may carry two distinct endpoint indices. -/
theorem pairOuter_isConsistentOff (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (p : VirtualConfig B × VirtualConfig B)
    (hp : ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
        p.1 c.1 = p.2 c.1) :
    IsConsistentOff (G := G) B f.1 (pairOuter (G := G) B R p) := by
  intro g hg
  rw [pairOuter, pairOuter]
  by_cases h1 : g.1.1 ∈ R <;> by_cases h2 : g.1.2 ∈ R
  · simp only [edgeLeftIncident, edgeRightIncident, h1, h2, if_true]
  · have hb : IsRegionBoundaryEdge (G := G) R g := Or.inl ⟨h1, h2⟩
    have : p.1 g = p.2 g := hp ⟨g, hb⟩ (fun h => hg (congrArg Subtype.val h))
    simp only [edgeLeftIncident, edgeRightIncident, h1, h2, if_true, if_false]
    exact this
  · have hb : IsRegionBoundaryEdge (G := G) R g := Or.inr ⟨h1, h2⟩
    have : p.1 g = p.2 g := hp ⟨g, hb⟩ (fun h => hg (congrArg Subtype.val h))
    simp only [edgeLeftIncident, edgeRightIncident, h1, h2, if_true, if_false]
    exact this.symm
  · simp only [edgeLeftIncident, edgeRightIncident, h1, h2, if_false]

open scoped Classical in
/-- The gauged region-inserted coefficient as an inner/outer double sum.  Summing over the
inner local configuration `ω`, the summand is the global ungauged B-vertex product against
`ω`, times the sum, over agreeing pairs, of the inserted matrix and the gauge factors
coupling the outer reading `pairOuter` to `ω` on every incident half-edge.

This factors each gauged vertex into its gauge matrices and the ungauged vertex
(`prod_gaugeVertex_eq_sum_local_open`) and swaps the inner/outer order, isolating the gauge
factors into the inner-fibered pair sum.  This is the region-granularity stage matching the
inner/outer split that `edgeInsertedCoeff_applyGauge` performs at the edge granularity before
the edgewise gauge sum. -/
theorem regionInsertedCoeff_applyGauge_eq_innerOuterSum (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) (applyGauge B Z) R f M σ τ =
      ∑ ω : OpenLocalConfig (G := G) B,
        (∏ v : V, B.component v (ω v) (assembleRegionσ (V := V) (d := d) R σ τ v)) *
          ∑ p ∈ Finset.univ.filter
              (fun p : VirtualConfig B × VirtualConfig B =>
                ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
                  p.1 c.1 = p.2 c.1),
            M (p.1 f.1) (p.2 f.1) *
              ∏ v : V, ∏ ie : IncidentEdge G v,
                edgeGaugeAt B Z v ie (pairOuter (G := G) B R p v ie) (ω v ie) := by
  classical
  rw [regionInsertedCoeff_applyGauge_eq_doubleSum B R Z f M σ τ]
  rw [Finset.sum_congr rfl (fun p _ => by
    rw [prod_gaugeVertex_eq_sum_local_open B Z (pairOuter (G := G) B R p)
      (assembleRegionσ (V := V) (d := d) R σ τ), Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

/-! ### The edgewise gauge-absorption equality

The region/complement contraction is the single-bond cut at the boundary edge `f`, up to the
non-boundary bond-dimension multiplicity, which is gauge-invariant.  Reading the outer reading
`pairOuter` of an agreeing pair at the in-region and complement endpoints of an edge
(`pairOuterReadFst`, `pairOuterReadSnd`), the agreeing pairs over a fixed consistent-off-`f`
configuration are parameterised by the free non-boundary legs (`pairOuterFiber_card`), so the
region-inserted coefficient is that multiplicity times the edge-inserted coefficient of the
assembled physical configuration (`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`).  The edge
gauge cancellation `edgeInsertedCoeff_applyGauge` then transports across, giving the region
gauge-absorption equality `regionInsertedCoeff_applyGauge`.  The map `regionEdgeOrient` records
the boundary-edge orientation forced by the edge convention of `edgeInsertedCoeff`. -/

/-- Read an outer config `ξ` at the in-region endpoint of an R-incident edge. -/
noncomputable def pairOuterReadFst (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B) (e : Edge G) : Fin (B.bondDim e) :=
  if _ : e.1.1 ∈ R then ξ e.1.1 (edgeLeftIncident (G := G) e)
  else ξ e.1.2 (edgeRightIncident (G := G) e)

/-- Read an outer config `ξ` at the complement endpoint of a complement-incident edge. -/
noncomputable def pairOuterReadSnd (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B) (e : Edge G) : Fin (B.bondDim e) :=
  if _ : e.1.1 ∈ R then ξ e.1.2 (edgeRightIncident (G := G) e)
  else ξ e.1.1 (edgeLeftIncident (G := G) e)

open scoped Classical in
/-- Rebuild a pair from an outer config and ghost legs on the non-boundary edges. -/
noncomputable def pairOuterFiberPair (B : Tensor G d) (R : Finset V)
    (ξ : OpenLocalConfig (G := G) B)
    (h : (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (B.bondDim e.1)) :
    VirtualConfig B × VirtualConfig B :=
  (fun e => if hinc : IsRegionIncidentEdge (G := G) R e then pairOuterReadFst (G := G) B R ξ e
              else h ⟨e, not_boundary_of_not_incident (G := G) R hinc⟩,
   fun e => if hb : IsRegionBoundaryEdge (G := G) R e then pairOuterReadSnd (G := G) B R ξ e
              else if _ : IsRegionIncidentEdge (G := G) R e then h ⟨e, hb⟩
              else pairOuterReadSnd (G := G) B R ξ e)

omit [Fintype V] in
/-- Reading `ξ` at the in-region endpoint of an edge incident to a vertex `v ∈ R`, when `ξ`
is consistent off `f` and the edge is not `f`, gives `ξ v ie`. -/
theorem pairOuterReadFst_eq (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    {v : V} (hv : v ∈ R) (ie : IncidentEdge G v) :
    pairOuterReadFst (G := G) B R ξ ie.1 = ξ v ie := by
  obtain ⟨e, hinc⟩ := ie
  -- `v` is `e.1.1` or `e.1.2`.
  rcases hinc with hL | hR
  · subst hL
    rw [pairOuterReadFst, dif_pos hv]
    rfl
  · subst hR
    by_cases h1 : e.1.1 ∈ R
    · -- both endpoints in R; e is not boundary; if e ≠ f, consistency gives equality.
      rw [pairOuterReadFst, dif_pos h1]
      by_cases hef : e = f.1
      · -- e = f but both endpoints in R contradicts f being a boundary edge.
        exfalso
        have hb := f.2
        rw [← hef] at hb
        rcases hb with ⟨_, h2⟩ | ⟨h1', _⟩
        · exact h2 (by exact ‹e.1.2 ∈ R›)
        · exact h1' h1
      · exact hξ e hef
    · rw [pairOuterReadFst, dif_neg h1]
      rfl

omit [Fintype V] in
/-- Reading `ξ` at the complement endpoint of an edge incident to a vertex `v ∉ R`, when `ξ`
is consistent off `f` and the edge is not `f`, gives `ξ v ie`. -/
theorem pairOuterReadSnd_eq (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    {v : V} (hv : v ∉ R) (ie : IncidentEdge G v) :
    pairOuterReadSnd (G := G) B R ξ ie.1 = ξ v ie := by
  obtain ⟨e, hinc⟩ := ie
  rcases hinc with hL | hR
  · subst hL
    rw [pairOuterReadSnd, dif_neg hv]
    rfl
  · subst hR
    by_cases h1 : e.1.1 ∈ R
    · rw [pairOuterReadSnd, dif_pos h1]
      rfl
    · -- both endpoints not in R; e not boundary; if e ≠ f consistency gives equality.
      rw [pairOuterReadSnd, dif_neg h1]
      by_cases hef : e = f.1
      · exfalso
        have hb := f.2
        rw [← hef] at hb
        rcases hb with ⟨h1', _⟩ | ⟨_, h2⟩
        · exact h1 h1'
        · exact hv h2
      · exact hξ e hef

omit [Fintype V] in
/-- The rebuilt pair's `pairOuter` recovers `ξ` (when `ξ` is consistent off `f`). -/
theorem pairOuter_pairOuterFiberPair (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ)
    (h : (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (B.bondDim e.1)) :
    pairOuter (G := G) B R (pairOuterFiberPair (G := G) B R ξ h) = ξ := by
  classical
  funext v ie
  rw [pairOuter]
  by_cases hv : v ∈ R
  · rw [if_pos hv]
    -- first component: edge ie.1 is R-incident (v ∈ R is an endpoint), reads pairOuterReadFst.
    have hinc : IsRegionIncidentEdge (G := G) R ie.1 := by
      rcases ie.2 with hie | hie
      · exact Or.inl (by rw [hie]; exact hv)
      · exact Or.inr (by rw [hie]; exact hv)
    simp only [pairOuterFiberPair, dif_pos hinc]
    exact pairOuterReadFst_eq (G := G) B R f ξ hξ hv ie
  · rw [if_neg hv]
    -- second component.
    simp only [pairOuterFiberPair]
    by_cases hb : IsRegionBoundaryEdge (G := G) R ie.1
    · rw [dif_pos hb]
      exact pairOuterReadSnd_eq (G := G) B R f ξ hξ hv ie
    · by_cases hinc : IsRegionIncidentEdge (G := G) R ie.1
      · -- ie.1 R-incident but v ∉ R, so the other endpoint ∈ R, hence ie.1 is boundary: contra hb.
        exfalso
        apply hb
        -- v is an endpoint of ie.1 and v ∉ R; the other endpoint is in R by incidence.
        rcases ie.2 with hie | hie
        · -- v = ie.1.1.
          have hv1 : ie.1.1.1 ∉ R := by rw [hie]; exact hv
          rcases hinc with h1 | h2
          · exact absurd h1 hv1
          · exact Or.inr ⟨hv1, h2⟩
        · -- v = ie.1.1.2.
          have hv2 : ie.1.1.2 ∉ R := by rw [hie]; exact hv
          rcases hinc with h1 | h2
          · exact Or.inl ⟨h1, hv2⟩
          · exact absurd h2 hv2
      · rw [dif_neg hb, dif_neg hinc]
        exact pairOuterReadSnd_eq (G := G) B R f ξ hξ hv ie

open scoped Classical in
/-- The `ξ`-fiber of the agreeing-off-`f` pairs under `pairOuter` has cardinality
`regionInteriorBondProd B R`. -/
theorem pairOuterFiber_card (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ξ : OpenLocalConfig (G := G) B) (hξ : IsConsistentOff (G := G) B f.1 ξ) :
    (Finset.univ.filter (fun p : VirtualConfig B × VirtualConfig B =>
        (∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1)
          ∧ pairOuter (G := G) B R p = ξ)).card =
      regionInteriorBondProd (G := G) B R := by
  classical
  rw [show regionInteriorBondProd (G := G) B R =
      (Finset.univ : Finset ((e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e})
        → Fin (B.bondDim e.1))).card from ?_]
  · refine Finset.card_nbij'
      (regionFiberLegs (G := G) B R) (pairOuterFiberPair (G := G) B R ξ) ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · -- The reconstruction lands in the `ξ`-fiber of agreeing-off-`f` pairs.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, pairOuter_pairOuterFiberPair (G := G) B R f ξ hξ h⟩
      -- agreement off `f` on boundary edges.
      intro c hc
      have hcb : IsRegionBoundaryEdge (G := G) R c.1 := c.2
      have hcinc : IsRegionIncidentEdge (G := G) R c.1 :=
        isRegionBoundaryEdge_touches (G := G) R hcb
      simp only [pairOuterFiberPair, dif_pos hcinc, dif_pos hcb]
      -- read-fst = read-snd on a boundary edge ≠ f, by consistency.
      have hcf : c.1 ≠ f.1 := fun h => hc (Subtype.ext h)
      rw [pairOuterReadFst, pairOuterReadSnd]
      by_cases h1 : c.1.1.1 ∈ R
      · simp only [dif_pos h1]; exact hξ c.1 hcf
      · simp only [dif_neg h1]; exact (hξ c.1 hcf).symm
    · -- Reconstructing from the fiber legs of a fiber pair recovers the pair.
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hagree, hmerge⟩ := hp
      refine Prod.ext ?_ ?_
      · funext e
        simp only [pairOuterFiberPair, regionFiberLegs]
        by_cases hinc : IsRegionIncidentEdge (G := G) R e
        · rw [dif_pos hinc]
          -- pairOuterReadFst ξ e = p.1 e because pairOuter p = ξ and e is R-incident.
          subst hmerge
          rw [pairOuterReadFst]
          by_cases h1 : e.1.1 ∈ R
          · simp only [dif_pos h1, pairOuter, edgeLeftIncident, if_pos h1]
          · -- e R-incident, e.1.1 ∉ R, so e.1.2 ∈ R.
            have h2 : e.1.2 ∈ R := by
              rcases hinc with h | h
              · exact absurd h h1
              · exact h
            simp only [dif_neg h1, pairOuter, edgeRightIncident, if_pos h2]
        · rw [dif_neg hinc, if_neg hinc]
      · funext e
        simp only [pairOuterFiberPair, regionFiberLegs]
        by_cases hb : IsRegionBoundaryEdge (G := G) R e
        · rw [dif_pos hb]
          -- boundary edge: pairOuterReadSnd ξ e = p.2 e.
          subst hmerge
          rw [pairOuterReadSnd]
          by_cases h1 : e.1.1 ∈ R
          · -- e.1.1 ∈ R; boundary ⇒ e.1.2 ∉ R.
            have h2 : e.1.2 ∉ R := by
              rcases hb with ⟨_, hr⟩ | ⟨hl, _⟩
              · exact hr
              · exact absurd h1 hl
            simp only [dif_pos h1, pairOuter, edgeRightIncident, if_neg h2]
          · -- e.1.1 ∉ R; boundary ⇒ e.1.2 ∈ R, so the left endpoint is the complement side.
            simp only [dif_neg h1, pairOuter, edgeLeftIncident, if_neg h1]
        · rw [dif_neg hb]
          by_cases hinc : IsRegionIncidentEdge (G := G) R e
          · rw [dif_pos hinc, if_pos hinc]
          · rw [dif_neg hinc]
            -- e not incident: pairOuterReadSnd ξ e = p.2 e.
            subst hmerge
            rw [pairOuterReadSnd]
            have h1 : e.1.1 ∉ R := fun h => hinc (Or.inl h)
            simp only [dif_neg h1, pairOuter, edgeLeftIncident, if_neg h1]
    · -- Reading the fiber legs of a reconstruction recovers them.
      intro h _
      funext e
      simp only [regionFiberLegs, pairOuterFiberPair]
      have hb : ¬ IsRegionBoundaryEdge (G := G) R e.1 := e.2
      by_cases hinc : IsRegionIncidentEdge (G := G) R e.1
      · -- R-incident non-boundary edge: legs read the second component, which is `h e`.
        rw [if_pos hinc, dif_neg hb, dif_pos hinc]
      · -- non-incident edge: legs read the first component, which is `h e`.
        rw [if_neg hinc, dif_neg hinc]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [regionInteriorBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e))
        (fun e => by simp [Finset.mem_filter]) (fun e => B.bondDim e)]

open scoped Classical in
/-- **The `pairOuter` fiber collapse.** Summing a function of `pairOuter p` over the agreeing-
off-`f` pairs equals the bond-dimension product over the non-boundary edges times the sum over
configurations consistent off `f`. Each fiber of `pairOuter` over a consistent-off-`f`
configuration has `regionInteriorBondProd B R` agreeing pairs (the free non-boundary legs);
no agreeing pair lies over an inconsistent-off-`f` configuration. -/
theorem sum_pairOuter_fiber_collapse (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (g : OpenLocalConfig (G := G) B → ℂ) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
      g (pairOuter (G := G) B R p)) =
      regionInteriorBondProd (G := G) B R •
        ∑ ξ ∈ Finset.univ.filter (fun ξ : OpenLocalConfig (G := G) B =>
            IsConsistentOff (G := G) B f.1 ξ),
          g ξ := by
  classical
  -- Group the agreeing pairs by their `pairOuter` value.
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p => pairOuter (G := G) B R p)
    (t := Finset.univ.filter (fun ξ : OpenLocalConfig (G := G) B =>
      IsConsistentOff (G := G) B f.1 ξ))
    (f := fun p => g (pairOuter (G := G) B R p))
    (s := Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1)) ?_]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    rw [Finset.mem_filter] at hξ
    -- On each fiber the summand is constant `g ξ`, with the bond product as count.
    rw [Finset.filter_filter,
      Finset.sum_congr rfl (g := fun _ => g ξ)
        (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
      Finset.sum_const]
    rw [show (Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          (∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
              p.1 c.1 = p.2 c.1)
            ∧ pairOuter (G := G) B R p = ξ)).card =
        regionInteriorBondProd (G := G) B R from
      pairOuterFiber_card (G := G) B R f ξ hξ.2]
  · -- Every agreeing pair's `pairOuter` is consistent off `f`.
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, pairOuter_isConsistentOff (G := G) B R f p hp.2⟩

/-- The orientation matrix sending the region-side/complement-side reading of a boundary edge
to its left/right reading: the identity when the left endpoint of `f` lies in `R`, the
transpose otherwise. -/
noncomputable def regionEdgeOrient (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then N else Nᵀ

open scoped Classical in
/-- **Region-to-edge identity.** The region-inserted coefficient on a boundary edge `f` of `R`
equals the bond-dimension product over the non-boundary edges times the edge-inserted
coefficient at `f` of the assembled physical configuration, with the inserted matrix oriented
by `regionEdgeOrient` (identity when `f`'s left endpoint lies in `R`, transpose otherwise).

The region/complement contraction overcounts the single-bond cut at `f` by the free non-boundary
legs (`sum_pairOuter_fiber_collapse`); the cut form is `edgeInsertedCoeff` read through
`edgeInsertedCoeff_eq_sum_local`, whose consistency deltas restrict to the configurations
consistent off `f`. -/
theorem regionInsertedCoeff_eq_smul_edgeInsertedCoeff (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) B R f N σ τ =
      regionInteriorBondProd (G := G) B R •
        edgeInsertedCoeff (G := G) B f.1 (assembleRegionσ (V := V) (d := d) R σ τ)
          (regionEdgeOrient (G := G) B R f N) := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum_vertex B R f N σ τ]
  -- Recognise the summand as `g (pairOuter p)` and collapse the fiber.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
      N (p.1 f.1) (p.2 f.1) *
        ∏ v : V, B.component v (pairOuter (G := G) B R p v)
          (assembleRegionσ (V := V) (d := d) R σ τ v)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig B × VirtualConfig B =>
          ∀ c : {c : Edge G // IsRegionBoundaryEdge (G := G) R c}, c ≠ f →
            p.1 c.1 = p.2 c.1),
        (fun ξ : OpenLocalConfig (G := G) B =>
          N (pairOuterReadFst (G := G) B R ξ f.1) (pairOuterReadSnd (G := G) B R ξ f.1) *
            ∏ v : V, B.component v (ξ v)
              (assembleRegionσ (V := V) (d := d) R σ τ v)) (pairOuter (G := G) B R p) from ?_]
  · rw [sum_pairOuter_fiber_collapse B R f (fun ξ : OpenLocalConfig (G := G) B =>
        N (pairOuterReadFst (G := G) B R ξ f.1) (pairOuterReadSnd (G := G) B R ξ f.1) *
          ∏ v : V, B.component v (ξ v)
            (assembleRegionσ (V := V) (d := d) R σ τ v))]
    congr 1
    -- The consistent-off-`f` sum is the edge-inserted coefficient (deltas collapse).
    rw [edgeInsertedCoeff_eq_sum_local B f.1 (assembleRegionσ (V := V) (d := d) R σ τ)
      (regionEdgeOrient (G := G) B R f N)]
    -- Restrict to consistent-off-`f` configs on both sides and match summands.
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (OpenLocalConfig (G := G) B))
      (fun ξ => IsConsistentOff (G := G) B f.1 ξ)]
    rw [show (∑ ξ ∈ Finset.univ.filter (fun ξ : OpenLocalConfig (G := G) B =>
          ¬ IsConsistentOff (G := G) B f.1 ξ),
        (∏ c : {c : Edge G // c ≠ f.1},
          if ξ c.1.1.1 (edgeLeftIncident (G := G) c.1) =
              ξ c.1.1.2 (edgeRightIncident (G := G) c.1) then (1 : ℂ) else 0) *
          (regionEdgeOrient (G := G) B R f N)
            (ξ f.1.1.1 (edgeLeftIncident (G := G) f.1))
            (ξ f.1.1.2 (edgeRightIncident (G := G) f.1)) *
          ∏ v : V, B.component v (ξ v) (assembleRegionσ (V := V) (d := d) R σ τ v)) = 0 from ?_,
      add_zero]
    · -- On consistent-off-`f` configs the deltas are 1 and the orientation matches.
      refine Finset.sum_congr rfl (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      rw [prod_off_delta_eq, if_pos hξ.2, one_mul]
      congr 1
      -- `N (readFst)(readSnd) = orient (ξ@L)(ξ@R)`.
      rw [regionEdgeOrient, pairOuterReadFst, pairOuterReadSnd]
      by_cases h1 : f.1.1.1 ∈ R
      · simp only [dif_pos h1, if_pos h1]
      · simp only [dif_neg h1, if_neg h1, Matrix.transpose_apply]
    · -- Inconsistent-off-`f` configs contribute zero.
      refine Finset.sum_eq_zero (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      rw [prod_off_delta_eq, if_neg hξ.2, zero_mul, zero_mul]
  · -- The summand rewrite: `N (p.1 f)(p.2 f) = N (readFst (pairOuter p))(readSnd (pairOuter p))`.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hcons := pairOuter_isConsistentOff (G := G) B R f p hp.2
    simp only
    congr 2
    · -- `pairOuterReadFst (pairOuter p) f = p.1 f`.
      rw [pairOuterReadFst, pairOuter, pairOuter]
      by_cases h1 : f.1.1.1 ∈ R
      · simp only [dif_pos h1, edgeLeftIncident, if_pos h1]
      · -- f.1.1 ∉ R, boundary ⇒ f.1.2 ∈ R; readFst reads the right (in-region) endpoint = p.1 f.
        have h2 : f.1.1.2 ∈ R := by
          rcases f.2 with ⟨hl, _⟩ | ⟨_, hr⟩
          · exact absurd hl h1
          · exact hr
        simp only [dif_neg h1, edgeRightIncident, if_pos h2]
    · -- `pairOuterReadSnd (pairOuter p) f = p.2 f`.
      rw [pairOuterReadSnd, pairOuter, pairOuter]
      by_cases h1 : f.1.1.1 ∈ R
      · -- f.1.1 ∈ R, boundary ⇒ f.1.2 ∉ R; readSnd reads the right (complement) endpoint = p.2 f.
        have h2 : f.1.1.2 ∉ R := by
          rcases f.2 with ⟨_, hr⟩ | ⟨hl, _⟩
          · exact hr
          · exact absurd h1 hl
        simp only [dif_pos h1, edgeRightIncident, if_neg h2]
      · simp only [dif_neg h1, edgeLeftIncident, if_neg h1]

/-- `regionEdgeOrient` does not depend on the tensor's components, only on the region and the
boundary edge. -/
theorem regionEdgeOrient_applyGauge (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    regionEdgeOrient (G := G) (applyGauge B Z) R f N = regionEdgeOrient (G := G) B R f N := rfl

omit [Fintype V] in
/-- `regionEdgeOrient` is an involution. -/
theorem regionEdgeOrient_regionEdgeOrient (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    regionEdgeOrient (G := G) B R f (regionEdgeOrient (G := G) B R f N) = N := by
  rw [regionEdgeOrient, regionEdgeOrient]
  by_cases h1 : f.1.1.1 ∈ R
  · simp only [if_pos h1]
  · simp only [if_neg h1, Matrix.transpose_transpose]

/-- **The edgewise region gauge-absorption equality.** Applying an oriented edge-gauge family `Z`
to a PEPS tensor and inserting `M` on a boundary edge `f` of `R` equals inserting, on the
ungauged tensor, the matrix obtained by orienting `M` to the edge convention, conjugating by the
open-edge gauge transpose, and orienting back: every interior edge and every boundary edge other
than `f` cancels its gauge pairwise, while the two endpoint gauges on `f` conjugate the inserted
matrix.

This is the region-granularity port of `edgeInsertedCoeff_applyGauge`.  The proof factors through
the region-to-edge identity `regionInsertedCoeff_eq_smul_edgeInsertedCoeff`: the region/complement
contraction is the single-bond cut at `f` (up to the non-boundary multiplicity, which is
gauge-invariant), so the edge-granularity cancellation applies and is transported back.  The
`regionEdgeOrient` records the boundary-edge orientation: the conjugation is by `(Z_f)ᵀ`
exactly as at the edge level when `f`'s left endpoint lies in `R`, and by the transpose-orientation
of that conjugation otherwise. -/
theorem regionInsertedCoeff_applyGauge (B : Tensor G d) (R : Finset V)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) (applyGauge B Z) R f M σ τ =
      regionInsertedCoeff (G := G) B R f
        (regionEdgeOrient (G := G) B R f
          ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ *
            regionEdgeOrient (G := G) B R f M *
            ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)⁻¹)ᵀ)) σ τ := by
  classical
  -- Apply the region-to-edge identity on the gauged tensor.
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff (applyGauge B Z) R f M σ τ]
  rw [regionEdgeOrient_applyGauge B R Z f M]
  -- Cancel the gauge at the edge granularity.
  rw [edgeInsertedCoeff_applyGauge B Z f.1 (assembleRegionσ (V := V) (d := d) R σ τ)
    (regionEdgeOrient (G := G) B R f M)]
  -- Transport back through the region-to-edge identity on `B`.
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff B R f
    (regionEdgeOrient (G := G) B R f
      ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ *
        regionEdgeOrient (G := G) B R f M *
        ((Z f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)⁻¹)ᵀ)) σ τ]
  -- The bond-dimension multiplicities agree; the oriented matrix is an involution.
  rw [regionEdgeOrient_regionEdgeOrient B R f]
  -- `regionInteriorBondProd (applyGauge B Z) R = regionInteriorBondProd B R` definitionally.
  rfl

end PEPS
end TNLean
