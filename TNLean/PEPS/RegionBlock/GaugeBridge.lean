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

The file also records the first stage of that gauge-cancellation bridge
(`regionComplProd_gauge_eq`): the region weight of a gauged tensor against the complement
weight of an agreeing pair is one global gauge-vertex product over all vertices, reading the
first configuration on the region and the second on the complement (`pairOuter`), with the
physical legs assembled.  This brings the double-sum form of the gauged region-inserted
coefficient into the single global gauge-vertex product whose `edgeGaugeAt` factors are ready
to cancel edgewise.  The remaining stage of the bridge --- the gauge sum over the agreeing
pair, so that interior edges cancel to consistency deltas while the boundary edge `f`
conjugates the inserted matrix --- is the open obligation recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

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

/-! ### The gauge-cancellation bridge

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

This is the first stage of the region-granularity gauge-cancellation bridge: it brings the
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
so the gauge-cancellation bridge compares them at this single granularity. -/

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

end PEPS
end TNLean
