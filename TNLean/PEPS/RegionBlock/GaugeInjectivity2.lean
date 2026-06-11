import TNLean.PEPS.RegionBlock.GaugeInjectivity

/-!
# A gauge preserves blocked-region linear independence

This file completes the gauge-absorbed blocked-region injectivity needed by the final
comparison of the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, proof of
Theorem 3, lines 1519--1571 of `Papers/1804.04964/paper_normal.tex`).

From the global-configuration form of the gauged blocked-region weight
(`regionBlockedWeight_applyGauge_eq_globalSum`), the blocked tensor of `applyGauge B X` over a
region `R` is the blocked tensor of `B` mixed by the boundary coupling matrix, the product over
the boundary edges of the surviving boundary gauges (`regionBlockedWeight_applyGauge`).  The
coupling matrix is invertible — its inverse is the product of the per-edge inverse gauges
(`sum_regionBoundaryCoupling_mul_inv`) — so linear independence transfers
(`linearIndependent_sum_smul`), giving the main result
`regionBlockedTensorInjective_applyGauge`: a gauge preserves blocked-region linear
independence.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The boundary coupling factorization -/

open scoped Classical in
/-- A boundary-fibered double sum collapses to a single sum reading the boundary label:
summing first over a boundary configuration `μ`, then over the global configurations whose
region boundary label is `μ`, is the same as summing over all global configurations and
reading the boundary label off each one. -/
private theorem sum_regionBoundary_fiber (B : Tensor G d) (R : Finset V)
    (F : RegionBoundaryConfig (G := G) B R → VirtualConfig B → ℂ) :
    (∑ μ : RegionBoundaryConfig (G := G) B R,
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = μ),
        F μ ζ) =
      ∑ ζ : VirtualConfig B, F (regionBoundaryLabel (G := G) B R ζ) ζ := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) B R ζ)]
  · rw [if_pos rfl]
  · intro μ _ hμ
    rw [if_neg (fun h => hμ h.symm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

open scoped Classical in
/-- **Gauge factorization of the blocked-region weight.**  The blocked-region weight of
`applyGauge B X` is the blocked-region weight of `B` mixed by the boundary coupling: the
product, over the boundary edges of `R`, of the surviving boundary gauge entries pairing the
outer boundary configuration with the inner one.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_applyGauge (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) B R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) (applyGauge B X) R bdry τ =
      ∑ bdry' : RegionBoundaryConfig (G := G) B R,
        (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          regionBoundaryGauge (G := G) B X R f (bdry f) (bdry' f)) *
          regionBlockedWeight (G := G) B R bdry' τ := by
  classical
  rw [regionBlockedWeight_applyGauge_eq_globalSum (G := G) B X R bdry τ]
  symm
  calc
    (∑ bdry' : RegionBoundaryConfig (G := G) B R,
      (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
        regionBoundaryGauge (G := G) B X R f (bdry f) (bdry' f)) *
        regionBlockedWeight (G := G) B R bdry' τ)
      -- Expand each blocked-region weight as its pinned global sum.
      = ∑ bdry' : RegionBoundaryConfig (G := G) B R,
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry'),
            (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
              regionBoundaryGauge (G := G) B X R f (bdry f)
                (regionBoundaryLabel (G := G) B R ζ f)) *
              ∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => ζ ie.1) (τ w) := by
        refine Finset.sum_congr rfl fun bdry' _ => ?_
        rw [regionBlockedWeight, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [Finset.mem_filter] at hζ
        rw [hζ.2]
    -- Collapse the boundary fiber.
    _ = ∑ ζ : VirtualConfig B,
          (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f)
              (regionBoundaryLabel (G := G) B R ζ f)) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => ζ ie.1) (τ w) :=
        sum_regionBoundary_fiber (G := G) B R _
    -- Read the boundary label off each global configuration.
    _ = ∑ ζ : VirtualConfig B,
          (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f) (ζ f.1)) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => ζ ie.1) (τ w) :=
        Finset.sum_congr rfl fun ζ _ => rfl

/-! ### Invertibility of the boundary coupling

The coupling matrix of the boundary configurations is the tensor product, over the boundary
edges, of the surviving boundary gauges; its inverse is the tensor product of their matrix
inverses.  Contracting the two over a shared boundary configuration gives the per-edge
identity matrices, hence the Kronecker delta of boundary configurations. -/

omit [Fintype V] in
/-- The inverse boundary gauge times the surviving boundary gauge is the identity. -/
theorem regionBoundaryGaugeInv_mul (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryGaugeInv (G := G) B X R f * regionBoundaryGauge (G := G) B X R f = 1 := by
  rw [regionBoundaryGauge, regionBoundaryGaugeInv]
  by_cases h : f.1.1.1 ∈ R
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h, ← Matrix.transpose_mul]
    simp

open scoped Classical in
/-- **The boundary coupling is invertible.**  Contracting the boundary coupling with the
product of the per-edge inverse gauges over a shared boundary configuration gives the
Kronecker delta of boundary configurations.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sum_regionBoundaryCoupling_mul_inv (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (b c : RegionBoundaryConfig (G := G) B R) :
    (∑ b' : RegionBoundaryConfig (G := G) B R,
      (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
        regionBoundaryGauge (G := G) B X R f (b f) (b' f)) *
        ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          regionBoundaryGaugeInv (G := G) B X R f (b' f) (c f)) =
      if b = c then 1 else 0 := by
  classical
  calc
    (∑ b' : RegionBoundaryConfig (G := G) B R,
      (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
        regionBoundaryGauge (G := G) B X R f (b f) (b' f)) *
        ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          regionBoundaryGaugeInv (G := G) B X R f (b' f) (c f))
      -- Merge the two products and exchange the sum with the edge product.
      = ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          ∑ z : Fin (B.bondDim f.1),
            regionBoundaryGauge (G := G) B X R f (b f) z *
              regionBoundaryGaugeInv (G := G) B X R f z (c f) := by
        rw [Finset.sum_congr rfl
          (fun b' _ => (Finset.prod_mul_distrib (s := Finset.univ)
            (f := fun f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
              regionBoundaryGauge (G := G) B X R f (b f) (b' f))
            (g := fun f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} =>
              regionBoundaryGaugeInv (G := G) B X R f (b' f) (c f))).symm)]
        simpa only [Fintype.piFinset_univ] using
          (Finset.prod_univ_sum
            (fun f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f} => Finset.univ)
            (fun f z => regionBoundaryGauge (G := G) B X R f (b f) z *
              regionBoundaryGaugeInv (G := G) B X R f z (c f))).symm
    -- Each boundary edge contracts to the identity matrix entry.
    _ = ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          (if b f = c f then (1 : ℂ) else 0) := by
        refine Finset.prod_congr rfl fun f _ => ?_
        rw [← Matrix.mul_apply, regionBoundaryGauge_mul_inv (G := G) B X R f,
          Matrix.one_apply]
    -- The per-edge deltas multiply to the delta of boundary configurations.
    _ = if b = c then 1 else 0 := by
        rw [Fintype.prod_boole]
        exact if_congr funext_iff.symm rfl rfl

/-! ### Transfer of linear independence -/

/-- Mixing a linearly independent family of vectors by a square matrix with a right inverse
preserves linear independence: a vanishing combination of the mixed family yields, by linear
independence, the vanishing of the mixed coefficients, and contracting with the right inverse
recovers each original coefficient. -/
theorem linearIndependent_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type*} [AddCommGroup W] [Module ℂ W] {v v' : ι → W} {K K' : ι → ι → ℂ}
    (hv : LinearIndependent ℂ v)
    (hKK' : ∀ b c : ι, (∑ b' : ι, K b b' * K' b' c) = if b = c then 1 else 0)
    (hv' : ∀ b : ι, v' b = ∑ b' : ι, K b b' • v b') :
    LinearIndependent ℂ v' := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- The mixed coefficients annihilate the original family.
  have hcoef : ∀ b' : ι, (∑ b : ι, g b * K b b') = 0 := by
    have h0 : (∑ b' : ι, (∑ b : ι, g b * K b b') • v b') = 0 := by
      calc
        (∑ b' : ι, (∑ b : ι, g b * K b b') • v b')
          = ∑ b' : ι, ∑ b : ι, (g b * K b b') • v b' := by
            refine Finset.sum_congr rfl fun b' _ => ?_
            rw [Finset.sum_smul]
        _ = ∑ b : ι, ∑ b' : ι, (g b * K b b') • v b' := Finset.sum_comm
        _ = ∑ b : ι, g b • v' b := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hv' b, Finset.smul_sum]
            refine Finset.sum_congr rfl fun b' _ => ?_
            rw [smul_smul]
        _ = 0 := hg
    exact Fintype.linearIndependent_iff.mp hv _ h0
  -- Contract with the right inverse to recover each coefficient.
  intro b
  calc
    g b = ∑ c : ι, g c * if c = b then 1 else 0 := by
        rw [Finset.sum_congr rfl (fun c _ => by rw [mul_ite, mul_one, mul_zero]),
          Finset.sum_ite_eq' Finset.univ b g, if_pos (Finset.mem_univ b)]
    _ = ∑ c : ι, g c * ∑ b' : ι, K c b' * K' b' b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hKK' c b]
    _ = ∑ c : ι, ∑ b' : ι, g c * (K c b' * K' b' b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ b' : ι, ∑ c : ι, g c * (K c b' * K' b' b) := Finset.sum_comm
    _ = ∑ b' : ι, (∑ c : ι, g c * K c b') * K' b' b := by
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun b' _ => ?_
        rw [hcoef b', zero_mul]

/-! ### The main result -/

/-- **A gauge preserves blocked-region linear independence.**  If the blocked tensor of `B`
over the region `R` is linearly independent in the boundary configuration, then so is the
blocked tensor of `applyGauge B X`: the gauge cancels pairwise on every interior edge of `R`,
and on every boundary edge it acts as an invertible matrix on the open boundary leg, so the
blocked tensor family of `applyGauge B X` is that of `B` mixed by the invertible boundary
coupling.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`: the blocked tensors of the gauge-absorbed second PEPS
$\widetilde B$ over the comparison regions are injective there because the blocked tensors of
`B` are. -/
theorem regionBlockedTensorInjective_applyGauge (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (hB : RegionBlockedTensorInjective (G := G) B R) :
    RegionBlockedTensorInjective (G := G) (applyGauge B X) R := by
  classical
  rw [RegionBlockedTensorInjective] at hB ⊢
  refine linearIndependent_sum_smul (v := regionBlockedTensorFamily (G := G) B R)
    (K := fun b b' => ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
      regionBoundaryGauge (G := G) B X R f (b f) (b' f))
    (K' := fun b b' => ∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
      regionBoundaryGaugeInv (G := G) B X R f (b f) (b' f))
    hB (sum_regionBoundaryCoupling_mul_inv (G := G) B X R) ?_
  intro b
  funext τ
  rw [show regionBlockedTensorFamily (G := G) (applyGauge B X) R b τ =
      regionBlockedWeight (G := G) (applyGauge B X) R b τ from rfl]
  rw [regionBlockedWeight_applyGauge (G := G) B X R b τ, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rfl

end PEPS
end TNLean
