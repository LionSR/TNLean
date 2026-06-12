import TNLean.PEPS.NormalAbsorbedFamily
import TNLean.PEPS.RegionBlock.ScalarExtraction
import TNLean.PEPS.RegionBlock.ReindexInjectivity
import TNLean.PEPS.RegionBlock.GaugeInjectivity2
import TNLean.PEPS.FundamentalTheorem

/-!
# The per-vertex scalar of the general normal PEPS comparison

This file performs the one-site comparison of the general normal PEPS theorem
(arXiv:1804.04964, Section 3, theorem labelled `normal`, lines 1576--1583 of
`Papers/1804.04964/paper_normal.tex`) on an arbitrary connected finite simple
graph: at every vertex `v`, the two one-site-different injective regions of the
blocking hypotheses, compared against the gauge-absorbed second tensor through
the bare-edge absorbed equality, produce a nonzero scalar `λ_v` with

> `A_v = λ_v · (gauge action of B at v)`.

The comparison pair is `R = withoutSite v` and `insert v R = withSite v`; each
member yields a region-block scalar proportionality
(`twoBlockProportional_of_edgeAbsorbed`), and the inserted-site scalar
extraction (`component_eq_gaugeVertex_of_twoBlockProportional`) divides the two
proportionality scalars into `λ_v`.

The hypothesis bundle allows two degenerate comparison regions on which the
boundary-edge engine cannot run, because they have no boundary edges: the empty
region (the site's region pair is `(∅, {v})`) and the full vertex set (the pair
is `(V \ {v}, V)`).  At most one member of a pair is degenerate, and on the
degenerate member the proportionality holds directly with scalar `1`: the
empty-region block of any tensor is the constant counting the global virtual
configurations, and the full-region block is the closed state coefficient,
where `SameState` applies.  All other regions have a boundary edge by
connectivity (`nonempty_regionBoundaryEdge_of_connected`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, theorem labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The two degenerate comparison regions

The empty region and the full vertex set have no boundary edges, so their
blocked tensors are a counting constant and the closed state coefficient
respectively; in both cases the comparison proportionality holds with
scalar `1`. -/

/-- The blocked weight of the empty region is the number of global virtual
configurations: there are no boundary edges, no vertices, and every global
virtual configuration contributes the empty product.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex` (the degenerate end of the one-site
comparison pair). -/
theorem regionBlockedWeight_empty (A : Tensor G d)
    (μ : RegionBoundaryConfig (G := G) A (∅ : Finset V))
    (τ : RegionPhysicalConfig (V := V) (d := d) (∅ : Finset V)) :
    regionBlockedWeight (G := G) A ∅ μ τ = (Fintype.card (VirtualConfig A) : ℂ) := by
  classical
  haveI hbdry : IsEmpty {f : Edge G // IsRegionBoundaryEdge (G := G) (∅ : Finset V) f} := by
    refine ⟨fun f => ?_⟩
    rcases f.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 (Finset.notMem_empty _)
    · exact absurd h2 (Finset.notMem_empty _)
  haveI hvert : IsEmpty {w : V // w ∈ (∅ : Finset V)} :=
    ⟨fun w => absurd w.2 (Finset.notMem_empty _)⟩
  unfold regionBlockedWeight
  have hfilter : (Finset.univ.filter
      (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A ∅ ζ = μ)) =
        Finset.univ :=
    Finset.filter_true_of_mem (fun ζ _ => funext fun f => hbdry.elim f)
  rw [hfilter, Finset.sum_congr rfl (fun ζ _ => Finset.prod_of_isEmpty _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The blocked weight of the full vertex set is the closed state coefficient:
there are no boundary edges, and the vertex product runs over all vertices.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex` (the degenerate end of the one-site
comparison pair). -/
theorem regionBlockedWeight_univ (A : Tensor G d)
    (μ : RegionBoundaryConfig (G := G) A (Finset.univ : Finset V))
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ : Finset V)) :
    regionBlockedWeight (G := G) A Finset.univ μ τ =
      stateCoeff A (fun v => τ ⟨v, Finset.mem_univ v⟩) := by
  classical
  haveI hbdry :
      IsEmpty {f : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ : Finset V) f} := by
    refine ⟨fun f => ?_⟩
    rcases f.2 with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 (Finset.mem_univ _)
    · exact h1 (Finset.mem_univ _)
  unfold regionBlockedWeight stateCoeff
  have hfilter : (Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A Finset.univ ζ = μ)) = Finset.univ :=
    Finset.filter_true_of_mem (fun ζ _ => funext fun f => hbdry.elim f)
  rw [hfilter]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  exact Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun v => Finset.mem_univ v))
    _ _ (fun w => rfl)

/-- **The empty-region comparison proportionality.**  Over the empty region the
blocked tensors of `A` and of any reindexed tensor with `A`'s bond dimensions
are both the counting constant of the global virtual configurations, so they
are proportional with scalar `1`.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex` (the comparison pair at a
site whose smaller region is empty). -/
theorem twoBlockScalarProportional_one_of_empty (A C : Tensor G d)
    (hbd : A.bondDim = C.bondDim) :
    TwoBlockScalarProportional (regionTwoBlock (G := G) A (∅ : Finset V))
      (regionTwoBlock (G := G) (reindexTensor (G := G) C hbd) (∅ : Finset V)) 1 := by
  intro η μ σ
  rw [regionTwoBlock_apply, regionTwoBlock_apply, one_mul,
    regionBlockedWeight_empty, regionBlockedWeight_empty]
  rfl

/-- **The full-region comparison proportionality.**  Over the full vertex set
the blocked tensor of `A` is the closed state coefficient and the blocked
tensor of the reindexed gauge-absorbed second tensor is the second state's
coefficient, so `SameState` gives the proportionality with scalar `1`.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex` (the comparison pair at a
site whose larger region is the full lattice). -/
theorem twoBlockScalarProportional_one_of_univ (A B : Tensor G d)
    (hbond : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (hAB : SameState A B) :
    TwoBlockScalarProportional
      (regionTwoBlock (G := G) A (Finset.univ : Finset V))
      (regionTwoBlock (G := G) (reindexTensor (G := G) (applyGauge B X) hbond)
        (Finset.univ : Finset V)) 1 := by
  intro η μ τ
  rw [regionTwoBlock_apply, regionTwoBlock_apply, one_mul,
    regionBlockedWeight_univ, regionBlockedWeight_univ,
    stateCoeff_reindexTensor (applyGauge B X) hbond, applyGauge_stateCoeff]
  exact hAB _

/-! ### The per-vertex scalar from the one-site comparison -/

open scoped Classical in
/-- **The per-vertex scalar of the general normal comparison.**

Under the general normal PEPS blocking hypotheses over the pair predicate on a
connected graph, with matched bond dimensions, the same state, positive bonds
for the first tensor, and a gauge family `X` realizing the bare-edge absorbed
equality at every edge, every vertex `v` carries a nonzero scalar `λ_v` with
`A_v = λ_v · (gauge action of B at v)` on every local virtual configuration and
physical index.

The comparison pair at `v` is `withoutSite v` and
`withSite v = insert v (withoutSite v)`; each member yields a region-block
proportionality — through the boundary-edge engine when it has a boundary edge,
and with scalar `1` directly on the degenerate members (the empty region and
the full vertex set) — and the inserted-site scalar extraction gives
`λ_v = c_S / c_R`.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583, via the proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_normalPerVertexScalar
    (A B : Tensor G d)
    (h : NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G)
    (hconn : G.Connected)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hedge : ∀ (e : Edge G) (σ : V → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (v : V) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        A.component v η σ =
          lam * gaugeVertex B X v
            (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ := by
  classical
  have hvR : v ∉ h.oneSiteSeparation.withoutSite v :=
    h.oneSiteSeparation.site_notMem_withoutSite v
  have hSins : h.oneSiteSeparation.withSite v =
      insert v (h.oneSiteSeparation.withoutSite v) :=
    h.oneSiteSeparation.withSite_eq_insert v
  -- Blocked-tensor injectivity of the comparison pair for `A`.
  have hRA : RegionBlockedTensorInjective (G := G) A
      (h.oneSiteSeparation.withoutSite v) := by
    have hi := (h.oneSiteSeparation.withoutSite_injective v).1
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCA : RegionBlockedTensorInjective (G := G) A
      (Finset.univ \ h.oneSiteSeparation.withoutSite v) := by
    have hi := (h.oneSiteSeparation.withoutSite_complement_injective v).1
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hSA : RegionBlockedTensorInjective (G := G) A
      (insert v (h.oneSiteSeparation.withoutSite v)) := by
    have hi := (h.oneSiteSeparation.withSite_injective v).1
    rw [regionInjectivityDataOf_isInjective] at hi
    rwa [hSins] at hi
  have hCSA : RegionBlockedTensorInjective (G := G) A
      (Finset.univ \ insert v (h.oneSiteSeparation.withoutSite v)) := by
    have hi := (h.oneSiteSeparation.withSite_complement_injective v).1
    rw [regionInjectivityDataOf_isInjective] at hi
    rwa [hSins] at hi
  -- Blocked-tensor injectivity of the comparison pair for the reindexed
  -- gauge-absorbed second tensor.
  have hgauge : ∀ R : Finset V, RegionBlockedTensorInjective (G := G) B R →
      RegionBlockedTensorInjective (G := G)
        (reindexTensor (G := G) (applyGauge B X) hbond) R :=
    fun R hi => regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond R
      (regionBlockedTensorInjective_applyGauge B X R hi)
  have hRC : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbond)
      (h.oneSiteSeparation.withoutSite v) := by
    refine hgauge _ ?_
    have hi := (h.oneSiteSeparation.withoutSite_injective v).2
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCC : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbond)
      (Finset.univ \ h.oneSiteSeparation.withoutSite v) := by
    refine hgauge _ ?_
    have hi := (h.oneSiteSeparation.withoutSite_complement_injective v).2
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hSC : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbond)
      (insert v (h.oneSiteSeparation.withoutSite v)) := by
    refine hgauge _ ?_
    have hi := (h.oneSiteSeparation.withSite_injective v).2
    rw [regionInjectivityDataOf_isInjective] at hi
    rwa [hSins] at hi
  have hCSC : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbond)
      (Finset.univ \ insert v (h.oneSiteSeparation.withoutSite v)) := by
    refine hgauge _ ?_
    have hi := (h.oneSiteSeparation.withSite_complement_injective v).2
    rw [regionInjectivityDataOf_isInjective] at hi
    rwa [hSins] at hi
  -- The proportionality over the comparison region.
  have hpropR : ∃ cR : ℂ, cR ≠ 0 ∧
      TwoBlockScalarProportional.{_, _, 0, _}
        (regionTwoBlock (G := G) A (h.oneSiteSeparation.withoutSite v))
        (regionTwoBlock (G := G)
          (reindexTensor (G := G) (applyGauge B X) hbond)
          (h.oneSiteSeparation.withoutSite v)) cR := by
    by_cases hRempty : h.oneSiteSeparation.withoutSite v = ∅
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [hRempty]
      exact twoBlockScalarProportional_one_of_empty A (applyGauge B X) hbond
    · have hRtop : h.oneSiteSeparation.withoutSite v ≠ Finset.univ := fun htop =>
        hvR (htop ▸ Finset.mem_univ v)
      haveI := nonempty_regionBoundaryEdge_of_connected hconn
        (Finset.nonempty_iff_ne_empty.mpr hRempty) hRtop
      exact twoBlockProportional_of_edgeAbsorbed A B hbond X
        (h.oneSiteSeparation.withoutSite v) hRA hCA hRC hCC hedge
  -- The proportionality over the one-site completion.
  have hpropS : ∃ cS : ℂ, cS ≠ 0 ∧
      TwoBlockScalarProportional.{_, _, 0, _}
        (regionTwoBlock (G := G) A
          (insert v (h.oneSiteSeparation.withoutSite v)))
        (regionTwoBlock (G := G)
          (reindexTensor (G := G) (applyGauge B X) hbond)
          (insert v (h.oneSiteSeparation.withoutSite v))) cS := by
    by_cases hStop : insert v (h.oneSiteSeparation.withoutSite v) = Finset.univ
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [hStop]
      exact twoBlockScalarProportional_one_of_univ A B hbond X hAB
    · have hSne : (insert v (h.oneSiteSeparation.withoutSite v)).Nonempty :=
        ⟨v, Finset.mem_insert_self v _⟩
      haveI := nonempty_regionBoundaryEdge_of_connected hconn hSne hStop
      exact twoBlockProportional_of_edgeAbsorbed A B hbond X
        (insert v (h.oneSiteSeparation.withoutSite v)) hSA hCSA hSC hCSC hedge
  obtain ⟨cR, hcR0, hcRprop⟩ := hpropR
  obtain ⟨cS, hcS0, hcSprop⟩ := hpropS
  exact ⟨cS / cR, div_ne_zero hcS0 hcR0,
    component_eq_gaugeVertex_of_twoBlockProportional A B
      (h.oneSiteSeparation.withoutSite v) hvR hbond X cR cS hcR0 hposA
      hRC hcRprop hcSprop⟩

end PEPS
end TNLean
