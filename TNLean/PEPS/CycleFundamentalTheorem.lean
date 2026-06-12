import TNLean.PEPS.CycleBlockingData
import TNLean.PEPS.NormalGeneralFundamentalTheorem

/-!
# The Fundamental Theorem for normal MPS on a closed chain

This file specializes the Fundamental Theorem for normal PEPS on a connected
graph (`fundamentalTheorem_normalPEPS`) to the cycle graph, obtaining the
first corollary after the theorem labelled `normal` of arXiv:1804.04964
(Section 3, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`): two
normal MPS `{A_i}` and `{B_i}` on a closed chain of `n ≥ 3L` sites, each with
the property that blocking any `L` consecutive sites gives an injective
tensor, generating the same state, are related by invertible matrices `Z_i`
(one per bond, `n + 1 ≡ 1`) with `B_i = Z_i⁻¹ A_i Z_{i+1}`; and the `Z_i` are
unique up to a multiplicative constant.

A site-dependent MPS on a closed chain of `n` sites is a PEPS on the cycle
graph over `Fin n`: each vertex carries one tensor with two virtual legs (the
two incident bonds) and the closed-chain state coefficient is the cyclic
trace of the matrix product.  The corollary's per-bond gauges `Z_i` are the
per-edge gauges of the graph-level gauge equivalence, and its blocks of `L`
consecutive sites are the arcs of `TNLean/PEPS/CycleArcRegion.lean`.

The hypotheses beyond the source's wording carry over from the general
theorem and are documented there and in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`: positive physical and
bond dimensions are the counterexample-backed faithfulness fixes of the
injective Fundamental Theorem, and `0 < L` makes "blocking `L` consecutive
sites" a blocking at all.  Connectivity holds on the cycle and is discharged,
not assumed.

## Relation to the matrix-product-state chapters

The development's MPS chapters (`TNLean/MPS/`) treat one site-independent
tensor (`MPSTensor`) generating the closed-chain states of *all* lengths at
once: their equality (`SameMPV`) quantifies over every chain length, and
their Fundamental Theorem (from arXiv:1606.00608) produces one global
similarity.  The present corollary is a different statement, at a *fixed*
chain length `n` with site-dependent tensors and one gauge per bond, and is
obtained from the PEPS theorem rather than from the transfer-matrix route of
the MPS chapters.  A dictionary between site-independent `MPSTensor` families
and cycle-graph tensors would let the fixed-length statement be compared with
the all-lengths one; it is not part of this file.  The source's second
corollary (the translation-invariant form with a single gauge `Z` and a root
of unity `λ`, lines 1624--1661) is likewise not delivered here: the
development's translation-invariant setting is the torus
(`fundamentalTheorem_normalTorusPEPS_unconditional`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, first corollary after the theorem labelled `normal`, lines
  1585--1622 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace TNLean
namespace PEPS

/-! ### Union closure for the shared predicate -/

/-- Union closure for the conjunction of two region-injectivity predicates,
from union closure of each.

Source: arXiv:1804.04964, Section 3, Lemma labelled `injective_union`, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`, applied to each of the
two tensors over the shared regions. -/
theorem regionInjectivityUnionClosure_pair {V : Type*} [DecidableEq V]
    {κ κ' : RegionInjectivityData V}
    (h : RegionInjectivityUnionClosure κ) (h' : RegionInjectivityUnionClosure κ') :
    RegionInjectivityUnionClosure (regionInjectivityDataPair κ κ') where
  union_injective hA hB :=
    ⟨h.union_injective hA.1 hB.1, h'.union_injective hA.2 hB.2⟩

/-! ### The corollary for normal MPS on a closed chain -/

/-- **Fundamental Theorem for normal MPS on a closed chain**
(arXiv:1804.04964, Section 3, first corollary after the theorem labelled
`normal`).

Two MPS on the closed chain of `n ≥ 3L` sites — tensors on the cycle graph
over `Fin n` — such that blocking any `L` consecutive sites gives an
injective tensor for each, generating the same state, are gauge equivalent:
there is an invertible matrix on every bond relating the defining tensors,
which is the source's family `Z_i` (for `i = 1, …, n`, `n + 1 ≡ 1`) with
`B_i = Z_i⁻¹ A_i Z_{i+1}`.

The blocking hypotheses of the general theorem are discharged by the arc
geometry: around every edge the chain splits into the `L` sites on one side,
the `L` sites on the other, and the remaining `n - 2L ≥ L` sites, all
injective (longer blocks by the source's union lemma); at every site the
`L + 1` sites starting there and the `L` sites starting at its successor
are injective with injective complements and differ exactly at the site; and
the only nearest-neighbour pair joining the two blocks around an edge is the
edge itself.  Connectivity of the cycle discharges the connectivity
hypothesis.  The bond dimensions are not assumed equal: the general theorem
forces them.

The hypotheses `0 < d` and the positive bond dimensions are the
counterexample-backed faithfulness fixes inherited from the injective
Fundamental Theorem (`docs/paper-gaps/peps_injective_ft_section3_route.tex`,
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`); `0 < L` is
implicit in the source's blocking of `L` consecutive sites.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalMPS_cycle {n L d : ℕ}
    (hL : 0 < L) (hn : 3 * L ≤ n)
    (A B : Tensor (SimpleGraph.cycleGraph n) d)
    (harcA : ∀ s : Fin n,
      RegionBlockedTensorInjective (G := SimpleGraph.cycleGraph n) A (cycleArcFrom s L))
    (harcB : ∀ s : Fin n,
      RegionBlockedTensorInjective (G := SimpleGraph.cycleGraph n) B (cycleArcFrom s L))
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (SimpleGraph.cycleGraph n), 0 < B.bondDim g) :
    GaugeEquiv A B := by
  haveI : NeZero n := ⟨by omega⟩
  have hU := regionInjectivityUnionClosure_pair
    (regionInjectivityUnionClosure_of_overlap A hposA)
    (regionInjectivityUnionClosure_of_overlap B hposB)
  have harc : NormalCycleArcInjectivityHypotheses L
      (regionInjectivityDataPair (regionInjectivityDataOf (G := SimpleGraph.cycleGraph n) A)
        (regionInjectivityDataOf (G := SimpleGraph.cycleGraph n) B)) :=
    ⟨fun s => ⟨harcA s, harcB s⟩⟩
  have hconn : (SimpleGraph.cycleGraph n).Connected := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact SimpleGraph.cycleGraph_connected
  exact fundamentalTheorem_normalPEPS A B
    (cycleNormalPEPSBlockingHypotheses harc hU hL hn)
    (fun e g => isCrossingEdge_cycleEdge_iff A hL hn e g) hAB hd hposA hposB hconn

/-- **Uniqueness clause of the Fundamental Theorem for normal MPS on a closed
chain** (arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`: the gauges `Z_i` are unique up to a multiplicative
constant).

Two per-bond gauge families each realizing the scalar-free gauge relation of
`fundamentalTheorem_normalMPS_cycle` are proportional at every bond.  This is
the general uniqueness clause instantiated on the cycle blocking.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalMPS_cycle_gauge_unique {n L d : ℕ}
    (hL : 0 < L) (hn : 3 * L ≤ n)
    (A B : Tensor (SimpleGraph.cycleGraph n) d)
    (harcA : ∀ s : Fin n,
      RegionBlockedTensorInjective (G := SimpleGraph.cycleGraph n) A (cycleArcFrom s L))
    (harcB : ∀ s : Fin n,
      RegionBlockedTensorInjective (G := SimpleGraph.cycleGraph n) B (cycleArcFrom s L))
    (hbond : A.bondDim = B.bondDim)
    (hposA : ∀ g : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (SimpleGraph.cycleGraph n), 0 < B.bondDim g)
    (X X' : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (v : Fin n)
      (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ =
        gaugeVertex A X v η σ)
    (hX' : ∀ (v : Fin n)
      (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ =
        gaugeVertex A X' v η σ)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    ∃ c : ℂˣ, (X' e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
      (c : ℂ) • (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
  haveI : NeZero n := ⟨by omega⟩
  have hU := regionInjectivityUnionClosure_pair
    (regionInjectivityUnionClosure_of_overlap A hposA)
    (regionInjectivityUnionClosure_of_overlap B hposB)
  have harc : NormalCycleArcInjectivityHypotheses L
      (regionInjectivityDataPair (regionInjectivityDataOf (G := SimpleGraph.cycleGraph n) A)
        (regionInjectivityDataOf (G := SimpleGraph.cycleGraph n) B)) :=
    ⟨fun s => ⟨harcA s, harcB s⟩⟩
  exact fundamentalTheorem_normalPEPS_gauge_unique A B
    (cycleNormalPEPSBlockingHypotheses harc hU hL hn) hbond hposA X X' hX hX' e

end PEPS
end TNLean
