/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Equiv.Fin.Rotate

import TNLean.Algebra.FinCyclicInduction
import TNLean.PEPS.CycleMPSTensor
import TNLean.PEPS.FundamentalTheorem
import TNLean.PEPS.IsoTransport

/-!
# Bond dimensions of a cyclically invariant injective MPS

The Applications-section corollary of arXiv:1804.04964 begins with a
site-dependent injective MPS `A₁, …, Aₙ` on a closed chain.  Translational
invariance identifies its state with the state of the one-site cyclic shift
`A₂, …, Aₙ, A₁`.  The source applies the injective MPS Fundamental Theorem to
these two descriptions and obtains an invertible matrix on every bond; in
particular, adjacent bond dimensions agree (lines 1803--1842 of
`Papers/1804.04964/paper_normal.tex`).

Here a site-dependent chain with possibly different bond dimensions is a
`Tensor (SimpleGraph.cycleGraph n) d`.  The cyclic successor permutation is a
graph automorphism (`cycleRotate`), and transport by its inverse places the
tensor at site `v + 1` at site `v` (`Tensor.cycleShift`).  Vertex injectivity is
preserved by transport, so the graph-level injective Fundamental Theorem
applies to a tensor and its cyclic shift.  Equality of its bond-dimension
functions then gives the source's adjacent-bond equality, and cyclic induction
gives equality of all bond dimensions on the closed chain.

This file establishes only the bond-dimension clause of the source corollary.
It does not construct the repeated tensor `B` from lines 1843--1889.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Applications section, corollary and proof lines 1803--1890 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {n d : ℕ} [NeZero n]

/-! ### The one-site rotation of the cycle -/

/-- The cyclic successor permutation `v ↦ v + 1` as an automorphism of the
cycle graph.

Source: arXiv:1804.04964, Applications section, lines 1815--1827 of
`Papers/1804.04964/paper_normal.tex`, where the second MPS description is the
one-site cyclic translate of the first. -/
def cycleRotate (hn : 3 ≤ n) :
    SimpleGraph.cycleGraph n ≃g SimpleGraph.cycleGraph n := by
  exact
    { toEquiv := finRotate n
      map_rel_iff' := by
        intro u v
        rw [cycleGraph_adj_iff_add_one hn, cycleGraph_adj_iff_add_one hn]
        simp only [finRotate_apply]
        constructor
        · rintro (h | h)
          · exact Or.inl (add_right_cancel h)
          · exact Or.inr (add_right_cancel h)
        · rintro (h | h)
          · exact Or.inl (congrArg (fun x : Fin n => x + 1) h)
          · exact Or.inr (congrArg (fun x : Fin n => x + 1) h) }

/-- The one-site cycle rotation sends site `v` to its cyclic successor.

Source: arXiv:1804.04964, Applications section, lines 1815--1827 of
`Papers/1804.04964/paper_normal.tex`. -/
@[simp] theorem cycleRotate_apply (hn : 3 ≤ n) (v : Fin n) :
    cycleRotate hn v = v + 1 := by
  exact finRotate_apply v

/-- Rotating the cycle carries the bond from `v` to `v + 1` to the next bond,
from `v + 1` to `v + 2`.

Source: arXiv:1804.04964, Applications section, lines 1828--1842 of
`Papers/1804.04964/paper_normal.tex`, where the Fundamental Theorem gauges are
indexed by successive bonds. -/
theorem Edge.map_cycleRotate_cycleSuccEdge (hn : 3 ≤ n) (v : Fin n) :
    Edge.map (cycleRotate hn) (cycleSuccEdge hn v) = cycleSuccEdge hn (v + 1) := by
  symm
  rw [cycleSuccEdge]
  apply Edge.ofAdj_eq_of_endpoints
  have hsource :
      (((cycleSuccEdge hn v).1.1 = v ∧ (cycleSuccEdge hn v).1.2 = v + 1) ∨
        ((cycleSuccEdge hn v).1.1 = v + 1 ∧ (cycleSuccEdge hn v).1.2 = v)) := by
    rw [cycleSuccEdge]
    exact Edge.ofAdj_endpoints (cycleGraph_adj_succ hn v)
  have hmap := Edge.map_endpoints (cycleRotate hn) (cycleSuccEdge hn v)
  rcases hsource with hs | hs <;> rcases hmap with hm | hm
  · exact Or.inl ⟨by rw [hm.1, hs.1, cycleRotate_apply],
      by rw [hm.2, hs.2, cycleRotate_apply]⟩
  · exact Or.inr ⟨by rw [hm.2, hs.1, cycleRotate_apply],
      by rw [hm.1, hs.2, cycleRotate_apply]⟩
  · exact Or.inr ⟨by rw [hm.2, hs.2, cycleRotate_apply],
      by rw [hm.1, hs.1, cycleRotate_apply]⟩
  · exact Or.inl ⟨by rw [hm.1, hs.2, cycleRotate_apply],
      by rw [hm.2, hs.1, cycleRotate_apply]⟩

/-! ### Cyclic shift and state invariance -/

/-- The site-dependent tensor family shifted as in the source,
`A₁, …, Aₙ ↦ A₂, …, Aₙ, A₁`.  Transport is taken along the inverse rotation,
so the transported tensor at site `v` comes from site `v + 1`.

Source: arXiv:1804.04964, Applications section, lines 1815--1827 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def Tensor.cycleShift (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hn : 3 ≤ n) : Tensor (SimpleGraph.cycleGraph n) d :=
  A.transport (cycleRotate hn).symm

/-- The state of a site-dependent closed chain is invariant under the one-site
cyclic shift when it agrees with the state generated by
`A₂, …, Aₙ, A₁`.

Source: arXiv:1804.04964, Applications section, lines 1807--1827 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsCycleShiftInvariantState (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hn : 3 ≤ n) : Prop :=
  SameState A (A.cycleShift hn)

/-! ### Adjacent and cyclewise bond-dimension equality -/

/-- Applying the injective PEPS Fundamental Theorem to a site-dependent closed
chain and its one-site cyclic shift gives the source's family of invertible
bond gauges `Zᵢ`.

Source: arXiv:1804.04964, Applications section, lines 1807--1842 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem gaugeEquiv_cycleShift_of_isCycleShiftInvariantState
    (hn : 3 ≤ n) (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hA : IsVertexInjective A) (hTI : IsCycleShiftInvariantState A hn)
    (hpos : ∀ e : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim e) :
    GaugeEquiv A (A.cycleShift hn) := by
  have hconn : (SimpleGraph.cycleGraph n).Connected :=
    ⟨SimpleGraph.cycleGraph_preconnected⟩
  apply fundamentalTheorem_PEPS A (A.cycleShift hn) hA
      (hA.transport (cycleRotate hn).symm) hTI hpos
  · intro e
    exact hpos (Edge.map (cycleRotate hn) e)
  · exact hconn

/-- Adjacent bonds of a cyclically invariant injective closed-chain MPS have
the same dimension: if `Dᵢ` is the dimension of the bond from site `i` to
site `i + 1`, then `Dᵢ = Dᵢ₊₁`.

This is the first conclusion of the Applications-section corollary.  It is
obtained from the bond-dimension equality in the injective Fundamental Theorem
applied to `A₁, …, Aₙ` and `A₂, …, Aₙ, A₁`.

Source: arXiv:1804.04964, Applications section, corollary line 1804 and proof
lines 1807--1842 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_cycleSuccEdge_add_one_eq_of_isCycleShiftInvariantState
    (hn : 3 ≤ n) (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hA : IsVertexInjective A) (hTI : IsCycleShiftInvariantState A hn)
    (hpos : ∀ e : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim e)
    (v : Fin n) :
    A.bondDim (cycleSuccEdge hn (v + 1)) = A.bondDim (cycleSuccEdge hn v) := by
  obtain ⟨hDim, _, _⟩ :=
    gaugeEquiv_cycleShift_of_isCycleShiftInvariantState hn A hA hTI hpos
  have h := congrFun hDim (cycleSuccEdge hn v)
  rw [Tensor.cycleShift, Tensor.transport_bondDim] at h
  have h' : A.bondDim (cycleSuccEdge hn v) =
      A.bondDim (Edge.map (cycleRotate hn) (cycleSuccEdge hn v)) := by
    simpa only [RelIso.symm_symm] using h
  rw [Edge.map_cycleRotate_cycleSuccEdge] at h'
  exact h'.symm

/-- All bonds of a cyclically invariant injective closed-chain MPS have the
same dimension.

Source: arXiv:1804.04964, Applications section, corollary line 1804 and proof
lines 1807--1842 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_eq_of_isCycleShiftInvariantState
    (hn : 3 ≤ n) (A : Tensor (SimpleGraph.cycleGraph n) d)
    (hA : IsVertexInjective A) (hTI : IsCycleShiftInvariantState A hn)
    (hpos : ∀ e : Edge (SimpleGraph.cycleGraph n), 0 < A.bondDim e)
    (e f : Edge (SimpleGraph.cycleGraph n)) :
    A.bondDim e = A.bondDim f := by
  obtain ⟨u, rfl⟩ := cycleSuccEdge_surjective hn e
  obtain ⟨v, rfl⟩ := cycleSuccEdge_surjective hn f
  have hzero (w : Fin n) :
      A.bondDim (cycleSuccEdge hn w) = A.bondDim (cycleSuccEdge hn 0) :=
    Fin.cyclic_induction
      (P := fun i => A.bondDim (cycleSuccEdge hn i) = A.bondDim (cycleSuccEdge hn 0))
      rfl (fun i hi =>
        (bondDim_cycleSuccEdge_add_one_eq_of_isCycleShiftInvariantState
          hn A hA hTI hpos i).trans hi) w
  exact (hzero u).trans (hzero v).symm

end PEPS
end TNLean
