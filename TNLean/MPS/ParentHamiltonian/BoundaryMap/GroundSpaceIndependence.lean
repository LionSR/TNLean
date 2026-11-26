/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.DFinsupp
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockGroundSpaceOverlap
import QICLean.Analysis.Projection.OverlapMatrix

/-!
# Independence from small subspace overlaps

A finite family of subspaces is independent when a matrix of its pairwise
overlap bounds has norm less than one. Consequently a finite family whose
pairwise overlaps tend uniformly to zero is eventually independent. The
ambient Hilbert spaces may vary along an arbitrary filter.

These are consequences of the lower Gram estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma overlapestimate, lines 2109--2175.
-/

open Filter
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace MPSTensor

/-- Distinct primitive tensors with faithful invariant matrices have
independent boundary spaces at every sufficiently large length.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint,
lines 1744--1820, combined with Lemma overlapestimate, lines 2109--2175.
The primitive faithful generating data and their inequivalence are supplied. -/
theorem eventually_groundSpaceES_iSupIndep_of_primitive
    {d : ℕ} {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (B : ∀ j, MPSTensor d (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i)) :
    ∀ᶠ N in atTop, iSupIndep (fun j => groundSpaceES (B j) N) := by
  apply Submodule.eventually_iSupIndep_of_pairwise_overlap
  intro ε hε
  filter_upwards [Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun hij =>
      (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
        (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε] with N hN
  exact fun i j hij => hN i j hij

end MPSTensor
