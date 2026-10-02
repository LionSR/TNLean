/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceMapContinuity
import TNLean.MPS.SharedInfra.MatrixFamilyTracePairing

/-!
# Simultaneous word spanning and joint boundary injectivity

The joint boundary map at length \(L\) is injective precisely when the length-\(L\) word tuples
span the product of the block matrix algebras. The equivalence follows from the nondegeneracy
of the trace pairing, without normalization or positivity assumptions on the tensor blocks.
It connects the common boundary-injectivity window with the simultaneous word span used in
the open-chain ground-space argument of PGVWC07, Theorem 12, lines 1430–1454.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Joint boundary injectivity at length \(L\) implies simultaneous spanning by length-\(L\)
words. This is the finite-dimensional trace duality behind the boundary parametrization in
PGVWC07, Theorem 12, proof lines 1430–1434. -/
theorem wordTupleSpanTop_of_blockGroundSpaceMap_injective
    {A : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hInj : Function.Injective (blockGroundSpaceMap A L)) : WordTupleSpanTop A L := by
  unfold WordTupleSpanTop
  apply Matrix.family_submodule_eq_top_of_trace_separating
  intro Δ hSep
  have hΔ : blockGroundSpaceMap A L Δ = 0 := by
    ext w
    simp only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
      Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun j _ => Matrix.trace_mul_comm
      (Kraus.evalWord (A j) (List.ofFn w)) (Δ j))]
    exact hSep (wordTuple A L w) (Submodule.subset_span (Set.mem_range_self w))
  have hΔzero : Δ = 0 := hInj (by simpa using hΔ)
  exact fun j => congrFun hΔzero j

/-- Simultaneous word spanning at a prescribed length is equivalent to injectivity of the joint
Hilbert boundary map. This is the trace-duality form of the boundary parametrization in
PGVWC07, Theorem 12, proof lines 1430–1434. -/
theorem wordTupleSpanTop_iff_blockGroundSpaceMapES_injective
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    WordTupleSpanTop A L ↔ Function.Injective (blockGroundSpaceMapES A L) := by
  refine ⟨fun hSpan => blockGroundSpaceMapES_injective_of_wordTupleSpanTop (A := A) hSpan, ?_⟩
  intro hInj
  exact wordTupleSpanTop_of_blockGroundSpaceMap_injective
    ((blockGroundSpaceMapES_injective_iff A L).mp hInj)

end MPSTensor
