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

At a positive initial length, joint boundary injectivity persists at every larger length.
Indeed, a boundary annihilated after adjoining one letter is annihilated by every letter;
every nonempty word then annihilates it, and injectivity at the original length gives zero.
Thus simultaneous word spanning is open and persists at larger lengths without normalization
or nonzero block-dimension assumptions.
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

/-- At each prescribed length, simultaneous word spanning is open in the tensor entries.
This is the finite-dimensional injectivity ingredient in arXiv:1010.3732, Appendix A,
lines 2499–2503 and 2575–2578. -/
theorem isOpen_setOf_wordTupleSpanTop_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ) :
    IsOpen {x | WordTupleSpanTop (A x) L} := by
  simpa only [wordTupleSpanTop_iff_blockGroundSpaceMapES_injective] using
    isOpen_setOf_blockGroundSpaceMapES_injective_family A hA L

/-- Joint boundary injectivity at a positive length persists after adjoining one physical site.
This is a normalization-free form of the word-span propagation in PGVWC07,
arXiv:quant-ph/0608197, lines 893–898. -/
theorem blockGroundSpaceMap_injective_succ_of_pos
    (A : (j : Fin r) → MPSTensor d (dim j)) {L : ℕ}
    (hInj : Function.Injective (blockGroundSpaceMap A L))
    (hL : 0 < L) :
    Function.Injective (blockGroundSpaceMap A (L + 1)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro Δ hΔ
  have hleft (i : Fin d) : blockGroundSpaceMap A L (fun j => A j i * Δ j) = 0 := by
    ext w
    have hw := congrFun hΔ (Fin.append w (fun _ : Fin 1 => i))
    simp only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
      Pi.zero_apply, List.ofFn_fin_append, Kraus.evalWord_append] at hw
    simpa only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
      Pi.zero_apply, List.ofFn_succ, List.ofFn_zero,
      Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one,
      Matrix.mul_assoc] using hw
  have hzero (i : Fin d) (j : Fin r) : A j i * Δ j = 0 :=
    congrFun (hInj ((hleft i).trans (map_zero _).symm)) j
  have hword (j : Fin r) (w : Fin L → Fin d) :
      Kraus.evalWord (A j) (List.ofFn w) * Δ j = 0 := by
    have hInt := Kraus.evalWord_intertwine (A j) (fun _ => 0) (Δ j)
      (fun i => by simp only [hzero, Matrix.mul_zero]) (List.ofFn w)
    cases L with
    | zero => omega
    | succ n =>
      simpa only [List.ofFn_succ, Kraus.evalWord_cons, Matrix.zero_mul,
        Matrix.mul_zero] using hInt
  apply hInj
  rw [map_zero]
  ext w
  simp only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
    hword, Matrix.trace_zero, Finset.sum_const_zero, Pi.zero_apply]

/-- Positive-length joint injectivity persists at every larger length without normalization.
This is the Hilbert-coordinate form of homogeneous word-span propagation in PGVWC07,
arXiv:quant-ph/0608197, lines 893–898. -/
theorem blockGroundSpaceMapES_injective_of_ge_of_pos
    (A : (j : Fin r) → MPSTensor d (dim j)) {L n : ℕ}
    (hInj : Function.Injective (blockGroundSpaceMapES A L))
    (hL : 0 < L) (hLn : L ≤ n) :
    Function.Injective (blockGroundSpaceMapES A n) := by
  rw [blockGroundSpaceMapES_injective_iff] at hInj ⊢
  exact Nat.le_induction hInj
    (fun k hk h => blockGroundSpaceMap_injective_succ_of_pos A h (hL.trans_le hk)) n hLn

/-- A positive simultaneous word span persists at all larger lengths, including for families
with zero block dimensions. This is a normalization-free form of homogeneous word-span
propagation in PGVWC07, arXiv:quant-ph/0608197, lines 893–898. -/
theorem wordTupleSpanTop_of_ge_of_pos
    (A : (j : Fin r) → MPSTensor d (dim j)) {L n : ℕ}
    (hSpan : WordTupleSpanTop A L) (hL : 0 < L) (hLn : L ≤ n) :
    WordTupleSpanTop A n := by
  exact (wordTupleSpanTop_iff_blockGroundSpaceMapES_injective A n).mpr
    (blockGroundSpaceMapES_injective_of_ge_of_pos A
      ((wordTupleSpanTop_iff_blockGroundSpaceMapES_injective A L).mp hSpan) hL hLn)

end MPSTensor
