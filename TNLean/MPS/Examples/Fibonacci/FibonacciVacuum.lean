/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.Fibonacci
import TNLean.MPS.MPDO.OperatorCyclicSum

/-!
# Fibonacci vacuum operator: the projection onto admissible configurations

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` lines 1262–1265: the
Fibonacci projector matrix product operator splits into two blocks `B_1`, `B_τ` of dimensions `2`
and `3` satisfying the Fibonacci fusion rules. The source prints no entries of `B_1`; the vacuum
block is the admissibility projector of `Examples/Fibonacci.lean`.

**Formalized here.** For every positive length `N`, the periodic operator `P_N = O_N(B_1)` of the
vacuum block is diagonal in the configuration basis, `⟨y|P_N|x⟩ = δ_{yx} p_N(x)`, where
`p_N(x) = ∏_v K_{x_v x_{v+1}}` is the cyclic admissibility weight of the adjacency matrix
`K = [[0, 1], [1, 1]]`, equal to `1` exactly when `x` has no cyclic neighbouring pair `00`. Hence
`P_N` is the orthogonal projection onto the span of the admissible basis vectors, its kernel is
the span of the inadmissible ones, and `P_N` is not the identity. In the Lean normalization the
label `0` is the trivial label `1` and the label `1` is `τ`; `|x⟩` is the standard basis vector
`Pi.single x 1`, and the cyclic successor `v + 1` is addition in `Fin N`.

**Local fix (provenance):** the entries of the vacuum block are not printed by the source;
the block used here is the admissibility projector of `Examples/Fibonacci.lean`, documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main definitions

* `FibonacciCompression.fibAdjacency`: the adjacency matrix `K = [[0, 1], [1, 1]]`.
* `FibonacciCompression.fibAdmissibility`: the cyclic admissibility weight `p_N`.

## Main results

* `FibonacciCompression.fibAdmissibility_eq_one_iff`: `p_N(x) = 1` exactly when `x` has no
  cyclic neighbouring pair `00`.
* `FibonacciCompression.mpo_fibOne_apply`: the kernel `⟨y|P_N|x⟩ = δ_{yx} p_N(x)`.
* `FibonacciCompression.mpo_fibOne_isStarProjection`: `P_N² = P_N = P_N†`.
* `FibonacciCompression.range_mpo_fibOne`, `FibonacciCompression.ker_mpo_fibOne`: the range and
  the kernel of `P_N`.
* `FibonacciCompression.mpo_fibOne_ne_one`: `P_N` is not the identity.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

noncomputable section

open scoped Matrix BigOperators

namespace FibonacciCompression

open MPSTensor

/-- The adjacency matrix `K = [[0, 1], [1, 1]]` of the Fibonacci chain: `K_{ab} = 0` exactly for
the neighbouring pair `ab = 00` of trivial labels. -/
def fibAdjacency : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 1, 1]

theorem fibAdjacency_apply (a b : Fin 2) :
    fibAdjacency a b = if ¬(a = 0 ∧ b = 0) then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

variable {N : ℕ} [NeZero N]

/-- The cyclic admissibility weight `p_N(x) = ∏_v K_{x_v x_{v+1}}` of a configuration of `N`
labels, the last-to-first pair included. -/
def fibAdmissibility (x : Fin N → Fin 2) : ℕ := ∏ v : Fin N, fibAdjacency (x v) (x (v + 1))

theorem fibAdmissibility_eq (x : Fin N → Fin 2) :
    fibAdmissibility x = if ∀ v, ¬(x v = 0 ∧ x (v + 1) = 0) then 1 else 0 := by
  simp only [fibAdmissibility, fibAdjacency_apply]
  rw [Finset.prod_boole]
  simp

/-- A configuration is admissible, `p_N(x) = 1`, exactly when it has no cyclic neighbouring pair
`00`. -/
lemma fibAdmissibility_eq_one_iff (x : Fin N → Fin 2) :
    fibAdmissibility x = 1 ↔ ∀ v, ¬(x v = 0 ∧ x (v + 1) = 0) := by
  rw [fibAdmissibility_eq]
  split_ifs with h <;> simpa using h

/-- The admissibility weight takes only the values `0` and `1`. -/
theorem fibAdmissibility_eq_zero_or_one (x : Fin N → Fin 2) :
    fibAdmissibility x = 0 ∨ fibAdmissibility x = 1 := by
  rw [fibAdmissibility_eq]
  split_ifs <;> simp

/-- The all-trivial configuration is not admissible. -/
theorem fibAdmissibility_zero : fibAdmissibility (fun _ : Fin N ↦ (0 : Fin 2)) = 0 := by
  simp [fibAdmissibility_eq]

/-- The entries of the vacuum block: `(B_1^{ij})_{lr} = δ_{ij} δ_{lj} K_{jr}`. -/
theorem fibOne_apply (i j l r : Fin 2) :
    fibOne i j l r = if i = j ∧ l = j then (fibAdjacency j r : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [fibOne, fibOneGolden, fibAdjacency]

/-- Project result: blueprint `lem:asymex_fib_vacuum`,
equation `eq:asymex_fib_vacuum_kernel`. **The kernel of the vacuum operator**:
`⟨y|P_N|x⟩ = δ_{yx} p_N(x)`. -/
lemma mpo_fibOne_apply (y x : Fin N → Fin 2) :
    MPOTensor.mpo fibOne N y x = if y = x then (fibAdmissibility x : ℂ) else 0 := by
  rw [MPOTensor.mpo_apply_of_forced_left_bond (π := id) (β := fun _ j ↦ j)
    (φ := fun _ j r ↦ (fibAdjacency j r : ℂ)) fun i j l r ↦ fibOne_apply i j l r]
  by_cases h : y = x
  · subst h
    simp [fibAdmissibility]
  · simp [h]

/-- The vacuum operator is the diagonal matrix of the admissibility weights. -/
theorem mpo_fibOne_eq_diagonal :
    MPOTensor.mpo fibOne N = Matrix.diagonal fun x ↦ (fibAdmissibility x : ℂ) := by
  ext y x
  rw [mpo_fibOne_apply]
  by_cases h : y = x
  · subst h
    simp
  · simp [h]

/-- `P_N` multiplies each coordinate by its admissibility weight; in particular
`P_N|x⟩ = p_N(x)|x⟩`. -/
theorem mpo_fibOne_mulVec (w : (Fin N → Fin 2) → ℂ) :
    MPOTensor.mpo fibOne N *ᵥ w = fun x ↦ (fibAdmissibility x : ℂ) * w x := by
  rw [mpo_fibOne_eq_diagonal]
  ext x
  exact Matrix.mulVec_diagonal _ _ x

/-- A vector supported on admissible configurations is fixed by `P_N`. -/
theorem mpo_fibOne_mulVec_eq_self {w : (Fin N → Fin 2) → ℂ}
    (hw : ∀ x, fibAdmissibility x = 0 → w x = 0) :
    MPOTensor.mpo fibOne N *ᵥ w = w := by
  rw [mpo_fibOne_mulVec]
  ext x
  rcases fibAdmissibility_eq_zero_or_one x with h | h
  · simp [hw x h]
  · simp [h]

/-- Project result: blueprint `lem:asymex_fib_vacuum`.
**The vacuum operator is an orthogonal projection**: `P_N² = P_N = P_N†`. -/
lemma mpo_fibOne_isStarProjection : IsStarProjection (MPOTensor.mpo fibOne N) := by
  rw [isStarProjection_iff', mpo_fibOne_eq_diagonal]
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext x
    rcases fibAdmissibility_eq_zero_or_one x with h | h <;> simp [h]
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    ext x
    simp

/-- Project result: blueprint `lem:asymex_fib_vacuum`, equation
`eq:asymex_fib_vacuum_range`. **The range of the vacuum operator** is the span of the admissible
basis vectors, `ran P_N = span_ℂ {|x⟩ : p_N(x) = 1}`. -/
lemma range_mpo_fibOne :
    LinearMap.range (Matrix.toLin' (MPOTensor.mpo fibOne N)) =
      Submodule.span ℂ
        ((fun x ↦ Pi.single x 1) '' {x : Fin N → Fin 2 | fibAdmissibility x = 1}) := by
  have hspan : Submodule.span ℂ
      ((fun x ↦ Pi.single x 1) '' {x : Fin N → Fin 2 | fibAdmissibility x = 1}) =
      Pi.spanSubset ℂ {x : Fin N → Fin 2 | fibAdmissibility x = 1} := by
    simp only [Pi.spanSubset, Pi.basisFun_apply]
  rw [hspan]
  ext v
  rw [Pi.mem_spanSubset_iff, LinearMap.mem_range]
  simp only [Matrix.toLin'_apply, mpo_fibOne_mulVec, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, rfl⟩ x hx
    rcases fibAdmissibility_eq_zero_or_one x with h | h
    · simp [h]
    · exact absurd h hx
  · intro hv
    refine ⟨v, funext fun x ↦ ?_⟩
    rcases fibAdmissibility_eq_zero_or_one x with h | h
    · simp [h, hv x (by simp [h])]
    · simp [h]

/-- Project result: blueprint `lem:asymex_fib_vacuum`, equation
`eq:asymex_fib_vacuum_null`. **The kernel of the vacuum operator** is the span of the
inadmissible basis vectors, `ker P_N = span_ℂ {|x⟩ : p_N(x) = 0}`. -/
lemma ker_mpo_fibOne :
    LinearMap.ker (Matrix.toLin' (MPOTensor.mpo fibOne N)) =
      Submodule.span ℂ
        ((fun x ↦ Pi.single x 1) '' {x : Fin N → Fin 2 | fibAdmissibility x = 0}) := by
  have hspan : Submodule.span ℂ
      ((fun x ↦ Pi.single x 1) '' {x : Fin N → Fin 2 | fibAdmissibility x = 0}) =
      Pi.spanSubset ℂ {x : Fin N → Fin 2 | fibAdmissibility x = 0} := by
    simp only [Pi.spanSubset, Pi.basisFun_apply]
  rw [hspan]
  ext v
  rw [Pi.mem_spanSubset_iff, LinearMap.mem_ker]
  simp only [Matrix.toLin'_apply, mpo_fibOne_mulVec, Set.mem_ofPred_eq, funext_iff,
    Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero]
  refine forall_congr' fun x ↦ ?_
  tauto

/-- Project result: blueprint `lem:asymex_fib_vacuum`. **The vacuum
operator is not the identity**: the all-trivial configuration lies in its kernel. -/
lemma mpo_fibOne_ne_one : MPOTensor.mpo fibOne N ≠ 1 := by
  intro h
  have := congrFun (congrFun h (fun _ ↦ 0)) (fun _ ↦ 0)
  rw [mpo_fibOne_apply] at this
  simp [fibAdmissibility_zero] at this

end FibonacciCompression
