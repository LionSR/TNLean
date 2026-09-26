/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.CyclicTraceForcedBond
import TNLean.MPS.Examples.Fibonacci.FibonacciAction
import TNLean.MPS.Examples.Fibonacci.FibonacciVacuum
import TNLean.MPS.Overlap.Basic

/-!
# Fibonacci amplitudes: the product state and the chain state

**Source.** Garre-Rubio, Lootens and Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1991–1993: for the Fibonacci matrix product operator of
arXiv:1511.08090 the invariant normal states form two blocks `x_1`, `x_τ`. The source prints no
explicit pair of states; the all-`τ` tensor `A` and the chain tensor `C` are the construction of
`Examples/FibonacciAction.lean`.

**Formalized here.** For every positive length `N`, the product tensor gives the basis vector
`|V^{(N)}(A)⟩ = |1, …, 1⟩`, of norm one. The chain tensor gives the amplitudes
`V^{(N)}(C)_x = p_N(x) σ^{n_0(x)} (-σ²)^{n_{11}(x)}`, where `p_N` is the cyclic admissibility
weight of `Examples/FibonacciVacuum.lean`, `n_0(x)` counts the zeros of `x` and `n_{11}(x)`
counts its cyclic neighbouring pairs `11`. The squared chain norm is
`∑_x p_N(x) σ^{2 n_0(x) + 4 n_{11}(x)}`, and this norm is positive. In the Lean normalization the
label `1` is `τ`, `σ = φ^{-1/2}` is `goldenSigmaReal`, the periodic vector is
`MPSTensor.mpvState`, and the cyclic successor `v + 1` is addition in `Fin N`. The remaining
clause of the blueprint lemma, that both vectors are fixed by the vacuum operator
`P_N = O_N(B_1)`, is `mpo_fibOne_mulVec_allTau` (`Examples/FibonacciAction.lean`) and
`mpo_fibOne_mulVec_chain` (`Examples/FibonacciAnomaly.lean`); the amplitude formula also shows
that the chain vector has admissible support, so `mpo_fibOne_mulVec_eq_self` applies to it.

## Main definitions

* `FibonacciCompression.fibZeroCount`: the number `n_0(x)` of zeros of a configuration.
* `FibonacciCompression.fibPairOneCount`: the number `n_{11}(x)` of cyclic neighbouring pairs `11`.
* `FibonacciCompression.fibChainWeight`: the matrix `H = [[0, σ], [1, -σ²]]` with
  `(C^i)_{lr} = δ_{li} H_{ir}`.

## Main results

* `FibonacciCompression.mpvState_fibAllTau`, `FibonacciCompression.norm_mpvState_fibAllTau`: the
  product state is `|1, …, 1⟩`, of norm one.
* `FibonacciCompression.mpv_fibChain`: the chain amplitudes.
* `FibonacciCompression.norm_mpvState_fibChain_sq`,
  `FibonacciCompression.norm_mpvState_fibChain_pos`: the squared chain norm, and its positivity.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

noncomputable section

open scoped Matrix BigOperators

namespace FibonacciCompression

open GoldenInt MPSTensor

variable {N : ℕ} [NeZero N]

/-! ### The product state -/

/-- The entries of the all-`τ` tensor: `A^i_{00} = δ_{i1}`. -/
theorem fibAllTau_entry (i : Fin 2) (l r : Fin 1) :
    fibAllTau i l r = if l = 0 then (if i = 1 then 1 else 0) else 0 := by
  fin_cases i <;> fin_cases l <;> fin_cases r <;> simp [fibAllTau_apply]

/-- Project result: blueprint `lem:asymex_fib_amplitudes`. **The product state is `|1, …, 1⟩`**: the
amplitude of the all-`τ` tensor at `x` is `1` on the all-`τ` configuration and `0` elsewhere. -/
lemma mpvState_fibAllTau :
    mpvState fibAllTau N = EuclideanSpace.single (fun _ : Fin N ↦ (1 : Fin 2)) 1 := by
  ext x
  rw [mpvState_apply, PiLp.single_apply,
    mpv_of_forced_left_bond (β := fun _ ↦ 0) (φ := fun i _ ↦ if i = 1 then 1 else 0)
      fibAllTau_entry, Fintype.prod_boole]
  simp [funext_iff]

/-- Project result: blueprint `lem:asymex_fib_amplitudes`. The product state has norm one. -/
lemma norm_mpvState_fibAllTau : ‖mpvState fibAllTau N‖ = 1 := by
  rw [mpvState_fibAllTau, PiLp.norm_single, norm_one]

/-! ### The chain state -/

/-- The number `n_0(x)` of zeros of a configuration. -/
def fibZeroCount (x : Fin N → Fin 2) : ℕ := (Finset.univ.filter fun v ↦ x v = 0).card

/-- The number `n_{11}(x)` of cyclic neighbouring pairs `11` of a configuration, the last-to-first
pair included. -/
def fibPairOneCount (x : Fin N → Fin 2) : ℕ :=
  (Finset.univ.filter fun v ↦ x v = 1 ∧ x (v + 1) = 1).card

/-- The matrix `H = [[0, σ], [1, -σ²]]` whose rows are the nonzero rows of the chain tensor:
`(C^i)_{lr} = δ_{li} H_{ir}`. -/
def fibChainWeight : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, goldenSigmaComplex; 1, -goldenSigmaComplex ^ 2]

theorem fibChain_zero : fibChain 0 = !![0, goldenSigmaComplex; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fibChain, fibChainGolden, ← GoldenInt.zero_def, ← GoldenInt.sigma.eq_def]

theorem fibChain_one : fibChain 1 = !![0, 0; 1, -goldenSigmaComplex ^ 2] := by
  have h : (⟨0, 0, -1, 0⟩ : GoldenInt) = -GoldenInt.sigma ^ 2 := by decide
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fibChain, fibChainGolden, ← GoldenInt.zero_def, ← GoldenInt.one_def, h]

/-- The entries of the chain tensor: `(C^i)_{lr} = δ_{li} H_{ir}`. -/
theorem fibChain_entry (i l r : Fin 2) :
    fibChain i l r = if l = i then fibChainWeight i r else 0 := by
  fin_cases i <;> fin_cases l <;> fin_cases r <;>
    simp [fibChain_zero, fibChain_one, fibChainWeight]

/-- The chain amplitude is the product of the entries of `H` along the configuration,
`V^{(N)}(C)_x = ∏_v H_{x_v x_{v+1}}`. -/
theorem mpv_fibChain_eq_prod (x : Fin N → Fin 2) :
    mpv fibChain x = ∏ v : Fin N, fibChainWeight (x v) (x (v + 1)) :=
  mpv_of_forced_left_bond (β := id) fibChain_entry x

/-- The entries of `H` split into the admissibility factor, a factor `σ` for each zero and a
factor `-σ²` for each pair `11`. -/
theorem fibChainWeight_eq (a b : Fin 2) :
    fibChainWeight a b = (fibAdjacency a b : ℂ) * (if a = 0 then goldenSigmaComplex else 1) *
      (if a = 1 ∧ b = 1 then -goldenSigmaComplex ^ 2 else 1) := by
  fin_cases a <;> fin_cases b <;> simp [fibChainWeight, fibAdjacency]

/-- Project result: blueprint `lem:asymex_fib_amplitudes`, equation `eq:asymex_fib_chain_amplitude`.
**The chain amplitudes**: `V^{(N)}(C)_x = p_N(x) σ^{n_0(x)} (-σ²)^{n_{11}(x)}`. -/
lemma mpv_fibChain (x : Fin N → Fin 2) :
    mpv fibChain x = (fibAdmissibility x : ℂ) * goldenSigmaComplex ^ fibZeroCount x *
      (-goldenSigmaComplex ^ 2) ^ fibPairOneCount x := by
  simp only [mpv_fibChain_eq_prod, fibChainWeight_eq, Finset.prod_mul_distrib, fibAdmissibility,
    Nat.cast_prod, Finset.prod_ite, Finset.prod_const, one_pow, mul_one, fibZeroCount,
    fibPairOneCount]

/-- The chain amplitudes are the images of real numbers. -/
theorem mpv_fibChain_eq_ofReal (x : Fin N → Fin 2) :
    mpv fibChain x = ((fibAdmissibility x : ℝ) * goldenSigmaReal ^ fibZeroCount x *
      (-goldenSigmaReal ^ 2) ^ fibPairOneCount x : ℝ) := by
  rw [mpv_fibChain]
  push_cast
  rfl

/-- Project result: blueprint `lem:asymex_fib_amplitudes`, equation `eq:asymex_fib_chain_norm`.
**The squared chain norm**: `‖V^{(N)}(C)‖² = ∑_x p_N(x) σ^{2 n_0(x) + 4 n_{11}(x)}`. -/
lemma norm_mpvState_fibChain_sq :
    ‖mpvState fibChain N‖ ^ 2 = ∑ x : Fin N → Fin 2,
      (fibAdmissibility x : ℝ) *
        goldenSigmaReal ^ (2 * fibZeroCount x + 4 * fibPairOneCount x) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mpvState_apply, mpv_fibChain_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (fibPairOneCount x) 2,
    (even_two_mul _).neg_pow, ← pow_mul]
  rcases fibAdmissibility_eq_zero_or_one x with h | h <;> simp only [h] <;> ring

/-- Project result: blueprint `lem:asymex_fib_amplitudes`. **The chain norm is positive**: the
all-`τ` amplitude is `(-σ²)^N ≠ 0`. -/
lemma norm_mpvState_fibChain_pos : 0 < ‖mpvState fibChain N‖ := by
  have hσ : goldenSigmaComplex ≠ 0 := by
    intro h
    have h2 := goldenSigmaReal_sq
    have : goldenSigmaReal = 0 := by simpa [goldenSigmaComplex] using h
    rw [this, zero_pow two_ne_zero] at h2
    exact (inv_pos.mpr Real.goldenRatio_pos).ne h2
  refine norm_pos_iff.mpr fun h ↦ ?_
  have hx := congrArg (fun v : MPVSpace 2 N ↦ v fun _ ↦ 1) h
  simp only [mpvState_apply, mpv_fibChain_eq_prod, PiLp.zero_apply] at hx
  simp [fibChainWeight, hσ] at hx

end FibonacciCompression
