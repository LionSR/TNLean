/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciDimension
import TNLean.MPS.Symmetry.MPOSymmetry.SymmetricBoundary

/-!
# Fibonacci: the positive symmetric boundary state

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex` lines 1795–1805 (`symboundary`): a positive combination
`ψ = ∑_x v_x ψ_{A_x}` of the blocks of a module with `O_a ψ = r_a ψ`, where `r_a = d_a` is the
quantum dimension when the blocks of the algebra and of the state coincide (line 1805); and
line 1993: the Fibonacci algebra `{1, τ; τ × τ = 1 + τ}` acts on two blocks by
`τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ`.

**Formalized here.** The Fibonacci structure constants form a fusion ring
(`MPOTensor.IsFusionRing`) with unit `1` and every label self-dual. For the pair of normal
states `ψ_A`, `ψ_C` carrying the regular representation
(`FibonacciCompression.isMPOSymmetricFamily_fibNimTargets`), the weights `v = (1, φ)` are the
positive common eigenvector, and `ψ = ψ_A + φ ψ_C` satisfies `O_1 ψ = ψ` and `O_τ ψ = φ ψ` at
every positive length: `r_τ = d_τ = φ`.

**Local fix (provenance):** the operator blocks `O_1`, `O_τ` and the two normal states are those
of `Examples/Fibonacci.lean` and `Examples/FibonacciAction.lean`, whose entries the source does not
print; documented in `docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main results

* `FibonacciCompression.isFusionRing_fibNim`: the Fibonacci fusion ring.
* `FibonacciCompression.fibDim_left_eigenvector`: `(1, φ)` is a common left eigenvector of the
  multiplicity matrices with eigenvalues `d_a`.
* `FibonacciCompression.mpo_fibBlock_mulVec_boundary`: `O_a ψ = d_a ψ` for both labels.
* `FibonacciCompression.mpo_fibTau_mulVec_boundary`: `O_τ ψ = φ ψ`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped goldenRatio Matrix

open MPSTensor MPOTensor

namespace FibonacciCompression

/-- **The Fibonacci fusion ring** (arXiv:2203.12563, line 1993): the structure constants
`fibNim` are associative, with unit `1` and both labels self-dual. -/
theorem isFusionRing_fibNim : IsFusionRing fibNim 0 id where
  assoc := by decide +kernel
  isFusionUnit := isFusionUnit_fibNim
  dual_dual _ := rfl
  apply_unit := by decide +kernel
  dual_anti a b c := by fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- **The weights `(1, φ)` are a positive common left eigenvector** of the Fibonacci
multiplicity matrices (arXiv:2203.12563, lines 1801–1805):
`∑_x v_x N_{a x}^y = d_a v_y` with `v = (d_1, d_τ) = (1, φ)`. -/
theorem fibDim_left_eigenvector (a y : Fin 2) :
    ∑ x, fibDim x * fibNim a x y = perronFrobeniusDim fibNim a * fibDim y := by
  rw [perronFrobeniusDim_eq_of_dimension_relation fibDim_pos fibNim_dimension_relation a,
    ← fibNim_dimension_relation a y]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The Fibonacci boundary state `ψ = ψ_A + φ ψ_C` at length `L`, the combination
`∑_x v_x ψ_{A_x}` of arXiv:2203.12563, line 1803, with weights `v = (1, φ)`. -/
noncomputable def fibBoundaryState (L : ℕ) : (Fin L → Fin 2) → ℂ :=
  fun σ => ∑ x, (fibDim x : ℂ) * mpv (fibNimTargets x) σ

/-- **The Fibonacci boundary state is a common eigenvector** (arXiv:2203.12563, lines
1795–1805): `O_a ψ = d_a ψ` for both labels at every positive length. -/
theorem mpo_fibBlock_mulVec_boundary (a : Fin 2) {L : ℕ} (hL : 0 < L) :
    mpo (fibBlock a) L *ᵥ fibBoundaryState L =
      (perronFrobeniusDim fibNim a : ℂ) • fibBoundaryState L :=
  isMPOSymmetricFamily_fibNimTargets.mpo_mulVec_sum_eq_smul
    (fun y => by exact_mod_cast fibDim_left_eigenvector a y) hL

/-- **`O_τ ψ = φ ψ`** (arXiv:2203.12563, line 1805 with lines 1993: `r_τ = d_τ = φ`). -/
theorem mpo_fibTau_mulVec_boundary {L : ℕ} (hL : 0 < L) :
    mpo fibTau L *ᵥ fibBoundaryState L = (φ : ℂ) • fibBoundaryState L := by
  have h := mpo_fibBlock_mulVec_boundary 1 hL
  rwa [perronFrobeniusDim_fibNim_tau] at h

/-- **`O_1 ψ = ψ`**: the unit fixes the Fibonacci boundary state. -/
theorem mpo_fibOne_mulVec_boundary {L : ℕ} (hL : 0 < L) :
    mpo fibOne L *ᵥ fibBoundaryState L = fibBoundaryState L := by
  have h := mpo_fibBlock_mulVec_boundary 0 hL
  rwa [perronFrobeniusDim_fibNim_one, Complex.ofReal_one, one_smul] at h

end FibonacciCompression
