/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXOnSiteSymmetry

/-!
# Constrained CZX boundary coordinates

A cyclic sequence of effective plaquette spins labels each boundary leg by
its adjacent pair. The resulting coordinate embedding is an isometry. The
physical rectangle support theorem uses these same coordinates; the boundary
matrix-product-unitary identification is re-exported by `CZXSymmetry`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), boundary plaquettes, lines 339–341.
-/

open scoped BigOperators Matrix
open Matrix

namespace TNLean.PEPS

variable (N : ℕ) [NeZero N]

/-- The closed chain of `N` boundary legs carrying the effective spins `c`: leg `m` carries the
qubits `(c m, c (m + 1))` of the two plaquettes it touches, so neighbouring legs carry the same
qubit of their common plaquette (arXiv:1106.4752,
`References/1106.4752/source/dDSPTmodel.tex` lines 339–341). -/
def czxBoundaryLegs (c : Fin N → Fin 2) : Fin N → Fin 4 :=
  fun m => czxBond (c m, c (m + 1))

theorem czxBoundaryLegs_injective : Function.Injective (czxBoundaryLegs N) := by
  intro c c' h
  funext m
  have := congrArg (fun x => (czxBond.symm (x m)).1) h
  simpa [czxBoundaryLegs] using this

/-- The isometric embedding of the effective spins into the configurations of the boundary
legs. -/
def czxBoundaryEmbedding : Matrix (Fin N → Fin 4) (Fin N → Fin 2) ℂ :=
  Matrix.of fun x c => if x = czxBoundaryLegs N c then 1 else 0

theorem czxBoundaryEmbedding_conjTranspose_mul_self :
    (czxBoundaryEmbedding N)ᴴ * czxBoundaryEmbedding N = 1 := by
  ext c c'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, czxBoundaryEmbedding, Matrix.of_apply,
    apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Matrix.one_apply]
  simp [(czxBoundaryLegs_injective N).eq_iff]

end TNLean.PEPS
