/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixKroneckerEmbed
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Identity-tensor homomorphisms for operator-norm C-star matrices

For finite index sets $m$ and $n$, the identity-tensor map
$A \mapsto A \otimes \mathbf 1_n$ is a star-algebra homomorphism from
$M_m(\mathbb C)$ to $M_{m \times n}(\mathbb C)$.  With the standard operator norms, this map
preserves the unit, multiplication, adjoint, and complex scalar multiplication.  It is injective
when $n$ is nonempty.

## Main definitions

* `CStarMatrix.leftKroneckerEmbed` — the identity-tensor star-algebra homomorphism.

## Main results

* `CStarMatrix.leftKroneckerEmbed_apply_apply` — its entrywise formula.
* `CStarMatrix.leftKroneckerEmbed_injective` — injectivity for a nonempty identity factor.
-/


namespace CStarMatrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The identity-tensor star-algebra homomorphism between operator-norm complex matrix algebras. -/
noncomputable def leftKroneckerEmbed :
    CStarMatrix m m ℂ →⋆ₐ[ℂ] CStarMatrix (m × n) (m × n) ℂ :=
  ofMatrixStarAlgEquiv.toStarAlgHom.comp <|
    (Matrix.leftKroneckerEmbed (m := m) (n := n)).comp
      ofMatrixStarAlgEquiv.symm.toStarAlgHom

/-- Entrywise, the homomorphism is a matrix tensored with the identity. -/
@[simp]
theorem leftKroneckerEmbed_apply_apply (A : CStarMatrix m m ℂ) (i j : m × n) :
    leftKroneckerEmbed (n := n) A i j = A i.1 j.1 * if i.2 = j.2 then 1 else 0 := by
  change A i.1 j.1 * (1 : Matrix n n ℂ) i.2 j.2 = _
  simp [Matrix.one_apply]

/-- The left Kronecker homomorphism is injective when the identity factor is nonempty. -/
theorem leftKroneckerEmbed_injective [Nonempty n] :
    Function.Injective (leftKroneckerEmbed (m := m) (n := n)) := by
  intro A B h
  ext i j
  let k : n := Classical.choice ‹Nonempty n›
  have hij := congrFun (congrFun h (i, k)) (j, k)
  simpa using hij

end CStarMatrix
