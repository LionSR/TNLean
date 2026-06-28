/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.OrderClosed

/-!
# Order-closedness of the Loewner order on finite matrices

This file records that the Loewner (positive semidefinite) order on finite
complex matrices is compatible with the matrix topology: the positive
semidefinite cone is closed, the order graph $\{(X, Y) : X \le Y\}$ is closed,
and consequently the order topology is closed (`OrderClosedTopology`).

These are purely topological facts about the matrix order, with no quantum
channel content. They are isolated in this low-level analysis module so that
both the channel theory and the operator-monotone and operator-concave
machinery (which integrate matrix-valued functions against the Loewner order)
can use them without depending on one another.

## Main results

* `matrix_isClosed_posSemidef` — the positive semidefinite cone is closed.
* `matrix_isClosed_le` — the Loewner order graph is closed.
* `matrixOrderClosedTopology` — the Loewner order on finite matrices has a closed
  order topology (`OrderClosedTopology`), registered as a scoped instance in the
  `MatrixOrder` namespace.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

/-- The quadratic form `X ↦ star v ⬝ᵥ X.mulVec v` is continuous. -/
private lemma continuous_quadraticForm {m : Type*} [Fintype m] (v : m → ℂ) :
    Continuous (fun X : Matrix m m ℂ => star v ⬝ᵥ X.mulVec v) :=
  Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_id continuous_const)

/-- The positive semidefinite cone is closed for matrices over any finite index
type. -/
theorem matrix_isClosed_posSemidef {m : Type*} [Finite m] :
    IsClosed {X : Matrix m m ℂ | X.PosSemidef} := by
  classical
  letI := Fintype.ofFinite m
  have : {X : Matrix m m ℂ | X.PosSemidef}
      = {X | X.IsHermitian} ∩
        ⋂ (v : m → ℂ), {X | 0 ≤ star v ⬝ᵥ X.mulVec v} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [this]
  exact (isClosed_eq continuous_star continuous_id).inter
    (isClosed_iInter fun v =>
      (isClosed_le continuous_const continuous_id).preimage (continuous_quadraticForm v))

/-- The Loewner order graph is closed for matrices over any finite index type. -/
theorem matrix_isClosed_le {m : Type*} [Finite m] :
    IsClosed {p : Matrix m m ℂ × Matrix m m ℂ | p.1 ≤ p.2} := by
  have hset :
      {p : Matrix m m ℂ × Matrix m m ℂ | p.1 ≤ p.2}
        = (fun p : Matrix m m ℂ × Matrix m m ℂ => p.2 - p.1) ⁻¹'
          {X : Matrix m m ℂ | X.PosSemidef} := by
    ext p
    simp [Matrix.le_iff]
  rw [hset]
  exact matrix_isClosed_posSemidef.preimage (continuous_snd.sub continuous_fst)

/-- The Loewner order on finite complex matrices has closed order topology. -/
@[reducible]
def matrixOrderClosedTopology {m : Type*} [Finite m] :
    OrderClosedTopology (Matrix m m ℂ) where
  isClosed_le' := matrix_isClosed_le

scoped[MatrixOrder] attribute [instance] matrixOrderClosedTopology
