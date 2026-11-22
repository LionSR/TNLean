/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalSign

/-!
# Trace signs of the example time-reversal gates

The time-reversal sign of an MPU in standard form with gates `u`, `v` on `ℂ² ⊗ ℂ²` is the
normalized trace
\[
  s(u,v) = \tfrac14\operatorname{tr}\bigl[\mathbb S_{12,34}\,v_{23}u_{12}u_{34}v_{23}\bigr]
\]
of equation `eq:sigma-from-trace` of arXiv:1703.09188 (lines 1595--1611). This file evaluates it
for the four gate pairs of the source's time-reversal examples (lines 1906--1962):

| `u` | `v` | `s(u,v)` |
|---|---|---|
| `CZ (X ⊗ X)` | `CZ` | `-1` |
| `1` | `1` | `1` |
| `i 1` | `1` | `-1` |
| `i CZ (X ⊗ X)` | `CZ` | `1` |

Here `X` is the Pauli matrix and `CZ = diag(1, 1, 1, -1)`. The values agree with the first sign
`σ⁽¹⁾` printed for these examples. They are statements about the gates only: the source's further
claims, the second sign `σ⁽²⁾` of a blocked standard form and the classification by both signs,
use Proposition `prop:sigma1-and-sigma2-equal` and are not stated here. The printed one-site CZX
tensor does not generate unitaries (`docs/paper-gaps/mpu_czx_tensor_normalization.tex`); the
gates `CZ (X ⊗ X)` and `CZ` are not affected.

The traces are evaluated exactly over `ℤ` and transported to `ℂ` along the integer cast.

## Main results

* `MPOTensor.timeReversalTrace_smul_left`: a scalar on `u` enters the trace squared.
* `MPOTensor.TimeReversalExamples.timeReversalSign_czx`, `timeReversalSign_one`,
  `timeReversalSign_I_smul_one`, `timeReversalSign_I_smul_czx`: the four signs.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d : ℕ}

/-- A scalar multiple of the gate `u` enters the time-reversal trace squared, since `u` occurs
twice: `tr[S v (c u ⊗ c u) v] = c² tr[S v (u ⊗ u) v]`.

Source: arXiv:1703.09188, equation `eq:sigma-from-trace`, lines 1595--1611. -/
theorem timeReversalTrace_smul_left (c : ℂ) (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    timeReversalTrace (c • u) v = c ^ 2 * timeReversalTrace u v := by
  unfold timeReversalTrace
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, sq]

/-- A scalar multiple of the gate `u` enters the normalized time-reversal trace squared.

Source: arXiv:1703.09188, equation `eq:sigma-from-trace`, lines 1595--1611. -/
theorem timeReversalSign_smul_left (c : ℂ) (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    timeReversalSign (c • u) v = c ^ 2 * timeReversalSign u v := by
  rw [timeReversalSign, timeReversalSign, timeReversalTrace_smul_left]
  ring

namespace TimeReversalExamples

/-- The two-qubit index type `ℂ² ⊗ ℂ²`. -/
local notation "Q" => Fin 2 × Fin 2

/-- The four-qubit index type `(ℂ² ⊗ ℂ²) ⊗ (ℂ² ⊗ ℂ²)`. -/
local notation "Q₄" => (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The controlled-`Z` gate `CZ = diag(1, 1, 1, -1)` on `ℂ² ⊗ ℂ²`. -/
def controlledZ : Matrix Q Q ℂ := Matrix.diagonal fun p ↦ if p = (1, 1) then -1 else 1

/-! ### Integer models -/

/-- The exchange of the two pairs of sites, over `ℤ`. -/
private def pairSwapZ : Matrix Q₄ Q₄ ℤ :=
  Matrix.of fun p q ↦ if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- A gate on the two middle sites of four, over `ℤ`. -/
private def middleZ (M : Matrix Q Q ℤ) : Matrix Q₄ Q₄ ℤ :=
  Matrix.of fun p q ↦
    if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 then M (p.1.2, p.2.1) (q.1.2, q.2.1) else 0

/-- The controlled-`Z` gate over `ℤ`. -/
private def controlledZZ : Matrix Q Q ℤ :=
  Matrix.of fun p q ↦ if p = q then (if p = (1, 1) then -1 else 1) else 0

/-- The gate `X ⊗ X` over `ℤ`. -/
private def pauliXXZ : Matrix Q Q ℤ :=
  Matrix.of fun p q ↦ if p.1 = 1 - q.1 ∧ p.2 = 1 - q.2 then 1 else 0

/-- The time-reversal trace over `ℤ`. -/
private def timeReversalTraceZ (u v : Matrix Q Q ℤ) : ℤ :=
  (pairSwapZ * (middleZ v * (u ⊗ₖ u) * middleZ v)).trace

/-- The integer cast, as a ring homomorphism. -/
local notation "ι" => Int.castRingHom ℂ

private theorem pairSwap_eq_map :
    Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm (Matrix.swapMatrix (2 * 2)) =
      pairSwapZ.map ι := by
  ext p q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.prodCongr_apply, Prod.map, Matrix.swapMatrix_apply, EmbeddingLike.apply_eq_iff_eq,
    Matrix.map_apply, pairSwapZ, Matrix.of_apply]
  split_ifs <;> simp

private theorem staircaseMiddle_map (M : Matrix Q Q ℤ) :
    staircaseMiddle (A := Fin 2) (E := Fin 2) (M.map ι) = (middleZ M).map ι := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨a', b'⟩, ⟨c', e'⟩⟩
  simp only [staircaseMiddle, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.map_apply, middleZ, Matrix.of_apply]
  by_cases ha : a = a' <;> by_cases he : e = e' <;> simp [ha, he]

private theorem kronecker_map (u : Matrix Q Q ℤ) :
    u.map ι ⊗ₖ u.map ι = (u ⊗ₖ u).map ι := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

/-- The time-reversal trace of integer gates is the integer trace. -/
private theorem timeReversalTrace_map (u v : Matrix Q Q ℤ) :
    timeReversalTrace (u.map ι) (v.map ι) = ((timeReversalTraceZ u v : ℤ) : ℂ) := by
  rw [timeReversalTrace, pairSwap_eq_map, staircaseMiddle_map, kronecker_map,
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← AddMonoidHom.map_trace]
  rfl

private theorem controlledZ_eq_map : controlledZ = controlledZZ.map ι := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [controlledZ, controlledZZ]

private theorem pauliXX_eq_map : pauliX ⊗ₖ pauliX = pauliXXZ.map ι := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [pauliX, pauliXXZ, Matrix.kroneckerMap_apply]

private theorem one_eq_map : (1 : Matrix Q Q ℂ) = (1 : Matrix Q Q ℤ).map ι :=
  (Matrix.map_one _ (map_zero ι) (map_one ι)).symm

private theorem timeReversalTraceZ_czx :
    timeReversalTraceZ (controlledZZ * pauliXXZ) controlledZZ = -4 := by
  decide +kernel

private theorem timeReversalTraceZ_one : timeReversalTraceZ 1 1 = 4 := by
  decide +kernel

/-! ### The four signs -/

/-- **CZX.** The gates `u = CZ (X ⊗ X)` and `v = CZ` have trace sign `-1`.

Source: arXiv:1703.09188, example CZX, lines 1906--1943, with the sign of equation
`eq:sigma-from-trace`, lines 1595--1611; the source prints `σ⁽¹⁾ = -1`. -/
theorem timeReversalSign_czx :
    timeReversalSign (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ = -1 := by
  rw [timeReversalSign, pauliXX_eq_map, controlledZ_eq_map, ← Matrix.map_mul,
    timeReversalTrace_map, timeReversalTraceZ_czx]
  norm_num

/-- The gates `u = v = 1` have trace sign `1`.

Source: arXiv:1703.09188, lines 1945--1962, the first of the other three time-reversal
classes, with the sign of equation `eq:sigma-from-trace`; the source prints `σ⁽¹⁾ = 1`. -/
theorem timeReversalSign_one : timeReversalSign (1 : Matrix Q Q ℂ) 1 = 1 := by
  rw [timeReversalSign, one_eq_map, timeReversalTrace_map, timeReversalTraceZ_one]
  norm_num

/-- The gates `u = i 1` and `v = 1` have trace sign `-1`.

Source: arXiv:1703.09188, lines 1945--1962, the second of the other three time-reversal
classes, with the sign of equation `eq:sigma-from-trace`; the source prints `σ⁽¹⁾ = -1`. -/
theorem timeReversalSign_I_smul_one :
    timeReversalSign (Complex.I • (1 : Matrix Q Q ℂ)) 1 = -1 := by
  rw [timeReversalSign_smul_left, timeReversalSign_one, Complex.I_sq, mul_one]

/-- The gates `u = i CZ (X ⊗ X)` and `v = CZ` have trace sign `1`.

Source: arXiv:1703.09188, lines 1945--1962, the third of the other three time-reversal
classes, with the sign of equation `eq:sigma-from-trace`; the source prints `σ⁽¹⁾ = 1`. -/
theorem timeReversalSign_I_smul_czx :
    timeReversalSign (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX))) controlledZ = 1 := by
  rw [timeReversalSign_smul_left, timeReversalSign_czx, Complex.I_sq]
  norm_num

end TimeReversalExamples

end MPOTensor
