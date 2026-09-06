/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXFusionTensors
import TNLean.MPS.MPDO.CZXActionTensors

/-!
# Explicit CZX fusion/action coordinates

The sequential printed action caps and the maintained product tensor determine
an explicit open-boundary proportionality coefficient. Its values are `1` and
`-1` in sectors `0` and `1`, respectively, and persist on every positive power
of the supported product letter.

**Scope restriction (explicit matrix coordinates):** These are contractions of
the literal caps/actions in arXiv:2502.20257, lines 4671–4694, motivated by
`eq:defL`, lines 1875–1913. They do not identify the coefficient with the paper's
L-symbol or its retained physical scalar. The density-label and Y-orientation
interpretations are separate questions; see
`docs/paper-gaps/fbc25_czx_fusion_coordinate_compatibility.tex`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace MPOTensor.CZX

/-- The sequential printed bra `p_(1-x) ⊗ p_x`, in `finProdFinEquiv` product-bond
order. Source: arXiv:2502.20257, lines 4690–4694. -/
def sequentialActionBra (x : Fin 2) : Matrix (Fin 1) (Fin 4) ℂ :=
  fun _ ab ↦ printedActionBra (1 - x) 0 ((finProdFinEquiv (m := 2) (n := 2)).symm ab).1 *
    printedActionBra x 0 ((finProdFinEquiv (m := 2) (n := 2)).symm ab).2

/-- The sequential printed ket `q_(1-x) ⊗ q_x`, in the same product-bond order.
Source: arXiv:2502.20257, lines 4690–4694. -/
def sequentialActionKet (x : Fin 2) : Matrix (Fin 4) (Fin 1) ℂ :=
  fun ab _ ↦ printedActionKet (1 - x) ((finProdFinEquiv (m := 2) (n := 2)).symm ab).1 0 *
    printedActionKet x ((finProdFinEquiv (m := 2) (n := 2)).symm ab).2 0

/-- The diagonal product-tensor letter supported by the blocked GHZ sector.
Source: arXiv:2502.20257, `eq:defL`, lines 1875–1913, specialized to the CZX
fusion/action data in lines 4671–4694. -/
def fusionActionLetter (x : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  mulTensor tensor tensor (finProdFinEquiv (x, x)) (finProdFinEquiv (x, x))

/-- The scalar obtained by contracting the sequential printed bra, one supported
product letter, and the maintained right fusion cap. Source: arXiv:2502.20257,
`eq:defL`, lines 1875–1913, and the literal caps/actions in lines 4671–4694. -/
def fusionActionCoefficient (x : Fin 2) : ℂ :=
  (sequentialActionBra x * fusionActionLetter x * fusionW) 0 0

set_option maxHeartbeats 800000 in
-- Only the two supported four-by-four product letters are evaluated.
private theorem fusionActionLetter_coordinates (x : Fin 2) :
    fusionActionLetter x = if x = 0 then
      !![0, 0, 0, 0; -1, 1, -1, 1; 0, 0, 0, 0; 0, 0, 0, 0]
    else !![0, 0, 0, 0; 0, 0, 0, 0; -1, -1, 1, 1; 0, 0, 0, 0] := by
  ext a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    norm_num [fusionActionLetter, mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.kroneckerMap_apply, Fin.sum_univ_four, tensor, blockTwo,
      decoratedSiteTensor, Matrix.mul_apply, Fin.sum_univ_two,
      finProdFinEquiv, Fin.divNat, Fin.modNat]

set_option maxHeartbeats 800000 in
-- The sparse letters reduce all four assertions to small complex coordinate calculations.
private theorem fusionAction_finite_calculation (x : Fin 2) :
    fusionActionCoefficient x = (if x = 0 then 1 else -1) ∧
    (sequentialActionBra x * fusionActionLetter x * sequentialActionKet x) 0 0 = 1 ∧
    fusionActionLetter x * fusionW =
      (if x = 0 then (1 : ℂ) else -1) • (fusionActionLetter x * sequentialActionKet x) ∧
    fusionActionLetter x * fusionActionLetter x = fusionActionLetter x := by
  unfold fusionActionCoefficient
  rw [fusionActionLetter_coordinates]
  fin_cases x <;> refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    first | apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j | skip
    all_goals
      norm_num +decide [sequentialActionBra, sequentialActionKet,
        printedActionBra, printedActionKet, fusionW, Matrix.mul_apply,
        Fin.sum_univ_four, finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.I_sq,
        Fin.reduceEq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecMul, dotProduct]
      <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The two values of the explicit fusion/action contraction. Source:
arXiv:2502.20257, literal caps/actions in lines 4671–4694. -/
theorem fusionActionCoefficient_coordinates :
    fusionActionCoefficient 0 = 1 ∧ fusionActionCoefficient 1 = -1 := by
  constructor
  · simpa using (fusionAction_finite_calculation 0).1
  · simpa using (fusionAction_finite_calculation 1).1

/-- Normalization, open-boundary proportionality, and idempotence for the actual
supported product letter and sequential printed caps. Source: arXiv:2502.20257,
`eq:defL`, lines 1875–1913, and the literal CZX data in lines 4671–4694. -/
theorem fusionAction_finite_identities (x : Fin 2) :
    (sequentialActionBra x * fusionActionLetter x * sequentialActionKet x) 0 0 = 1 ∧
    fusionActionLetter x * fusionW =
      fusionActionCoefficient x • (fusionActionLetter x * sequentialActionKet x) ∧
    fusionActionLetter x * fusionActionLetter x = fusionActionLetter x := by
  rw [(fusionAction_finite_calculation x).1]
  exact (fusionAction_finite_calculation x).2

/-- Positive repetitions of the supported letter preserve both contractions and
open-boundary proportionality. This is a matrix consequence of the literal CZX
caps/actions in arXiv:2502.20257, lines 4671–4694. -/
theorem fusionAction_positive_power (x : Fin 2) (n : ℕ) :
    fusionActionLetter x ^ (n + 1) = fusionActionLetter x ∧
    (sequentialActionBra x * fusionActionLetter x ^ (n + 1) * fusionW) 0 0 =
      fusionActionCoefficient x ∧
    (sequentialActionBra x * fusionActionLetter x ^ (n + 1) * sequentialActionKet x) 0 0 = 1 ∧
    fusionActionLetter x ^ (n + 1) * fusionW =
      fusionActionCoefficient x • (fusionActionLetter x ^ (n + 1) * sequentialActionKet x) := by
  have hp : fusionActionLetter x ^ (n + 1) = fusionActionLetter x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      exact (fusionAction_finite_identities x).2.2
  rw [hp]
  exact ⟨rfl, rfl, (fusionAction_finite_identities x).1,
    (fusionAction_finite_identities x).2.1⟩

end MPOTensor.CZX
