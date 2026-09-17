/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXSquare
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.StackedPairGauge
import TNLean.MPS.FundamentalTheorem.Reduction.Splitting

/-!
# The anomaly of the CZX symmetry as a failure of star closure

Example D of the P5 note
(`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`, `ex:p5ft-czx`) is a
multi-block compression with no sitewise intertwiner at all: the stacked product tensor of the
CZX symmetry compresses onto the weighted bond-one identity at the level of words, but both
sitewise intertwiner spaces vanish. By the splitting criterion this forces the virtual algebra of
the stacked tensor to fail to be closed under conjugate transposition, even though the physical
operator of the symmetry is unitary. This is the algebraic trace of the anomaly.

## Main results

* `CZXCompression.czxSquareTarget_isNormal`: the single target of Example D is normal.
* `CZXCompression.czxSquare_not_starClosed`: the virtual algebra of the stacked tensor is not
  closed under conjugate transposition.
-/

open scoped Matrix

namespace CZXCompression

open MPSTensor

private theorem negIdentityIntMPS_unit (x y : Fin 1) :
    negIdentityIntMPS ((fun _ _ => 0) x y) =
      ((fun _ _ => -1 : Fin 1 → Fin 1 → ℤ) x y) • Matrix.single x y 1 := by
  revert x y
  decide

/-- **The single target of Example D is normal**: its bond dimension is one and the letter `0`
acts by the nonzero scalar `-1`, so the one-site matrices already span the whole `1 x 1` matrix
algebra. -/
theorem czxSquareTarget_isNormal (s : Unit) : Kraus.IsNormal (czxSquareTarget s) :=
  P6Compression.isNormal_of_single_eq_smul negIdentityIntMPS (c := 1) one_ne_zero
    (fun a => by rw [czxSquareTarget_eq, one_smul]) (fun _ _ => 0) (fun _ _ => -1)
    (fun _ _ => by norm_num) negIdentityIntMPS_unit

/-- **The anomaly of the CZX symmetry is the failure of star closure of the virtual algebra**.
The stacked product tensor of Example D has no nonzero sitewise right intertwiner with its
target, so by the splitting criterion its virtual algebra is not closed under conjugate
transposition, although the physical operator of the symmetry is unitary. -/
theorem czxSquare_not_starClosed :
    ¬ ∀ i, (czxSquare i)ᴴ ∈ Algebra.adjoin ℂ (Set.range czxSquare) := by
  refine MPSTensor.not_forall_conjTranspose_mem_adjoin_of_forall_right_intertwiner_eq_zero
    squareSlots czxSquareTarget (fun s _ => czxSquareTarget_isNormal s)
    (fun _ _ => Nat.one_pos) czxSquare
    (fun w hw => czxSquare_compression.trace_evalWord_eq_sum w hw) squareSlot ?_
  intro X hX
  have hv : ∀ i, czxSquare i *ᵥ (fun x => X x 0) =
      czxSquareTarget () i 0 0 • (fun x => X x 0) := by
    intro i
    funext x
    have h := congrFun (congrFun (hX i) x) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_one] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact h.trans (mul_comm _ _)
  have hX0 := czxSquare_right_intertwiner_eq_zero (fun x => X x 0) hv
  ext x j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact congrFun hX0 x

end CZXCompression
