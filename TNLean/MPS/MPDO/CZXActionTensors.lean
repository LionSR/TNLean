/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.MPDO.CZXGHZAction

/-!
# The printed CZX action tensors on blocked GHZ sectors

The bra and ket are those of arXiv:2502.20257, `main.tex` lines 4690–4694,
with normalized plus/minus states. The directions follow `Commands.tex`
`ALl`/`ARl`: the interior is bra–acted word–ket.

**Scope restriction:** the printed pair satisfies `eq:action_interior`
(lines 1841–1870) only for nonempty words. Its empty contraction is one half
of the identity, not the identity. The finite witness below records this
obstruction explicitly; see `docs/paper-gaps/fbc25_czx_action_empty_word.tex`.
The exterior equation `eq:action_exterior`
(lines 1788–1838) is proved with nonempty buffers and nonempty middle.
No claim about unbuffered defect formulas or action existence is made.
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.CZX

/-- The actual once-blocked GHZ sector in the maintained CZX physical order.
Source: arXiv:2502.20257, lines 4660–4670. -/
def blockedSector (x : Fin 2) : MPSTensor 4 1 :=
  Kraus.reindexPhysical (twoSiteBlockEquiv 2)
    (MPSTensor.blockTensor (MPSTensor.ghzSectorTensor x) 2)

/-- Direct physical contraction of the shared CZX tensor with a bond-one
blocked GHZ sector; no MPO multiplication is used. -/
def actedSector (x : Fin 2) : MPSTensor 4 2 :=
  fun i l r ↦ ∑ j, tensor i j l r * blockedSector x j 0 0

/-- The actual target sector, with the two GHZ labels exchanged. -/
def actionTarget (x : Fin 2) : MPSTensor 4 1 := blockedSector (1 - x)

/-- The unique supported output letter of the action on sector `x`. -/
def actionLetter (x : Fin 2) : Fin 4 := finProdFinEquiv (1 - x, 1 - x)

/-- The supported matrix is an evaluation of the shared CZX tensor. -/
def actionMatrix (x : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  tensor (actionLetter x) (finProdFinEquiv (x, x))

/-- The printed bra $p_0=(0,-i)$, $p_1=(1,0)$.
Source: arXiv:2502.20257, lines 4690–4694. -/
def printedActionBra (x : Fin 2) : Matrix (Fin 1) (Fin 2) ℂ :=
  fun _ ↦ if x = 0 then ![0, -Complex.I] else ![1, 0]

/-- The printed ket $q_0=(-i,i)^T/2$, $q_1=(1,1)^T/2$.
Source: arXiv:2502.20257, lines 4690–4694 (normalized plus/minus states). -/
def printedActionKet (x : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ ↦ if x = 0 then ![-Complex.I / 2, Complex.I / 2] i else 1 / 2

private theorem blockedSector_apply (x : Fin 2) (i : Fin 4) :
    blockedSector x i = if i = finProdFinEquiv (x, x) then 1 else 0 :=
  blockTensor_ghzSectorTensor_apply x i

/-- Sparse support of the actual physical contraction. -/
theorem actedSector_apply (x : Fin 2) (i : Fin 4) :
    actedSector x i = if i = actionLetter x then actionMatrix x else 0 := by
  ext l r
  simp only [actedSector, blockedSector_apply, Matrix.ite_apply,
    Matrix.one_apply_eq, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases x <;> fin_cases i <;> fin_cases l <;> fin_cases r <;>
    norm_num [actionLetter, actionMatrix, tensor, blockTwo, decoratedSiteTensor,
      Matrix.mul_apply, Fin.sum_univ_two, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Sparse support of the actual reindexed target sector. -/
theorem actionTarget_apply (x : Fin 2) (i : Fin 4) :
    actionTarget x i = if i = actionLetter x then 1 else 0 :=
  blockedSector_apply (1 - x) i

/-- Coordinates of the two named evaluations of the shared tensor. -/
theorem actionMatrix_coordinates :
    actionMatrix 0 = !![0, 0; -1, 1] ∧
    actionMatrix 1 = !![1, 1; 0, 0] := by
  constructor <;> ext l r <;> fin_cases l <;> fin_cases r <;>
    norm_num [actionMatrix, actionLetter, tensor, blockTwo, decoratedSiteTensor,
      Matrix.mul_apply, Fin.sum_univ_two, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Kernel-checked local identities for the printed pair. In particular its
empty contraction differs from its one-letter contraction. -/
theorem printedAction_finite_identities (x : Fin 2) :
    actionMatrix x * actionMatrix x = actionMatrix x ∧
    printedActionBra x * printedActionKet x = (1 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
    printedActionBra x * actionMatrix x * printedActionKet x = 1 ∧
    actionMatrix x * printedActionKet x * printedActionBra x * actionMatrix x =
      actionMatrix x := by
  have hC : actionMatrix x = if x = 0 then !![0, 0; -1, 1] else !![1, 1; 0, 0] := by
    fin_cases x
    · exact actionMatrix_coordinates.1
    · exact actionMatrix_coordinates.2
  rw [hC]
  fin_cases x <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [printedActionBra, printedActionKet, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_sq, Matrix.one_apply, Matrix.vecMul, dotProduct] <;>
    ring_nf <;> norm_num [Complex.I_sq]

private theorem evalWord_sparse {D : ℕ} (A : MPSTensor 4 D)
    (k : Fin 4) (C : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ i, A i = if i = k then C else 0) (hC : C * C = C)
    (w : List (Fin 4)) (hw : w ≠ []) :
    Kraus.evalWord A w = if ∀ i ∈ w, i = k then C else 0 := by
  classical
  induction w with
  | nil => contradiction
  | cons i w ih =>
    cases w with
    | nil => simp [hA]
    | cons j w =>
      rw [Kraus.evalWord_cons, hA, ih (by simp), ite_zero_mul_ite_zero, hC]
      simp

/-- All nonempty acted words are either zero or the supported idempotent. -/
theorem evalWord_actedSector (x : Fin 2) (w : List (Fin 4)) (hw : w ≠ []) :
    Kraus.evalWord (actedSector x) w =
      if ∀ i ∈ w, i = actionLetter x then actionMatrix x else 0 :=
  evalWord_sparse _ _ _ (actedSector_apply x) (printedAction_finite_identities x).1 w hw

/-- All nonempty target words are either zero or the bond-one identity. -/
theorem evalWord_actionTarget (x : Fin 2) (w : List (Fin 4)) (hw : w ≠ []) :
    Kraus.evalWord (actionTarget x) w =
      if ∀ i ∈ w, i = actionLetter x then 1 else 0 :=
  evalWord_sparse _ _ _ (actionTarget_apply x) (one_mul _) w hw

/-- Literal printed interior equation on nonempty words, arXiv:2502.20257,
`eq:action_interior`. The empty word is explicitly excluded. -/
theorem printedAction_interior (x : Fin 2) (w : List (Fin 4)) (hw : w ≠ []) :
    printedActionBra x * Kraus.evalWord (actedSector x) w * printedActionKet x =
      Kraus.evalWord (actionTarget x) w := by
  rw [evalWord_actedSector x w hw, evalWord_actionTarget x w hw]
  split_ifs
  · exact (printedAction_finite_identities x).2.2.1
  · simp

/-- Literal printed buffered exterior equation, arXiv:2502.20257,
`eq:action_exterior`. Both buffers and the middle are nonempty. -/
theorem printedAction_exterior (x : Fin 2) (a c b : List (Fin 4))
    (ha : a ≠ []) (hc : c ≠ []) (hb : b ≠ []) :
    Kraus.evalWord (actedSector x) a * printedActionKet x *
      Kraus.evalWord (actionTarget x) c * printedActionBra x *
      Kraus.evalWord (actedSector x) b =
      Kraus.evalWord (actedSector x) (a ++ c ++ b) := by
  rw [Kraus.evalWord_append, Kraus.evalWord_append,
    evalWord_actedSector x a ha, evalWord_actedSector x b hb,
    evalWord_actedSector x c hc, evalWord_actionTarget x c hc]
  split_ifs <;> simp_all only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    (printedAction_finite_identities x).1, (printedAction_finite_identities x).2.2.2]

/-- Finite counterexample to the printed empty-word interior equation. -/
theorem printedAction_empty_ne (x : Fin 2) :
    printedActionBra x * Kraus.evalWord (actedSector x) [] * printedActionKet x ≠
      Kraus.evalWord (actionTarget x) [] := by
  simp only [Kraus.evalWord_nil, Matrix.mul_one]
  rw [(printedAction_finite_identities x).2.1]
  intro h
  have := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ ↦ M 0 0) h
  norm_num at this

/-- Consequently the literal printed pair is not an all-word reduction. -/
theorem printedAction_not_isReduction (x : Fin 2) :
    ¬ MPSTensor.IsReduction (actedSector x) (actionTarget x)
      (printedActionBra x) (printedActionKet x) :=
  fun h ↦ printedAction_empty_ne x (h.evalWord [])

/-- A separately dressed bra, obtained by absorbing the actual supported
exterior letter. This is not the printed bra or a scalar gauge choice and
must not replace it in unbuffered defect formulas. -/
def dressedActionBra (x : Fin 2) : Matrix (Fin 1) (Fin 2) ℂ :=
  printedActionBra x * actionMatrix x

/-- Dressing is invisible when followed by a nonempty actual acted word. -/
theorem dressedActionBra_absorption (x : Fin 2) (b : List (Fin 4)) (hb : b ≠ []) :
    dressedActionBra x * Kraus.evalWord (actedSector x) b =
      printedActionBra x * Kraus.evalWord (actedSector x) b := by
  rw [evalWord_actedSector x b hb]
  split_ifs
  · rw [dressedActionBra, Matrix.mul_assoc, (printedAction_finite_identities x).1]
  · simp

/-- The separately dressed pair, unlike the printed pair, is an all-word
reduction. This algebraic construction does not assert the printed
empty-word equation of arXiv:2502.20257, `eq:action_interior`. -/
theorem dressedAction_isReduction (x : Fin 2) :
    MPSTensor.IsReduction (actedSector x) (actionTarget x)
      (dressedActionBra x) (printedActionKet x) := by
  refine ⟨(printedAction_finite_identities x).2.2.1, fun w ↦ ?_⟩
  by_cases hw : w = []
  · subst w
    simpa only [Kraus.evalWord_nil, Matrix.mul_one, dressedActionBra] using
      (printedAction_finite_identities x).2.2.1
  · rw [dressedActionBra_absorption x w hw]
    exact printedAction_interior x w hw

/-- The dressed reduction has exterior buffer length one. The proof uses
absorption into the actual right exterior word, not a change of the
unbuffered printed action tensor. -/
theorem dressedAction_isReductionExteriorBufferLength (x : Fin 2) :
    MPSTensor.IsReductionExteriorBufferLength (actedSector x) (actionTarget x)
      (dressedActionBra x) (printedActionKet x) 1 := by
  intro a c b hc ha hb
  have ha' : a ≠ [] := by intro h; simp [h] at ha
  have hb' : b ≠ [] := by intro h; simp [h] at hb
  rw [Matrix.mul_assoc _ (dressedActionBra x), dressedActionBra_absorption x b hb',
    ← Matrix.mul_assoc]
  exact printedAction_exterior x a c b ha' hc hb'

end MPOTensor.CZX
