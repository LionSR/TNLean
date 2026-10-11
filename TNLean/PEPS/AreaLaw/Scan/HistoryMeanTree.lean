/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.HistoryWeights
import QICLean.Analysis.Transport.Derivative
import Mathlib.Data.Fintype.EquivFin

/-!
# Recursive mean trees for actual scanner histories

The initial offsets and each simultaneous padded charge choice have an explicit
finite uniform binary tree. A subsequent history tree is formed by substituting
that charge tree at every leaf of the preceding tree. The tree shape is retained:
equal classical distributions would not justify replacing a matrix mean tree.
A deterministic fill uses one leaf and introduces no additional random branch.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154, and `06-transport.tex`, lines 270–286.
This constructs classical trees and their matrix endpoint identities only; it
does not construct the pre-vector or identify transported entropy measures.
-/

open scoped unitInterval ComplexOrder MatrixOrder
open Matrix

namespace TNLean.PEPS.AreaLaw.Scan

private noncomputable def tailProbability (n : ℕ) : unitInterval :=
  ⟨(n + 1 : ℝ) / (n + 2), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < n + 2)).2
      linarith⟩

private noncomputable def uniformFin : (n : ℕ) → MeanTree (Fin (n + 1))
  | 0 => .leaf 0
  | n + 1 => .node (tailProbability n) (.leaf 0) ((uniformFin n).map Fin.succ)

private theorem uniformFin_weight (n : ℕ) (i : Fin (n + 1)) :
    (uniformFin n).weight i = 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => simp [uniformFin, Fin.eq_zero i]
  | succ n ih =>
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [uniformFin, MeanTree.weight_node,
        MeanTree.weight_map_of_forall_ne _ (by intro j; exact Fin.succ_ne_zero j)]
      simp only [MeanTree.weight_leaf, Pi.single_eq_same, mul_one, mul_zero, add_zero]
      dsimp [tailProbability]
      push_cast
      field_simp [hn1, hn2]
      ring
    · rw [uniformFin, MeanTree.weight_node,
        MeanTree.weight_map_apply _ (Fin.succ_injective _), ih]
      simp only [MeanTree.weight_leaf, Pi.single_eq_of_ne (Fin.succ_ne_zero j),
        mul_zero, zero_add]
      dsimp [tailProbability]
      push_cast
      field_simp [hn1, hn2]
      ring

private noncomputable def finiteUniform (α : Type*) [Fintype α] [Nonempty α] : MeanTree α :=
  let e := (Fintype.equivFin α).symm
  let h : Fintype.card α - 1 + 1 = Fintype.card α :=
    Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)
  (uniformFin (Fintype.card α - 1)).map fun i ↦ e (Fin.cast h i)

private theorem finiteUniform_weight (α : Type*) [Fintype α] [Nonempty α]
    [DecidableEq α] (a : α) :
    (finiteUniform α).weight a = 1 / (Fintype.card α : ℝ) := by
  have h : Fintype.card α - 1 + 1 = Fintype.card α :=
    Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)
  let i : Fin (Fintype.card α - 1 + 1) := Fin.cast h.symm (Fintype.equivFin α a)
  have he : (Fintype.equivFin α).symm (Fin.cast h i) = a := by simp [i]
  change ((uniformFin (Fintype.card α - 1)).map
    (fun j ↦ (Fintype.equivFin α).symm (Fin.cast h j))).weight a = _
  have hinj : Function.Injective (fun j : Fin (Fintype.card α - 1 + 1) ↦
      (Fintype.equivFin α).symm (Fin.cast h j)) :=
    (Fintype.equivFin α).symm.injective.comp (Fin.cast_injective h)
  rw [← he, MeanTree.weight_map_apply _ hinj, uniformFin_weight]
  have hc : ((Fintype.card α - 1 : ℕ) : ℝ) + 1 = Fintype.card α := by
    exact_mod_cast h
  rw [hc]

/-- The fixed uniform tree for one actual simultaneous charge, including blank
slots and repeated labels. Positive capacity makes its leaf type nonempty. -/
noncomputable def chargeChoiceTree (K M : ℕ) (hM : 0 < M) : MeanTree (ChargeChoices K M) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact finiteUniform (ChargeChoices K M)

/-- Every concrete charge leaf has its actual classical probability. -/
theorem chargeChoiceTree_weight (K M : ℕ) (hM : 0 < M) (c : ChargeChoices K M) :
    (chargeChoiceTree K M hM).weight c = chargeWeight c := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rw [chargeChoiceTree, finiteUniform_weight]
  simp only [ChargeChoices, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, chargeWeight]
  rw [_root_.one_div_pow]

/-- Initial offsets are sampled once; every subsequent tree is obtained by
substitution at the existing leaves, never by reassociating matrix means. -/
noncomputable def historyMeanTree (K m M : ℕ) (hm : 0 < m) (hM : 0 < M) :
    (k : ℕ) → MeanTree (History K m M k)
  | 0 => by
    letI : Nonempty (History K m M 0) := ⟨(fun _ ↦ ⟨0, hm⟩, Fin.elim0)⟩
    exact finiteUniform (History K m M 0)
  | k + 1 => (historyMeanTree K m M hm hM k).bind fun h ↦
      (chargeChoiceTree K M hM).map (extendHistory h)

private theorem extendHistory_injective {K m M k : ℕ} (h : History K m M k) :
    Function.Injective (extendHistory h) := by
  intro a b hab
  have he := congrArg (fun x : History K m M (k + 1) ↦ x.2 (Fin.last k)) hab
  simpa [extendHistory] using he

private theorem extendHistory_old_eq {K m M k : ℕ} {h h' : History K m M k}
    {c c' : ChargeChoices K M} (he : extendHistory h c = extendHistory h' c') : h = h' := by
  apply Prod.ext
  · have hh := congrArg (fun x : History K m M (k + 1) ↦ x.1) he
    exact hh
  · funext i
    have hi := congrArg (fun x : History K m M (k + 1) ↦ x.2 i.castSucc) he
    simpa [extendHistory] using hi

/-- The recursive tree retains exactly the product probability of each physical
history, not merely total probability one. -/
theorem historyMeanTree_weight (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (h : History K m M k) :
    (historyMeanTree K m M hm hM k).weight h = historyWeight h := by
  induction k with
  | zero =>
    let : Nonempty (History K m M 0) := ⟨(fun _ ↦ ⟨0, hm⟩, Fin.elim0)⟩
    rw [historyMeanTree, finiteUniform_weight]
    simp [historyWeight, Nat.cast_pow]
  | succ k ih =>
    let old : History K m M k := (h.1, Fin.init h.2)
    let c := h.2 (Fin.last k)
    have he : extendHistory old c = h := by
      apply Prod.ext
      · rfl
      · exact Fin.snoc_init_self h.2
    rw [← he, historyMeanTree,
      MeanTree.weight_bind_of_forall_ne _ (h₀ := old)]
    · rw [MeanTree.weight_map_apply _ (extendHistory_injective old), ih,
        chargeChoiceTree_weight, historyWeight_extendHistory]
    · intro h' hh'
      exact MeanTree.weight_map_of_forall_ne _ fun c' he' ↦
        hh' (extendHistory_old_eq he')

/-- A deterministic fill has exactly one conditional choice. -/
def fillChoiceTree : MeanTree Unit := .leaf ()

/-- Deterministic fills carry conditional probability one. -/
@[simp] theorem fillChoiceTree_weight : fillChoiceTree.weight () = 1 := by
  simp [fillChoiceTree]

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The next root is the old history tree evaluated at its conditional charge
roots. This is substitution, not associativity of geometric means. -/
theorem historyMeanTree_eval_succ (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (A : History K m M (k + 1) → Matrix N N ℂ) :
    (historyMeanTree K m M hm hM (k + 1)).eval A =
      (historyMeanTree K m M hm hM k).eval
        (fun h ↦ (chargeChoiceTree K M hM).eval (fun c ↦ A (extendHistory h c))) := by
  simp only [historyMeanTree, MeanTree.eval_bind, MeanTree.eval_map, Function.comp_def]

/-- The singleton fill tree evaluates to the actual deterministic new input. -/
@[simp] theorem fillChoiceTree_eval (A : Unit → Matrix N N ℂ) :
    fillChoiceTree.eval A = A () := rfl

/-- At the old endpoint, the interpolating charge tree has exactly the old
history root. Positive definiteness is needed by the matrix mean endpoint law. -/
theorem charge_interpRoot_zero (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (A : History K m M k → Matrix N N ℂ)
    (B : History K m M (k + 1) → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (historyMeanTree K m M hm hM k)
      (fun _ ↦ chargeChoiceTree K M hM) A (fun h c ↦ B (extendHistory h c)) 0 =
        (historyMeanTree K m M hm hM k).eval A := by
  unfold Matrix.Transport.interpRoot MeanTree.interpTree
  rw [MeanTree.eval_bind]
  congr 1
  funext h
  simp only [MeanTree.eval_node, MeanTree.eval_leaf, MeanTree.eval_map,
    Matrix.Transport.interpInput, Function.comp_def]
  exact Matrix.geomMean_zero (hA h)
    (MeanTree.posDef_eval (fun c ↦ hB (extendHistory h c)) _)

/-- At the new endpoint, the interpolating root is exactly the recursively
constructed next history root. Matching distributions alone is not used. -/
theorem charge_interpRoot_one (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (A : History K m M k → Matrix N N ℂ)
    (B : History K m M (k + 1) → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (historyMeanTree K m M hm hM k)
      (fun _ ↦ chargeChoiceTree K M hM) A (fun h c ↦ B (extendHistory h c)) 1 =
        (historyMeanTree K m M hm hM (k + 1)).eval B := by
  rw [historyMeanTree_eval_succ]
  unfold Matrix.Transport.interpRoot MeanTree.interpTree
  rw [MeanTree.eval_bind]
  congr 1
  funext h
  simp only [MeanTree.eval_node, MeanTree.eval_leaf, MeanTree.eval_map,
    Matrix.Transport.interpInput, Function.comp_def]
  exact Matrix.geomMean_one (hA h)
    (MeanTree.posDef_eval (fun c ↦ hB (extendHistory h c)) _)

/-- The new endpoint of a deterministic fill keeps the same history tree and
changes only its leaf inputs. Thus it is the old tree of the following charge. -/
theorem fill_interpRoot_one (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (A B : History K m M k → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (historyMeanTree K m M hm hM k)
      (fun _ ↦ fillChoiceTree) A (fun h _ ↦ B h) 1 =
        (historyMeanTree K m M hm hM k).eval B := by
  unfold Matrix.Transport.interpRoot MeanTree.interpTree
  rw [MeanTree.eval_bind]
  congr 1
  funext h
  simp only [MeanTree.eval_node, MeanTree.eval_leaf, MeanTree.eval_map,
    Matrix.Transport.interpInput, Function.comp_def, fillChoiceTree_eval]
  exact Matrix.geomMean_one (hA h) (hB h)

/-- The old endpoint of a deterministic fill is the preceding completed root. -/
theorem fill_interpRoot_zero (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (A B : History K m M k → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (historyMeanTree K m M hm hM k)
      (fun _ ↦ fillChoiceTree) A (fun h _ ↦ B h) 0 =
        (historyMeanTree K m M hm hM k).eval A := by
  unfold Matrix.Transport.interpRoot MeanTree.interpTree
  rw [MeanTree.eval_bind]
  congr 1
  funext h
  simp only [MeanTree.eval_node, MeanTree.eval_leaf, MeanTree.eval_map,
    Matrix.Transport.interpInput, Function.comp_def, fillChoiceTree_eval]
  exact Matrix.geomMean_zero (hA h) (hB h)

/-- The terminal old leaf has its actual history mass times the old-edge weight. -/
theorem historyMeanTree_interp_weight_old (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (p : unitInterval) (h : History K m M k) :
    (MeanTree.interpTree (historyMeanTree K m M hm hM k)
      (fun _ ↦ chargeChoiceTree K M hM) p).weight ⟨h, none⟩ =
        (1 - (p : ℝ)) * historyWeight h := by
  rw [MeanTree.weight_interpTree_old, historyMeanTree_weight]

/-- The terminal new leaf has the exact history-times-charge probability. -/
theorem historyMeanTree_interp_weight_new (K m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (k : ℕ) (p : unitInterval) (h : History K m M k) (c : ChargeChoices K M) :
    (MeanTree.interpTree (historyMeanTree K m M hm hM k)
      (fun _ ↦ chargeChoiceTree K M hM) p).weight ⟨h, some c⟩ =
        (p : ℝ) * historyWeight h * chargeWeight c := by
  rw [MeanTree.weight_interpTree_new, historyMeanTree_weight, chargeChoiceTree_weight]

end TNLean.PEPS.AreaLaw.Scan
