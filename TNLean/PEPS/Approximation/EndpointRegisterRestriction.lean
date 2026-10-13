/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorWord
import TNLean.PEPS.Approximation.WordStructuralCongruence
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-! # The retained endpoint maps in their original order

Restricting the actual endpoint word retains precisely the selected registers
and their endomorphisms, in the original order. The proof compares constructed
words before restriction and then follows the selected chronological operations.
Source vectors and normalization play no role.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309,
409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The ordered endpoint registers and their supplied endomorphisms, with the
left endpoint preceding the right endpoint at each source occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309
and 565–588. -/
def endpointRegisterData : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    (∀ i, U i →L[ℂ] U i) → (∀ i, V i →L[ℂ] V i) →
      List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))
  | [], _, _, _, _ => []
  | r :: R, U, V, A, B =>
      ⟨⟨r.left, U 0⟩, A 0⟩ :: ⟨⟨r.right, V 0⟩, B 0⟩ ::
        endpointRegisterData R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ A i.succ) (fun i ↦ B i.succ)

/-- Apply the recorded endomorphisms in register order, preserving every later
register as a spectator. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588. -/
def endpointRegisterWord : (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) →
    Word (D.map Sigma.fst) (D.map Sigma.fst)
  | [] => .id []
  | z :: D => (Word.localEndpoint z.1 z.2 (D.map Sigma.fst)).comp
      (Word.frame z.1 (endpointRegisterWord D))

/-- The word of an ordered list of endpoint endomorphisms introduces no pair
preparation. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 279–309 and 565–588. -/
theorem sources_endpointRegisterWord
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    (endpointRegisterWord D).sources = [] := by
  induction D with
  | nil => rfl
  | cons z D ih =>
      simp only [endpointRegisterWord, Word.sources, Word.sources_localEndpoint,
        ih, List.nil_append]

private theorem endpointRegisterData_layout (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    (endpointRegisterData R U V A B).map Sigma.fst = slotLayout R U V := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      simp only [endpointRegisterData, List.map_cons, slotLayout_cons,
        List.cons_append, List.nil_append, ih]

private theorem localEndpoint_word_heq (r : Reg P) (A : r.space →L[ℂ] r.space)
    {a b : Layout P} (h : a = b) :
    HEq (Word.localEndpoint r A a) (Word.localEndpoint r A b) := by
  cases h
  rfl

private theorem endpointWord_heq_registerWord (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    HEq (endpointWord R U V A B) (endpointRegisterWord (endpointRegisterData R U V A B)) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      let ru : Reg P := ⟨r.left, U 0⟩
      let rv : Reg P := ⟨r.right, V 0⟩
      have ht := (endpointRegisterData_layout R (fun i ↦ U i.succ)
        (fun i ↦ V i.succ) (fun i ↦ A i.succ) (fun i ↦ B i.succ)).symm
      have hv := Word.comp_heq (congrArg (rv :: ·) ht) (congrArg (rv :: ·) ht)
        (congrArg (rv :: ·) ht) (localEndpoint_word_heq rv (B 0) ht)
        (Word.frame_heq rv ht ht (ih _ _ _ _))
      have hu := Word.comp_heq (congrArg (ru :: ·) (congrArg (rv :: ·) ht))
        (congrArg (ru :: ·) (congrArg (rv :: ·) ht))
        (congrArg (ru :: ·) (congrArg (rv :: ·) ht))
        (localEndpoint_word_heq ru (A 0) (congrArg (rv :: ·) ht))
        (Word.frame_heq ru (congrArg (rv :: ·) ht) (congrArg (rv :: ·) ht) hv)
      unfold endpointWord
      exact (Word.castLayouts_heq _ _ _).trans hu

private theorem restrict_endpointRegisterLayout (f : P → Bool)
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    Layout.restrict f (D.map Sigma.fst) =
      (D.filter (fun z ↦ f z.1.owner)).map Sigma.fst := by
  simp only [Layout.restrict, List.filter_map, Function.comp_def]

/-- Filtering the endpoint data retains exactly the selected source registers,
with their original spaces and order. The supplied endpoint maps do not enter
the register-list identity. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–309, 409–434 and 565–588. -/
theorem endpointRegisterData_filter_layout (f : P → Bool) (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    ((endpointRegisterData R U V A B).filter (fun z ↦ f z.1.owner)).map Sigma.fst =
      Layout.restrict f (slotLayout R U V) := by
  exact (restrict_endpointRegisterLayout f (endpointRegisterData R U V A B)).symm.trans
    (congrArg (Layout.restrict f) (endpointRegisterData_layout R U V A B))

private theorem localEndpoint_eval_heq (r : Reg P) (A : r.space →L[ℂ] r.space)
    {a b : Layout P} (h : a = b) :
    HEq (Word.localEndpoint r A a).eval (Word.localEndpoint r A b).eval := by
  cases h
  rfl

private theorem restrict_endpointRegisterWord_eval_heq (f : P → Bool)
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    HEq ((endpointRegisterWord D).restrict f (sources_endpointRegisterWord D)).eval
      (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))).eval := by
  induction D with
  | nil => rfl
  | cons z D ih =>
      rcases z with ⟨r, A⟩
      let T := (D.filter (fun z ↦ f z.1.owner)).map Sigma.fst
      have ht := restrict_endpointRegisterLayout f D
      let u := (Word.localEndpoint r A (D.map Sigma.fst)).restrict f rfl
      let v := (Word.frame r (endpointRegisterWord D)).restrict f
        (sources_endpointRegisterWord D)
      by_cases hr : f r.owner = true
      · have hu : HEq u.eval (Word.localEndpoint r A T).eval :=
          (Word.restrict_localMap_true_eval_heq f r.owner (a := [r]) (b := [r])
            (by simp) (by simp)
            (A.rTensor ℂ) (D.map Sigma.fst) hr).trans (localEndpoint_eval_heq r A ht)
        have hv : HEq v.eval
            (Word.frame r (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner)))).eval :=
          (Word.restrict_frame_true_eval_heq f r (endpointRegisterWord D)
            (sources_endpointRegisterWord D) hr).trans
            (Word.eval_frame_heq r
              ((endpointRegisterWord D).restrict f (sources_endpointRegisterWord D))
              (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))) ht ht ih)
        have hcomp := Word.eval_comp_heq u v (Word.localEndpoint r A T)
          (Word.frame r (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))))
          (by simp only [Layout.restrict_cons, hr, ↓reduceIte, ht])
          (by simp only [Layout.restrict_cons, hr, ↓reduceIte, ht])
          (by simp only [Layout.restrict_cons, hr, ↓reduceIte, ht]) hu hv
        simp only [List.filter_cons, hr, ↓reduceIte]
        change HEq (u.comp v).eval
          ((Word.localEndpoint r A T).comp
            (Word.frame r (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))))).eval
        exact hcomp
      · have hr' := Bool.eq_false_iff.mpr hr
        have hu : HEq u.eval (Word.id T).eval :=
          (Word.restrict_localMap_false_eval_heq f r.owner (a := [r]) (b := [r])
            (by simp) (by simp)
            (A.rTensor ℂ) (D.map Sigma.fst) hr').trans (Word.eval_id_heq ht)
        have hv : HEq v.eval
            (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))).eval :=
          (Word.restrict_frame_false_eval_heq f r (endpointRegisterWord D)
            (sources_endpointRegisterWord D) hr').trans ih
        have hcomp := Word.eval_comp_heq u v (Word.id T)
          (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner)))
          (by simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte, ht])
          (by simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte, ht])
          (by simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte, ht]) hu hv
        simp only [List.filter_cons, hr', Bool.false_eq_true, ↓reduceIte]
        change HEq (u.comp v).eval
          (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))).eval
        exact hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id
          (endpointRegisterWord (D.filter (fun z ↦ f z.1.owner))).eval))

/-- The actual restricted endpoint operator is the chronological word of
precisely its selected endpoint maps, preserving their original spaces and
order. The inventory and endomorphisms are arbitrary, including empty lists,
zero-dimensional spaces and zero maps. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–309, 409–434 and 565–588. -/
theorem restrict_endpointWord_eval_heq_registerWord (f : P → Bool)
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    HEq ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)).eval
      (endpointRegisterWord
        ((endpointRegisterData R U V A B).filter (fun z ↦ f z.1.owner))).eval := by
  let D := endpointRegisterData R U V A B
  have hL := endpointRegisterData_layout R U V A B
  have hWord : endpointWord R U V A B = (endpointRegisterWord D).castLayouts hL hL :=
    eq_of_heq ((endpointWord_heq_registerWord R U V A B).trans
      (Word.castLayouts_heq (endpointRegisterWord D) hL hL).symm)
  rw [hWord, Word.restrict_castLayouts f (endpointRegisterWord D) hL hL
    (sources_endpointRegisterWord D)]
  exact (Word.eval_castLayouts_heq _ _ _).trans
    (restrict_endpointRegisterWord_eval_heq f D)

end TNLean.PEPS.PairEffect.SourceInventory
