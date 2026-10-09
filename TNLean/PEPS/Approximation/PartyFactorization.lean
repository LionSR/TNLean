/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Factorization of local operations across a partition of the parties

A composition containing no pair-source preparations acts independently on disjoint
sets of parties. Its two factors are the compositions obtained by retaining the
registers and local operations of the respective sets. The register identifications
are the canonical permutations preserving the order within each set.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 5.2, `eq:compression-source-gate`,
  `04-compression.tex`, lines 233–251.
  Revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

private theorem assoc_symm_mapL {E E' F F' G G' : HSpace}
    (a : E →L[ℂ] E') (b : F →L[ℂ] F') (c : G →L[ℂ] G')
    (x : E ⊗[ℂ] (F ⊗[ℂ] G)) :
    (TensorProduct.assocIsometry ℂ E' F' G').symm
        (TensorProduct.mapL a (TensorProduct.mapL b c) x) =
      TensorProduct.mapL (TensorProduct.mapL a b) c
        ((TensorProduct.assocIsometry ℂ E F G).symm x) := by
  refine DFunLike.congr_fun
    (f := isoL (TensorProduct.assocIsometry ℂ E' F' G').symm ∘L
      TensorProduct.mapL a (TensorProduct.mapL b c))
    (g := TensorProduct.mapL (TensorProduct.mapL a b) c ∘L
      isoL (TensorProduct.assocIsometry ℂ E F G).symm)
    (clm_ext_tmul₃ fun u v w ↦ ?_) x
  simp only [comp_apply, isoL_apply, TensorProduct.mapL_tmul,
    TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul]

private theorem leftComm_mapL {E E' F F' G G' : HSpace}
    (a : E →L[ℂ] E') (b : F →L[ℂ] F') (c : G →L[ℂ] G')
    (x : E ⊗[ℂ] (F ⊗[ℂ] G)) :
    leftCommL E' F' G' (TensorProduct.mapL a (TensorProduct.mapL b c) x) =
      TensorProduct.mapL b (TensorProduct.mapL a c) (leftCommL E F G x) := by
  refine DFunLike.congr_fun
    (f := leftCommL E' F' G' ∘L TensorProduct.mapL a (TensorProduct.mapL b c))
    (g := TensorProduct.mapL b (TensorProduct.mapL a c) ∘L leftCommL E F G)
    (clm_ext_tmul₃ fun u v w ↦ ?_) x
  simp only [comp_apply, TensorProduct.mapL_tmul, leftCommL_tmul]

private theorem mapL_apply_heq {A A' B B' C C' D D' : HSpace}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (a : A →L[ℂ] B) (a' : A' →L[ℂ] B') (b : C →L[ℂ] D) (b' : C' →L[ℂ] D')
    (ha : HEq a a') (hb : HEq b b') {x : A ⊗[ℂ] C} {x' : A' ⊗[ℂ] C'}
    (hx : HEq x x') : HEq (TensorProduct.mapL a b x) (TensorProduct.mapL a' b' x') := by
  cases hA
  cases hB
  cases hC
  cases hD
  cases ha
  cases hb
  cases hx
  rfl

variable {P : Type}

private theorem partitionIso_eval_swap (f : P → Bool) (r t : Reg P) (tail : Layout P) :
    isoL (Layout.partitionIso f (t :: r :: tail)) ∘L (Word.swap r t tail).eval =
      TensorProduct.mapL (Word.restrict f (Word.swap r t tail) rfl).eval
        (Word.restrict (fun p ↦ !f p) (Word.swap r t tail) rfl).eval ∘L
          isoL (Layout.partitionIso f (r :: t :: tail)) := by
  apply clm_ext_tmul₃
  intro x y z
  obtain ⟨z, rfl⟩ := (Layout.partitionIso f tail).symm.surjective z
  induction z using TensorProduct.inductionOn with
  | add u v hu hv =>
      simp only [map_add, TensorProduct.tmul_add]
      exact congrArg₂ (· + ·) hu hv
  | tmul a b =>
      simp only [comp_apply, isoL_apply, Word.eval, leftCommL_tmul]
      cases hr : f r.owner <;> cases ht : f t.owner
      · apply eq_of_heq
        refine (Layout.partitionIso_cons_cons_false_false_tmul f t r tail ht hr y x a b).trans ?_
        have hm := mapL_apply_heq
          (A := Mem (Layout.restrict f (r :: t :: tail)))
          (A' := Mem (Layout.restrict f tail))
          (B := Mem (Layout.restrict f (t :: r :: tail)))
          (B' := Mem (Layout.restrict f tail))
          (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: t :: tail)))
          (C' := Mem (r :: t :: Layout.restrict (fun p ↦ !f p) tail))
          (D := Mem (Layout.restrict (fun p ↦ !f p) (t :: r :: tail)))
          (D' := Mem (t :: r :: Layout.restrict (fun p ↦ !f p) tail))
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          _ _ _ _
          (Word.restrict_swap_false_false_eval_heq f r t tail hr ht)
          (Word.restrict_swap_true_true_eval_heq (fun p ↦ !f p) r t tail
            (by simp [hr]) (by simp [ht]))
          (Layout.partitionIso_cons_cons_false_false_tmul f r t tail hr ht x y a b)
        refine HEq.trans ?_ hm.symm
        simp only [TensorProduct.mapL_tmul, Word.eval, leftCommL_tmul, id_apply]
        rfl
      · apply eq_of_heq
        refine (Layout.partitionIso_cons_cons_true_false_tmul f t r tail ht hr y x a b).trans ?_
        have hm := mapL_apply_heq
          (A := Mem (Layout.restrict f (r :: t :: tail)))
          (A' := Mem (t :: Layout.restrict f tail))
          (B := Mem (Layout.restrict f (t :: r :: tail)))
          (B' := Mem (t :: Layout.restrict f tail))
          (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: t :: tail)))
          (C' := Mem (r :: Layout.restrict (fun p ↦ !f p) tail))
          (D := Mem (Layout.restrict (fun p ↦ !f p) (t :: r :: tail)))
          (D' := Mem (r :: Layout.restrict (fun p ↦ !f p) tail))
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          _ _ _ _
          (Word.restrict_swap_false_true_eval_heq f r t tail hr ht)
          (Word.restrict_swap_true_false_eval_heq (fun p ↦ !f p) r t tail
            (by simp [hr]) (by simp [ht]))
          (Layout.partitionIso_cons_cons_false_true_tmul f r t tail hr ht x y a b)
        refine HEq.trans ?_ hm.symm
        simp only [TensorProduct.mapL_tmul, id_apply]
        rfl
      · apply eq_of_heq
        refine (Layout.partitionIso_cons_cons_false_true_tmul f t r tail ht hr y x a b).trans ?_
        have hm := mapL_apply_heq
          (A := Mem (Layout.restrict f (r :: t :: tail)))
          (A' := Mem (r :: Layout.restrict f tail))
          (B := Mem (Layout.restrict f (t :: r :: tail)))
          (B' := Mem (r :: Layout.restrict f tail))
          (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: t :: tail)))
          (C' := Mem (t :: Layout.restrict (fun p ↦ !f p) tail))
          (D := Mem (Layout.restrict (fun p ↦ !f p) (t :: r :: tail)))
          (D' := Mem (t :: Layout.restrict (fun p ↦ !f p) tail))
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          _ _ _ _
          (Word.restrict_swap_true_false_eval_heq f r t tail hr ht)
          (Word.restrict_swap_false_true_eval_heq (fun p ↦ !f p) r t tail
            (by simp [hr]) (by simp [ht]))
          (Layout.partitionIso_cons_cons_true_false_tmul f r t tail hr ht x y a b)
        refine HEq.trans ?_ hm.symm
        simp only [TensorProduct.mapL_tmul, id_apply]
        rfl
      · apply eq_of_heq
        refine (Layout.partitionIso_cons_cons_true_true_tmul f t r tail ht hr y x a b).trans ?_
        have hm := mapL_apply_heq
          (A := Mem (Layout.restrict f (r :: t :: tail)))
          (A' := Mem (r :: t :: Layout.restrict f tail))
          (B := Mem (Layout.restrict f (t :: r :: tail)))
          (B' := Mem (t :: r :: Layout.restrict f tail))
          (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: t :: tail)))
          (C' := Mem (Layout.restrict (fun p ↦ !f p) tail))
          (D := Mem (Layout.restrict (fun p ↦ !f p) (t :: r :: tail)))
          (D' := Mem (Layout.restrict (fun p ↦ !f p) tail))
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          (by simp [Layout.restrict_cons, hr, ht])
          _ _ _ _
          (Word.restrict_swap_true_true_eval_heq f r t tail hr ht)
          (Word.restrict_swap_false_false_eval_heq (fun p ↦ !f p) r t tail
            (by simp [hr]) (by simp [ht]))
          (Layout.partitionIso_cons_cons_true_true_tmul f r t tail hr ht x y a b)
        refine HEq.trans ?_ hm.symm
        simp only [TensorProduct.mapL_tmul, Word.eval, leftCommL_tmul, id_apply]
        rfl

private theorem localMap_appendIso_symm {p : P} {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (U : Mem a →L[ℂ] Mem b) (tail : Layout P) (s : Mem a) (x : Mem tail) :
    (Word.localMap p ha hb U tail).eval ((appendIso a tail).symm (s ⊗ₜ x)) =
      (appendIso b tail).symm (U s ⊗ₜ x) := by
  simp [Word.eval]

/-- Partitioning registers by their owners factors a source-free word into its two
actual restrictions. Source: polynomial-PEPS manuscript, Theorem 5.2,
`eq:compression-source-gate`, lines 233–251. -/
theorem Word.partitionIso_eval (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) :
    isoL (Layout.partitionIso f ℓ') ∘L w.eval =
      TensorProduct.mapL (w.restrict f hs).eval (w.restrict (fun p ↦ !f p) hs).eval ∘L
        isoL (Layout.partitionIso f ℓ) := by
  induction w with
  | id ℓ => simp [Word.restrict, Word.eval]
  | comp w w' ih ih' =>
      simp only [Word.restrict, Word.eval_comp]
      rw [← comp_assoc, ih' (List.append_eq_nil_iff.mp hs).1, comp_assoc,
        ih (List.append_eq_nil_iff.mp hs).2, ← comp_assoc, ← TensorProduct.mapL_comp]
  | @localMap p a b ha hb U tail =>
      let e := (appendIso a tail).trans ((Layout.partitionIso f tail).lTensor (Mem a))
      suffices H :
          (isoL (Layout.partitionIso f (b ++ tail)) ∘L
            (Word.localMap p ha hb U tail).eval) ∘L isoL e.symm =
          (TensorProduct.mapL ((Word.localMap p ha hb U tail).restrict f rfl).eval
            ((Word.localMap p ha hb U tail).restrict (fun p ↦ !f p) rfl).eval ∘L
              isoL (Layout.partitionIso f (a ++ tail))) ∘L isoL e.symm by
        ext1 z
        obtain ⟨v, rfl⟩ := e.symm.surjective z
        exact DFunLike.congr_fun H v
      apply clm_ext_tmul₃
      intro s x y
      simp only [comp_apply, isoL_apply, e, LinearIsometryEquiv.symm_trans,
        LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_lTensor,
        iso_lTensor_apply, lTensor_tmul, localMap_appendIso_symm]
      cases hp : f p with
      | false =>
          apply eq_of_heq
          refine (Layout.partitionIso_append_false_tmul f b tail hb hp (U s) x y).trans ?_
          have hm := mapL_apply_heq
            (A := Mem (Layout.restrict f (a ++ tail)))
            (A' := Mem (Layout.restrict f tail))
            (B := Mem (Layout.restrict f (b ++ tail)))
            (B' := Mem (Layout.restrict f tail))
            (C := Mem (Layout.restrict (fun q ↦ !f q) (a ++ tail)))
            (C' := Mem (a ++ Layout.restrict (fun q ↦ !f q) tail))
            (D := Mem (Layout.restrict (fun q ↦ !f q) (b ++ tail)))
            (D' := Mem (b ++ Layout.restrict (fun q ↦ !f q) tail))
            (by rw [Layout.restrict_append, Layout.restrict_eq_nil_of_owner f ha hp]; rfl)
            (by rw [Layout.restrict_append, Layout.restrict_eq_nil_of_owner f hb hp]; rfl)
            (by rw [Layout.restrict_append,
              Layout.restrict_eq_self_of_owner (fun q ↦ !f q) ha (by simp [hp])])
            (by rw [Layout.restrict_append,
              Layout.restrict_eq_self_of_owner (fun q ↦ !f q) hb (by simp [hp])])
            _ _ _ _
            (Word.restrict_localMap_false_eval_heq f p ha hb U tail hp)
            (Word.restrict_localMap_true_eval_heq (fun q ↦ !f q) p ha hb U tail
              (by simp [hp]))
            (Layout.partitionIso_append_false_tmul f a tail ha hp s x y)
          refine HEq.trans ?_ hm.symm
          apply heq_of_eq
          simp only [TensorProduct.mapL_tmul, id_apply, localMap_appendIso_symm]
      | true =>
          apply eq_of_heq
          refine (Layout.partitionIso_append_true_tmul f b tail hb hp (U s) x y).trans ?_
          have hm := mapL_apply_heq
            (A := Mem (Layout.restrict f (a ++ tail)))
            (A' := Mem (a ++ Layout.restrict f tail))
            (B := Mem (Layout.restrict f (b ++ tail)))
            (B' := Mem (b ++ Layout.restrict f tail))
            (C := Mem (Layout.restrict (fun q ↦ !f q) (a ++ tail)))
            (C' := Mem (Layout.restrict (fun q ↦ !f q) tail))
            (D := Mem (Layout.restrict (fun q ↦ !f q) (b ++ tail)))
            (D' := Mem (Layout.restrict (fun q ↦ !f q) tail))
            (by rw [Layout.restrict_append, Layout.restrict_eq_self_of_owner f ha hp])
            (by rw [Layout.restrict_append, Layout.restrict_eq_self_of_owner f hb hp])
            (by rw [Layout.restrict_append,
              Layout.restrict_eq_nil_of_owner (fun q ↦ !f q) ha (by simp [hp])]; rfl)
            (by rw [Layout.restrict_append,
              Layout.restrict_eq_nil_of_owner (fun q ↦ !f q) hb (by simp [hp])]; rfl)
            _ _ _ _
            (Word.restrict_localMap_true_eval_heq f p ha hb U tail hp)
            (Word.restrict_localMap_false_eval_heq (fun q ↦ !f q) p ha hb U tail
              (by simp [hp]))
            (Layout.partitionIso_append_true_tmul f a tail ha hp s x y)
          refine HEq.trans ?_ hm.symm
          apply heq_of_eq
          simp only [TensorProduct.mapL_tmul, id_apply, localMap_appendIso_symm]
  | source => contradiction
  | swap r t tail => exact partitionIso_eval_swap f r t tail
  | @frame r a b w ih =>
      apply clm_ext_tmul
      intro x y
      cases hr : f r.owner with
      | false =>
          apply eq_of_heq
          refine (Layout.partitionIso_cons_false_tmul f r b hr x (w.eval y)).trans ?_
          have hm := mapL_apply_heq
            (A := Mem (Layout.restrict f (r :: a)))
            (A' := Mem (Layout.restrict f a))
            (B := Mem (Layout.restrict f (r :: b)))
            (B' := Mem (Layout.restrict f b))
            (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: a)))
            (C' := HSpace.of (r.space ⊗[ℂ] Mem (Layout.restrict (fun p ↦ !f p) a)))
            (D := Mem (Layout.restrict (fun p ↦ !f p) (r :: b)))
            (D' := HSpace.of (r.space ⊗[ℂ] Mem (Layout.restrict (fun p ↦ !f p) b)))
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            _ _ _ _
            (Word.restrict_frame_false_eval_heq f r w hs hr)
            (Word.restrict_frame_true_eval_heq (fun p ↦ !f p) r w hs (by simp [hr]))
            (Layout.partitionIso_cons_false_tmul f r a hr x y)
          refine HEq.trans ?_ hm.symm
          apply heq_of_eq
          rw [show Layout.partitionIso f b (w.eval y) =
            TensorProduct.mapL (w.restrict f hs).eval
              (w.restrict (fun p ↦ !f p) hs).eval (Layout.partitionIso f a y) from
            DFunLike.congr_fun (ih hs) y]
          simpa [leftCommL, TensorProduct.mapL_tmul, lTensor_eq_mapL] using
            leftComm_mapL (ContinuousLinearMap.id ℂ r.space) (w.restrict f hs).eval
              (w.restrict (fun p ↦ !f p) hs).eval (x ⊗ₜ Layout.partitionIso f a y)
      | true =>
          apply eq_of_heq
          refine (Layout.partitionIso_cons_true_tmul f r b hr x (w.eval y)).trans ?_
          have hm := mapL_apply_heq
            (A := Mem (Layout.restrict f (r :: a)))
            (A' := HSpace.of (r.space ⊗[ℂ] Mem (Layout.restrict f a)))
            (B := Mem (Layout.restrict f (r :: b)))
            (B' := HSpace.of (r.space ⊗[ℂ] Mem (Layout.restrict f b)))
            (C := Mem (Layout.restrict (fun p ↦ !f p) (r :: a)))
            (C' := Mem (Layout.restrict (fun p ↦ !f p) a))
            (D := Mem (Layout.restrict (fun p ↦ !f p) (r :: b)))
            (D' := Mem (Layout.restrict (fun p ↦ !f p) b))
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            (by rw [Layout.restrict_cons, hr]; rfl)
            _ _ _ _
            (Word.restrict_frame_true_eval_heq f r w hs hr)
            (Word.restrict_frame_false_eval_heq (fun p ↦ !f p) r w hs (by simp [hr]))
            (Layout.partitionIso_cons_true_tmul f r a hr x y)
          refine HEq.trans ?_ hm.symm
          apply heq_of_eq
          rw [show Layout.partitionIso f b (w.eval y) =
            TensorProduct.mapL (w.restrict f hs).eval
              (w.restrict (fun p ↦ !f p) hs).eval (Layout.partitionIso f a y) from
            DFunLike.congr_fun (ih hs) y]
          simpa only [TensorProduct.mapL_tmul, id_apply, lTensor_eq_mapL] using
            assoc_symm_mapL (ContinuousLinearMap.id ℂ r.space) (w.restrict f hs).eval
              (w.restrict (fun p ↦ !f p) hs).eval (x ⊗ₜ Layout.partitionIso f a y)

end TNLean.PEPS.PairEffect
