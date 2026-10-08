/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorLocality

/-! # Locality of the actual endpoint operators

The source inventory records the owner and order of each endpoint. The literal
operator word restricted to selected parties depends only on their endpoints.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–309 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-endpointinventorylocality-01
TNLean.PEPS.PairEffect.SourceInventory.restrict_endpointWord_eval_eq_of_agree
Provenance-ID: 8769-chronological-network-endpointinventorylocality-02
TNLean.PEPS.PairEffect.Word.restrict_castLayouts_eval_heq
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Word
/-- Layout transport preserves the restriction of an actual source-free word.
Source: polynomial-PEPS 04-compression.tex, lines 409–427. -/
theorem restrict_castLayouts_eval_heq (f : P → Bool) {a b a' b' : Layout P}
    (w : Word a b) (ha : a = a') (hb : b = b') (hs : w.sources = []) :
    HEq (((w.castLayouts ha hb).restrict f ((sources_castLayouts _ _ _).trans hs)).eval)
      ((w.restrict f hs).eval) := by
  cases ha
  cases hb
  rfl
end Word
namespace SourceInventory
/-- The actual endpoint word restricted to selected parties depends only on
endpoint operators owned by those parties. No cancellation of any complementary
operator is used. Source: polynomial-PEPS 04-compression.tex, lines 351–381
and 565–588. -/
theorem restrict_endpointWord_eval_eq_of_agree (f : P → Bool)
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A A' : ∀ i, U i →L[ℂ] U i) (B B' : ∀ i, V i →L[ℂ] V i)
    (hA : ∀ i, f (R.get i).left = true → A i = A' i)
    (hB : ∀ i, f (R.get i).right = true → B i = B' i) :
    ((endpointWord R U V A B).restrict f (sources_endpointWord _ _ _ _ _)).eval =
      ((endpointWord R U V A' B').restrict f (sources_endpointWord _ _ _ _ _)).eval := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      let ru : Reg P := ⟨r.left, U 0⟩
      let rv : Reg P := ⟨r.right, V 0⟩
      let tail := slotLayout R (fun i => U i.succ) (fun i => V i.succ)
      let wt := endpointWord R (fun i => U i.succ) (fun i => V i.succ)
        (fun i => A i.succ) (fun i => B i.succ)
      let wt' := endpointWord R (fun i => U i.succ) (fun i => V i.succ)
        (fun i => A' i.succ) (fun i => B' i.succ)
      have hwt : wt.sources = [] := sources_endpointWord _ _ _ _ _
      have hwt' : wt'.sources = [] := sources_endpointWord _ _ _ _ _
      have het : (wt.restrict f hwt).eval = (wt'.restrict f hwt').eval :=
        ih _ _ _ _ _ _ (fun i => hA i.succ) (fun i => hB i.succ)
      let vw := Word.comp (Word.localEndpoint rv (B 0) tail) (Word.frame rv wt)
      let vw' := Word.comp (Word.localEndpoint rv (B' 0) tail) (Word.frame rv wt')
      have hvw : vw.sources = [] := by
        simp only [vw, Word.sources, Word.sources_localEndpoint, hwt, List.nil_append]
      have hvw' : vw'.sources = [] := by
        simp only [vw', Word.sources, Word.sources_localEndpoint, hwt', List.nil_append]
      have hev : HEq ((vw.restrict f hvw).eval) ((vw'.restrict f hvw').eval) :=
        Word.restrict_comp_eval_heq f rfl rfl rfl
          (Word.localEndpoint rv (B 0) tail) (Word.localEndpoint rv (B' 0) tail)
          (Word.frame rv wt) (Word.frame rv wt')
          (Word.sources_localEndpoint _ _ _) (Word.sources_localEndpoint _ _ _) hwt hwt'
          (heq_of_eq (Word.restrict_localEndpoint_eval_eq_of_agree f rv _ _ tail (hB 0)))
          (Word.restrict_frame_eval_heq f rv rfl rfl _ _ hwt hwt' (heq_of_eq het))
      let zw := Word.comp (Word.localEndpoint ru (A 0) (rv :: tail)) (Word.frame ru vw)
      let zw' := Word.comp (Word.localEndpoint ru (A' 0) (rv :: tail)) (Word.frame ru vw')
      have hzw : zw.sources = [] := by
        simp only [zw, Word.sources, Word.sources_localEndpoint, hvw, List.nil_append]
      have hzw' : zw'.sources = [] := by
        simp only [zw', Word.sources, Word.sources_localEndpoint, hvw', List.nil_append]
      have hez : HEq ((zw.restrict f hzw).eval) ((zw'.restrict f hzw').eval) :=
        Word.restrict_comp_eval_heq f rfl rfl rfl
          (Word.localEndpoint ru (A 0) (rv :: tail))
          (Word.localEndpoint ru (A' 0) (rv :: tail)) (Word.frame ru vw) (Word.frame ru vw')
          (Word.sources_localEndpoint _ _ _) (Word.sources_localEndpoint _ _ _) hvw hvw'
          (heq_of_eq (Word.restrict_localEndpoint_eval_eq_of_agree f ru _ _ (rv :: tail) (hA 0)))
          (Word.restrict_frame_eval_heq f ru rfl rfl _ _ hvw hvw' hev)
      exact eq_of_heq ((Word.restrict_castLayouts_eval_heq f zw _ _ hzw).trans
        (hez.trans (Word.restrict_castLayouts_eval_heq f zw' _ _ hzw').symm))

end SourceInventory
end TNLean.PEPS.PairEffect
