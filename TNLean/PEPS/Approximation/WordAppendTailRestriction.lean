/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordAppendTail
import TNLean.PEPS.Approximation.WordPermutationRestriction
import TNLean.Lattice.PartyCircuit.WordEvaluationTransport
import TNLean.PEPS.Approximation.FrameListRestriction

/-!
# Restriction beside retained spectator registers

Restricting a source-free composition extended by spectator registers gives
the restricted composition extended by precisely the retained spectators.
The input, output and spectator memories are arbitrary. In particular,
restriction does not require the spectator memory to disappear.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P : Type}

/-- The two-block exchange with its empty final memory identified. -/
private def twoBlockExchange (a b : Layout P) : Word (a ++ b) (b ++ a) :=
  (exchangeBlocks a b []).castLayouts (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a))

private theorem sources_twoBlockExchange (a b : Layout P) :
    (twoBlockExchange a b).sources = [] := by
  simp only [twoBlockExchange, sources_castLayouts, sources_exchangeBlocks]

private theorem restrict_twoBlockExchange_eval_heq (f : P → Bool) (a b : Layout P) :
    HEq ((twoBlockExchange a b).restrict f (sources_twoBlockExchange a b)).eval
      (twoBlockExchange (Layout.restrict f a) (Layout.restrict f b)).eval := by
  unfold twoBlockExchange
  rw [restrict_castLayouts f (exchangeBlocks a b [])
    (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a)) (sources_exchangeBlocks a b [])]
  exact (eval_castLayouts_heq
    ((exchangeBlocks a b []).restrict f (sources_exchangeBlocks a b [])) _ _).trans
      ((restrict_exchangeBlocks_eval_heq f a b []).trans
        (eval_castLayouts_heq
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b) [])
          (congrArg (Layout.restrict f a ++ ·) (List.append_nil (Layout.restrict f b)))
          (congrArg (Layout.restrict f b ++ ·) (List.append_nil (Layout.restrict f a)))).symm)

/-- Selection commutes with extending a source-free composition by spectator
registers: precisely the selected spectators remain beside the selected
composition. No empty-memory or operator-equality hypothesis is imposed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
409–434 and 565–588. -/
theorem restrict_appendTail_eval_heq (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (tail : Layout P) :
    HEq ((w.appendTail tail).restrict f ((sources_appendTail w tail).trans hs)).eval
      ((w.restrict f hs).appendTail (Layout.restrict f tail)).eval := by
  let u := twoBlockExchange a tail
  let v := frameList tail w
  let z := twoBlockExchange tail b
  let u' := twoBlockExchange (Layout.restrict f a) (Layout.restrict f tail)
  let v' := frameList (Layout.restrict f tail) (w.restrict f hs)
  let z' := twoBlockExchange (Layout.restrict f tail) (Layout.restrict f b)
  have hu : u.sources = [] := sources_twoBlockExchange a tail
  have hv : v.sources = [] := (sources_frameList w tail).trans hs
  have hz : z.sources = [] := sources_twoBlockExchange tail b
  have hvz : (v.comp z).sources = [] := by
    simp only [sources, hv, hz, List.nil_append]
  have hinner : HEq ((v.comp z).restrict f hvz).eval (v'.comp z').eval :=
    eval_comp_heq (v.restrict f hv) (z.restrict f hz) v' z'
      (Layout.restrict_append f tail a) (Layout.restrict_append f tail b)
      (Layout.restrict_append f b tail)
      (restrict_frameList_eval_heq f tail w hs)
      (restrict_twoBlockExchange_eval_heq f tail b)
  have houter := eval_comp_heq (u.restrict f hu) ((v.comp z).restrict f hvz)
    u' (v'.comp z')
    (Layout.restrict_append f a tail) (Layout.restrict_append f tail a)
    (Layout.restrict_append f b tail)
    (restrict_twoBlockExchange_eval_heq f a tail) hinner
  have hall : (u.comp (v.comp z)).sources = [] := by
    simp only [sources, hu, hv, hz, List.nil_append]
  change HEq ((u.comp (v.comp z)).restrict f hall).eval (u'.comp (v'.comp z')).eval
  exact houter

end TNLean.PEPS.PairEffect.Word
