/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EndpointWordRestriction

/-! # Pointwise congruence of restricted endpoint words

Fix the source inventory, the endpoint spaces, and a selector of owners.
Changing an endpoint map at an unselected owner leaves the restricted word
unchanged. At selected owners the corresponding maps must agree. This is a
congruence statement for the actual endpoint operators; no local factorization
or equality of sampled averages is assumed.

The register order and spectator memories are fixed throughout. The maps and
spaces are arbitrary, including zero-dimensional spaces and an empty inventory.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588, pointwise endpoint locality.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

private theorem restrict_castLayouts_congr (f : P → Bool)
    {a b a' b' : Layout P} (u v : Word a b) (hu : u.sources = []) (hv : v.sources = [])
    (ha : a = a') (hb : b = b') (h : u.restrict f hu = v.restrict f hv) :
    (u.castLayouts ha hb).restrict f ((Word.sources_castLayouts u ha hb).trans hu) =
      (v.castLayouts ha hb).restrict f ((Word.sources_castLayouts v ha hb).trans hv) := by
  rw [Word.restrict_castLayouts f u ha hb hu,
    Word.restrict_castLayouts f v ha hb hv, h]

private theorem restrict_comp_congr (f : P → Bool) {a b c : Layout P}
    (u u' : Word a b) (v v' : Word b c)
    (hu : u.sources = []) (hu' : u'.sources = [])
    (hv : v.sources = []) (hv' : v'.sources = [])
    (h : u.restrict f hu = u'.restrict f hu')
    (h' : v.restrict f hv = v'.restrict f hv') :
    (u.comp v).restrict f (by simp only [Word.sources, hu, hv, List.nil_append]) =
      (u'.comp v').restrict f (by simp only [Word.sources, hu', hv', List.nil_append]) := by
  change (u.restrict f hu).comp (v.restrict f hv) =
    (u'.restrict f hu').comp (v'.restrict f hv')
  exact congrArg₂ Word.comp h h'

private theorem restrict_frame_congr (f : P → Bool) (r : Reg P) {a b : Layout P}
    (u v : Word a b) (hu : u.sources = []) (hv : v.sources = [])
    (h : u.restrict f hu = v.restrict f hv) :
    (Word.frame r u).restrict f hu = (Word.frame r v).restrict f hv := by
  simp only [Word.restrict]
  split <;> rw [h]

private theorem restrict_localEndpoint_congr (f : P → Bool) (r : Reg P)
    (A A' : r.space →L[ℂ] r.space) (tail : Layout P)
    (h : f r.owner = true → A = A') :
    (Word.localEndpoint r A tail).restrict f (Word.sources_localEndpoint r A tail) =
      (Word.localEndpoint r A' tail).restrict f (Word.sources_localEndpoint r A' tail) := by
  by_cases hr : f r.owner = true
  · rw [h hr]
  · simp only [Word.localEndpoint, Word.restrict, dite_eq_right hr]

private theorem restrict_endpointWord_eq_of_local_eq
    (f : P → Bool) (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A A' : ∀ i, U i →L[ℂ] U i) (B B' : ∀ i, V i →L[ℂ] V i)
    (hL : ∀ i, f (R.get i).left = true → A i = A' i)
    (hR : ∀ i, f (R.get i).right = true → B i = B' i) :
    (endpointWord R U V A B).restrict f (sources_endpointWord R U V A B) =
      (endpointWord R U V A' B').restrict f (sources_endpointWord R U V A' B') := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      have hTail := ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ A i.succ) (fun i ↦ A' i.succ)
        (fun i ↦ B i.succ) (fun i ↦ B' i.succ)
        (fun i ↦ hL i.succ) (fun i ↦ hR i.succ)
      have hLeft := restrict_localEndpoint_congr f ⟨r.left, U 0⟩ (A 0) (A' 0)
        (⟨r.right, V 0⟩ :: slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)) (hL 0)
      have hRight := restrict_localEndpoint_congr f ⟨r.right, V 0⟩ (B 0) (B' 0)
        (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)) (hR 0)
      unfold endpointWord
      refine restrict_castLayouts_congr f _ _ ?_ ?_
        (slotLayout_cons r R U V).symm (slotLayout_cons r R U V).symm ?_
      · simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
          List.nil_append]
      · simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
          List.nil_append]
      · apply restrict_comp_congr f <;>
          try simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
            List.nil_append]
        · exact hLeft
        · apply restrict_frame_congr f
          try simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
            List.nil_append]
          apply restrict_comp_congr f <;>
            try simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord]
          · exact hRight
          · exact restrict_frame_congr f _ _ _ _ _ hTail

/-- On a fixed source inventory, the restricted endpoint operator depends only
on the maps at selected endpoint owners. Equalities are required solely for
those endpoint maps, without a premise asserting equality of local factors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and
565–588, pointwise endpoint locality in the construction. -/
theorem restrict_endpointWord_eval_eq_of_local_eq
    (f : P → Bool) (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A A' : ∀ i, U i →L[ℂ] U i) (B B' : ∀ i, V i →L[ℂ] V i)
    (hL : ∀ i, f (R.get i).left = true → A i = A' i)
    (hR : ∀ i, f (R.get i).right = true → B i = B' i) :
    ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)).eval =
      ((endpointWord R U V A' B').restrict f (sources_endpointWord R U V A' B')).eval :=
  congrArg Word.eval (restrict_endpointWord_eq_of_local_eq f R U V A A' B B' hL hR)

end TNLean.PEPS.PairEffect.SourceInventory
