/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction
import TNLean.PEPS.Approximation.SourcePreparationCoordinates

/-! # Locality of the actual endpoint operators

The source inventory records the owner and order of each endpoint. The literal
operator word restricted to selected parties depends only on their endpoints.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Word
/-- Apply an actual endpoint operator to one register, leaving the other
registers as spectators. Source: polynomial-PEPS 04-compression.tex, lines 279–309. -/
def localEndpoint (r : Reg P) (A : r.space →L[ℂ] r.space) (tail : Layout P) :
    Word (r :: tail) (r :: tail) :=
  Word.localMap r.owner (ℓ₁ := [r]) (ℓ₂ := [r])
    (by simp) (by simp) (A.rTensor ℂ) tail

/-- Endpoint operators introduce no source preparation.
Source: polynomial-PEPS 04-compression.tex, lines 279–309. -/
theorem sources_localEndpoint (r : Reg P) (A : r.space →L[ℂ] r.space) (tail : Layout P) :
    (localEndpoint r A tail).sources = [] := rfl
end Word
namespace SourceInventory
/-- The actual source-free operator applying the two supplied endpoint maps
at every original source slot. Owners and slot order are recorded by the
original inventory. Source: polynomial-PEPS 04-compression.tex, lines 279–309
and 565–588. -/
def endpointWord : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    (∀ i, U i →L[ℂ] U i) → (∀ i, V i →L[ℂ] V i) →
      Word (slotLayout R U V) (slotLayout R U V)
  | [], _, _, _, _ => .id []
  | r :: R, U, V, A, B =>
      let ru : Reg P := ⟨r.left, U 0⟩
      let rv : Reg P := ⟨r.right, V 0⟩
      let tail := slotLayout R (fun i => U i.succ) (fun i => V i.succ)
      (Word.comp (Word.localEndpoint ru (A 0) (rv :: tail))
        (Word.frame ru (Word.comp (Word.localEndpoint rv (B 0) tail)
          (Word.frame rv (endpointWord R (fun i => U i.succ) (fun i => V i.succ)
            (fun i => A i.succ) (fun i => B i.succ)))))).castLayouts
              (slotLayout_cons r R U V).symm (slotLayout_cons r R U V).symm

/-- The literal endpoint-operator word is source-free.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem sources_endpointWord (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    (endpointWord R U V A B).sources = [] := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      exact (Word.sources_castLayouts _ _ _).trans (by
        simp only [Word.sources, Word.sources_localEndpoint, ih, List.nil_append])

end SourceInventory
end TNLean.PEPS.PairEffect
