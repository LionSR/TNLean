/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction
import TNLean.PEPS.Approximation.BasisMatrixOperator
import QICLean.Channel.PartialTrace

/-! # Mixed coordinate traces of restricted chronological words

Restrict three source-free chronological words to the same selected parties.
The two source-to-output words and the source-input word determine a mixed
coordinate matrix. Tracing its discarded output coordinates gives the
retained physical matrix. The definition uses arbitrary finite orthonormal
coordinate bases and imposes no contraction or normalization assumption.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 574–579.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect

/-- The mixed coordinate trace for arbitrary source-free words is formed before
the actual sampled words are substituted. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 574–579. -/
def restrictedMixedPhysicalTrace {Q I X E : Type}
    [Fintype I] [Fintype X] [Fintype E] {a b : Layout Q} (f : Q → Bool)
    (u t : Word a b) (v : Word a a)
    (hu : u.sources = []) (ht : t.sources = []) (hv : v.sources = [])
    (B : OrthonormalBasis I ℂ (Mem (Layout.restrict f a)))
    (C : OrthonormalBasis (X × E) ℂ (Mem (Layout.restrict f b))) : Matrix X X ℂ := by
  classical
  exact Matrix.partialTraceRight (α := X) (β := E)
    (Matrix.of (fun row col ↦ C.repr ((u.restrict f hu).eval (B col)) row) *
      LinearMap.toMatrix B.toBasis B.toBasis (v.restrict f hv).eval.toLinearMap *
      (Matrix.of (fun row col ↦ C.repr ((t.restrict f ht).eval (B col)) row))ᴴ)

end TNLean.PEPS.PairEffect
