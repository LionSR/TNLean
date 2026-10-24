/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EndpointRegisterRestriction
import TNLean.Lattice.Compression.WordOwnerEvaluation

/-!
# Owner and layout identification of an arbitrary endpoint-register word

The endpoint operators are arbitrary. The owner relabelling and the
identification of equal layouts change neither their spaces nor their maps.
No source indices, branch labels, or sampled matrices are unfolded here.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceInventory

/-- Relabelling the owners of an arbitrary endpoint-register list and
identifying its input and output layouts preserves the operator under the
canonical space identification.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
theorem endpointRegisterWord_eval_heq_mapOwner_castLayouts {P Q : Type}
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) (f : P → Q)
    {a b : Layout Q} (ha : Layout.mapOwner f (D.map Sigma.fst) = a)
    (hb : Layout.mapOwner f (D.map Sigma.fst) = b) :
    HEq (((endpointRegisterWord D).mapOwner f).castLayouts ha hb).eval
      (endpointRegisterWord D).eval :=
  (Word.eval_castLayouts_heq ((endpointRegisterWord D).mapOwner f) ha hb).trans
    (Word.eval_mapOwner_heq f (endpointRegisterWord D))

end TNLean.Lattice.PartyCircuit.SourceInventory
