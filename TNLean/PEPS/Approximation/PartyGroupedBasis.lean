/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyLabelledCoordinates
import TNLean.PEPS.Approximation.PartyGrouping

/-!
# Party tensor bases on the original register order

The canonical grouping isometry identifies the original register memory with
the ordered tensor product of the party memories. Transporting their labelled
product basis by the inverse isometry gives an orthonormal basis of the
original memory.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P] [DecidableEq P]
variable {I : P → Type} [∀ p, Fintype (I p)]

/-- The actual party product basis on the original register order, transported
by the canonical grouping isometry.
Source: polynomial-PEPS 04-compression.tex, lines 565–588. -/
def partyGroupedBasis (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    OrthonormalBasis ((p : P) → I p) ℂ (Mem a) :=
  (partyLabelledBasis a b ps hn hc).map
    (groupByPartyIso ps a hn (fun r _ => hc r.owner)).symm

end TNLean.PEPS.PairEffect
