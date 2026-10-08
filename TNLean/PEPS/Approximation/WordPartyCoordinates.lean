/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CanonicalPartyFactorization
import TNLean.PEPS.Approximation.PartyLabelledCoordinates

/-! # Party coordinates of source-free chronological words

The canonical grouping isometry transports the product of the literal local register bases to
the original register order. The matrix of a source-free word in these bases is obtained from
its actual singleton restrictions.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P] [DecidableEq P]
variable {I J : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (J p)]

/-- The actual party product basis on the original register order, transported
by the canonical grouping isometry.
Source: polynomial-PEPS 04-compression.tex, lines 565–588. -/
def partyGroupedBasis (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    OrthonormalBasis ((p : P) → I p) ℂ (Mem a) :=
  (partyLabelledBasis a b ps hn hc).map
    (groupByPartyIso ps a hn (fun r _ => hc r.owner)).symm

namespace Word
/-- The actual matrix of a source-free chronological word in the party product
bases is the product of its literal singleton-restriction matrix entries.
No tensor factorization or nonvanishing hypothesis is assumed.
Source: polynomial-PEPS 04-compression.tex, lines 565–588. -/
theorem partyGroupedBasis_repr_eval {a z : Layout P} (w : Word a z) (hs : w.sources = [])
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (c : (p : P) → OrthonormalBasis (J p) ℂ (Mem (Layout.atParty p z)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (x : (p : P) → J p) (y : (p : P) → I p) :
    (partyGroupedBasis z c ps hn hc).repr
        (w.eval (partyGroupedBasis a b ps hn hc y)) x =
      ∏ p, (c p).repr ((w.restrict (SourceCircuit.partySelector p) hs).eval (b p (y p))) (x p) := by
  change (partyLabelledBasis z c ps hn hc).repr
    (groupByPartyIso ps z hn (fun r _ => hc r.owner)
      (w.eval ((groupByPartyIso ps a hn (fun r _ => hc r.owner)).symm
        (partyLabelledBasis a b ps hn hc y)))) x = _
  have h := congrArg
    (fun A => A ((groupByPartyIso ps a hn (fun r _ => hc r.owner)).symm
      (partyLabelledBasis a b ps hn hc y)))
    (groupByPartyIso_eval_eq_tensorRestrictions w hs ps hn (fun p _ => hc p))
  simp only [comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply] at h
  rw [h]
  exact partyLabelledBasis_repr_tensorPartyMaps a z b c _ ps hn hc x y

end Word
end TNLean.PEPS.PairEffect
