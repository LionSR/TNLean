/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyTensorCoordinates

/-! # Party-labelled coordinates of local tensor maps

An exhaustive order identifies the tensor-basis coordinates with functions on
the original party set. Source: polynomial-PEPS, `04-compression.tex`, lines 565–579.
-/
noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P] [DecidableEq P]
variable {I J : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (J p)]

/-- The ordered tensor basis indexed by original parties.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
def partyLabelledBasis (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    OrthonormalBasis ((p : P) → I p) ℂ (Mem (partyLayout ps a)) :=
  (partyListBasis a b ps).reindex (Equiv.piCongrLeft (fun p => I p)
    (List.Nodup.getEquivOfForallMemList ps hn hc))

/-- Relabelling preserves the actual tensor-basis vector.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
theorem partyLabelledBasis_apply (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) (y : (p : P) → I p) :
    partyLabelledBasis a b ps hn hc y = partyListBasis a b ps (fun i => y (ps.get i)) :=
  (partyListBasis a b ps).reindex_apply _ y

/-- The matrix entries of the tensor map are the products of the actual
party-local entries, in original party labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
theorem partyLabelledBasis_repr_tensorPartyMaps (a z : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (c : (p : P) → OrthonormalBasis (J p) ℂ (Mem (Layout.atParty p z)))
    (B : (p : P) → Mem (Layout.atParty p a) →L[ℂ] Mem (Layout.atParty p z))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (x : (p : P) → J p) (y : (p : P) → I p) :
    (partyLabelledBasis z c ps hn hc).repr
      (tensorPartyMaps a z B ps (partyLabelledBasis a b ps hn hc y)) x =
      ∏ p, (c p).repr (B p (b p (y p))) (x p) := by
  have hv := congrArg (tensorPartyMaps a z B ps) (partyLabelledBasis_apply a b ps hn hc y)
  calc
    _ = (partyListBasis z c ps).repr
      (tensorPartyMaps a z B ps (partyListBasis a b ps (fun i => y (ps.get i))))
      (fun i => x (ps.get i)) :=
      (partyListBasis z c ps).repr_reindex _ _ x |>.trans
        (congrArg (fun v => (partyListBasis z c ps).repr v (fun i => x (ps.get i))) hv)
    _ = ∏ i : Fin ps.length, (c (ps.get i)).repr
      (B (ps.get i) (b (ps.get i) (y (ps.get i)))) (x (ps.get i)) :=
      partyListBasis_repr_tensorPartyMaps a z b c B ps _ _
    _ = _ := (List.Nodup.getEquivOfForallMemList ps hn hc).prod_comp
      (fun p => (c p).repr (B p (b p (y p))) (x p))
end TNLean.PEPS.PairEffect
