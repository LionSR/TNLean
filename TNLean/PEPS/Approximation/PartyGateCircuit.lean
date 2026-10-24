/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutPartitionWord
import TNLean.PEPS.Approximation.PartyChainRestriction

/-!
# A sum of monomials on a list of parties as one gate

A bounded change of the protocol of Proposition 7.1 may be a sum `∑_ξ c_ξ M_ξ` of allowed
monomials, as in the small-patch rewrite of Lemma 6.3, all of which use only the parties of a
fixed finite set `S`. Such a change is a single nonprivate gate whose participants are the
parties of `S` (`06-geometry.tex`, lines 574–583), provided that the monomials act on the
registers of `S` alone: their complementary parts, which consist of exchanges of the other
registers, act as the identity (`PartyChain.FixesOutside`).

The gate is built as follows (`PartyGate.exists_originalCircuit`). The registers of `S` are
moved in front by exchanges (`Layout.partitionWord`), the monomials are restricted to them
(`PartyChain.selectedPart`) and relabelled by the parties of `S`, the resulting expansion is
one nonprivate gate with the other registers as spectators, and the registers are moved back
(`Layout.unpartitionWord`). If `S` has a single party the gate is a private map of that party
instead, as the original circuits require. The construction keeps the coefficients, the number
of monomials and the number of pair effects of each monomial.

## Main definitions

* `PartyCircuit.PartyChain.FixesOutside` : a monomial leaves the registers outside `S` in place.
* `PairEffect.selectedGate`, `PairEffect.mapOwnerGate` : the restriction and relabelling of a
  sum of monomials.

## Main results

* `PairEffect.partitionIso_gate` : the factorization of a sum of monomials that fix the
  registers outside `S`.
* `PartyCircuit.PartyGate.exists_originalCircuit` : such a sum is an original circuit with at most
  one nonprivate gate, whose participants lie in `S`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), original circuits, `04-compression.tex`,
  lines 21–43 and 199–208; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583;
  Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean
open TNLean.Lattice.PartyCircuit

variable {P : Type}

/-! ### Pair effects of a monomial using selected parties -/

namespace Lattice.PartyCircuit.PartyChain

theorem effectParties_of_usesOnly {S : Set P} {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (h : M.UsesOnly S) : ∀ e ∈ M.effectParties, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 := by
  induction M with
  | final w => simp [effectParties]
  | effect hpq α β ℓS w η rest ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨h.1, h.2.1, hpq⟩
      · exact ih h.2.2.2 e he

@[simp] theorem effectParties_selectedPart (f : P → Bool) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : M.UsesOnly {p | f p = true}) :
    (M.selectedPart f h).effectParties = M.effectParties := by
  induction M with
  | final w => rfl
  | effect hpq α β ℓS w η rest ih => simp only [selectedPart, effectParties, ih]

/-- A monomial using only the parties of `S` leaves the other registers in place: its
complementary part acts as the identity, for a given identification `h` of the other registers
of its input and output layouts. -/
def FixesOutside [DecidableEq P] (S : Finset P) {ℓX ℓY : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓX =
      Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓY)
    (M : PartyChain ℓX ℓY) : Prop :=
  ∃ hM : M.UsesOnly {p | decide (p ∈ S) = true},
    (M.complementPart (fun p ↦ decide (p ∈ S)) hM).eval = isoL (Layout.memCongr h)

end Lattice.PartyCircuit.PartyChain

/-! ### Restricting and relabelling a sum of monomials -/

namespace PEPS.PairEffect
/-- The selected parts of the monomials of a sum. -/
def selectedGate (f : P → Bool) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (∀ m ∈ G, m.2.UsesOnly {p | f p = true}) →
      PartyGate (Layout.restrict f ℓ) (Layout.restrict f ℓ')
  | [], _ => []
  | m :: G, h => (m.1, m.2.selectedPart f (h m List.mem_cons_self)) ::
      selectedGate f G fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

/-- The relabelled monomials of a sum. -/
def mapOwnerGate {Q : Type} (g : P → Q) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (∀ m ∈ G, ∀ e ∈ m.2.effectParties, g e.1 ≠ g e.2) →
      PartyGate (Layout.mapOwner g ℓ) (Layout.mapOwner g ℓ')
  | [], _ => []
  | m :: G, h => (m.1, m.2.mapOwner g (h m List.mem_cons_self)) ::
      mapOwnerGate g G fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

theorem length_selectedGate (f : P → Bool) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (h : ∀ m ∈ G, m.2.UsesOnly {p | f p = true}) →
      (selectedGate f G h).length = G.length
  | [], _ => rfl
  | _ :: G, _ => congrArg (· + 1) (length_selectedGate f G _)

theorem length_mapOwnerGate {Q : Type} (g : P → Q) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (h : ∀ m ∈ G, ∀ e ∈ m.2.effectParties, g e.1 ≠ g e.2) →
      (mapOwnerGate g G h).length = G.length
  | [], _ => rfl
  | _ :: G, _ => congrArg (· + 1) (length_mapOwnerGate g G _)

theorem mem_selectedGate {f : P → Bool} {ℓ ℓ' : Layout P} :
    {G : PartyGate ℓ ℓ'} → {h : ∀ m ∈ G, m.2.UsesOnly {p | f p = true}} →
      ∀ {m'}, m' ∈ selectedGate f G h →
        ∃ m, ∃ hm : m ∈ G, m' = (m.1, m.2.selectedPart f (h m hm))
  | [], _, _, hm' => by simp [selectedGate] at hm'
  | m :: G, h, m', hm' => by
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact ⟨m, List.mem_cons_self, rfl⟩
      · obtain ⟨m₀, hm₀, rfl⟩ := mem_selectedGate hm'
        exact ⟨m₀, List.mem_cons_of_mem _ hm₀, rfl⟩

theorem mem_mapOwnerGate {Q : Type} {g : P → Q} {ℓ ℓ' : Layout P} :
    {G : PartyGate ℓ ℓ'} → {h : ∀ m ∈ G, ∀ e ∈ m.2.effectParties, g e.1 ≠ g e.2} →
      ∀ {m'}, m' ∈ mapOwnerGate g G h → ∃ m, ∃ hm : m ∈ G, m' = (m.1, m.2.mapOwner g (h m hm))
  | [], _, _, hm' => by simp [mapOwnerGate] at hm'
  | m :: G, h, m', hm' => by
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact ⟨m, List.mem_cons_self, rfl⟩
      · obtain ⟨m₀, hm₀, rfl⟩ := mem_mapOwnerGate hm'
        exact ⟨m₀, List.mem_cons_of_mem _ hm₀, rfl⟩

theorem map_norm_selectedGate (f : P → Bool) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (h : ∀ m ∈ G, m.2.UsesOnly {p | f p = true}) →
      (selectedGate f G h).map (fun m => ‖m.1‖) = G.map fun m => ‖m.1‖
  | [], _ => rfl
  | _ :: G, _ => congrArg (_ :: ·) (map_norm_selectedGate f G _)

theorem map_norm_mapOwnerGate {Q : Type} (g : P → Q) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (h : ∀ m ∈ G, ∀ e ∈ m.2.effectParties, g e.1 ≠ g e.2) →
      (mapOwnerGate g G h).map (fun m => ‖m.1‖) = G.map fun m => ‖m.1‖
  | [], _ => rfl
  | _ :: G, _ => congrArg (_ :: ·) (map_norm_mapOwnerGate g G _)

/-- **Factorization of a sum of monomials fixing the outside registers.** -/
theorem partitionIso_gate [DecidableEq P] (S : Finset P) {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    : (G : PartyGate ℓ ℓ') → (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) →
      (hF : ∀ m (hm : m ∈ G), (m.2.complementPart (fun p ↦ decide (p ∈ S)) (hU m hm)).eval =
        isoL (Layout.memCongr h)) →
      isoL (Layout.partitionIso (fun p ↦ decide (p ∈ S)) ℓ') ∘L gate (toGate G) =
        TensorProduct.mapL (gate (toGate (selectedGate _ G hU))) (isoL (Layout.memCongr h)) ∘L
          isoL (Layout.partitionIso (fun p ↦ decide (p ∈ S)) ℓ)
  | [], _, _ => by
      simp only [selectedGate, toGate, gate, comp_zero, TensorProduct.mapL_zero_left, zero_comp]
  | m :: G, hU, hF => by
      have hm := m.2.partitionIso_eval (fun p ↦ decide (p ∈ S)) (hU m List.mem_cons_self)
      rw [hF m List.mem_cons_self] at hm
      have ih := partitionIso_gate S h G (fun m' hm' => hU m' (List.mem_cons_of_mem _ hm'))
        (fun m' hm' => hF m' (List.mem_cons_of_mem _ hm'))
      simp only [selectedGate, toGate, gate, comp_add, comp_smul, hm, ih,
        TensorProduct.mapL_add_left, TensorProduct.mapL_smul_left, add_comp, smul_comp]

/-- Relabelling the owners of a sum of monomials intertwines the gates. -/
theorem gate_mapOwnerGate {Q : Type} (g : P → Q) {ℓ ℓ' : Layout P} :
    (G : PartyGate ℓ ℓ') → (h : ∀ m ∈ G, ∀ e ∈ m.2.effectParties, g e.1 ≠ g e.2) →
      gate (toGate (mapOwnerGate g G h)) ∘L isoL (Layout.mapOwnerIso g ℓ) =
        isoL (Layout.mapOwnerIso g ℓ') ∘L gate (toGate G)
  | [], _ => by simp only [mapOwnerGate, toGate, gate, zero_comp, comp_zero]
  | m :: G, h => by
      simp only [mapOwnerGate, toGate, gate, add_comp, comp_add, smul_comp, comp_smul,
        PartyChain.eval_mapOwner, gate_mapOwnerGate g G]

end PEPS.PairEffect
end TNLean
