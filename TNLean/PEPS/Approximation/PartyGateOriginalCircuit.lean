/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.LayoutEqualityCoordinates
import TNLean.PEPS.Approximation.PartyGateCircuit

/-!
# A sum of monomials on a list of parties as an original circuit

This file completes `TNLean.PEPS.Approximation.PartyGateCircuit`: a sum `∑_ξ c_ξ M_ξ` of
allowed monomials that use only the parties of a finite set `S` and fix the other registers is
an original circuit with at most one nonprivate gate, whose participants lie in `S`: the circuit
`gateCircuit` has the operator of the sum (`eval_gateCircuit`). The coefficients, the number of
monomials and the pair effects of each monomial are kept, so the expansion bounds of Theorem 5.2
transfer. The resulting existence statement, together with the bound on pair sources, is
`PartyGate.exists_originalCircuit` in `TNLean.PEPS.Approximation.PartyGateSourceBound`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), original circuits, `04-compression.tex`,
  lines 21–43 and 199–208; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect
open TNLean.Lattice.PartyCircuit

variable {P : Type} [DecidableEq P]

/-! ### Relabelling registers by the parties of a finite set -/

/-- Each party of `S` as itself, every other party as the fixed party `d` of `S`. -/
def finsetRetraction (S : Finset P) (d : S) (p : P) : S :=
  if h : p ∈ S then ⟨p, h⟩ else d

theorem val_finsetRetraction {S : Finset P} (d : S) {p : P} (hp : p ∈ S) :
    (finsetRetraction S d p : P) = p := by
  simp [finsetRetraction, hp]

theorem mapOwner_val_finsetRetraction {S : Finset P} (d : S) :
    (a : Layout P) → (∀ r ∈ a, r.owner ∈ S) →
      Layout.mapOwner (Function.Embedding.subtype (· ∈ S))
        (Layout.mapOwner (finsetRetraction S d) a) = a
  | [], _ => rfl
  | r :: a, ha => by
      simp only [Layout.mapOwner_cons, Function.Embedding.subtype_apply,
        val_finsetRetraction d (ha r List.mem_cons_self)]
      rw [mapOwner_val_finsetRetraction d a fun t ht => ha t (List.mem_cons_of_mem _ ht)]

omit [DecidableEq P] in
private theorem cons_tmul_heq {r r' : Reg P} {a a' : Layout P} (hr : r' = r) (ha : a' = a)
    (u : r.space) (u' : r'.space) (hu : HEq u' u) (v : Mem a) (v' : Mem a') (hv : HEq v' v) :
    HEq (u' ⊗ₜ[ℂ] v' : Mem (r' :: a')) (u ⊗ₜ[ℂ] v : Mem (r :: a)) := by
  subst hr
  subst ha
  cases hu
  cases hv
  rfl

theorem mapOwnerIso_val_finsetRetraction_heq {S : Finset P} (d : S) :
    (a : Layout P) → (ha : ∀ r ∈ a, r.owner ∈ S) → (x : Mem a) →
      HEq (Layout.mapOwnerIso (Function.Embedding.subtype (· ∈ S))
        (Layout.mapOwner (finsetRetraction S d) a)
          (Layout.mapOwnerIso (finsetRetraction S d) a x)) x
  | [], _, _ => HEq.rfl
  | r :: a, ha, x => by
      have hr : (⟨(finsetRetraction S d r.owner : P), r.space⟩ : Reg P) = r := by
        cases r
        simp [val_finsetRetraction d (ha _ List.mem_cons_self)]
      have ha' : ∀ t ∈ a, t.owner ∈ S := fun t ht => ha t (List.mem_cons_of_mem _ ht)
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          simp only [map_add]
          exact Layout.add_heq (congrArg Mem (mapOwner_val_finsetRetraction d (r :: a) ha))
            hx hy
      | tmul u v =>
          exact cons_tmul_heq hr (mapOwner_val_finsetRetraction d a ha') u u HEq.rfl v _
            (mapOwnerIso_val_finsetRetraction_heq d a ha' v)

theorem memCongr_mapOwnerIso_val_finsetRetraction {S : Finset P} (d : S) (a : Layout P)
    (ha : ∀ r ∈ a, r.owner ∈ S) (x : Mem a) :
    Layout.memCongr (mapOwner_val_finsetRetraction d a ha)
        (Layout.mapOwnerIso (Function.Embedding.subtype (· ∈ S))
          (Layout.mapOwner (finsetRetraction S d) a)
            (Layout.mapOwnerIso (finsetRetraction S d) a x)) = x :=
  eq_of_heq ((Layout.memCongr_apply_heq _ _).trans
    (mapOwnerIso_val_finsetRetraction_heq d a ha x))

/-! ### The restricted gate -/

theorem owner_mem_of_mem_restrict {S : Finset P} {ℓ : Layout P} {r : Reg P}
    (hr : r ∈ Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ) : r.owner ∈ S := by
  simpa using (List.mem_filter.mp hr).2

theorem effectParties_retraction_ne {S : Finset P} (d : S) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : M.UsesOnly {p | decide (p ∈ S) = true}) :
    ∀ e ∈ (M.selectedPart (fun p ↦ decide (p ∈ S)) h).effectParties,
      finsetRetraction S d e.1 ≠ finsetRetraction S d e.2 := by
  intro e he
  rw [PartyChain.effectParties_selectedPart] at he
  obtain ⟨h₁, h₂, hne⟩ := M.effectParties_of_usesOnly h e he
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq] at h₁ h₂
  intro heq
  apply hne
  rw [← val_finsetRetraction d h₁, ← val_finsetRetraction d h₂, heq]

/-- The relabelled restricted gate of a sum of monomials using only the parties of `S`. -/
def retractedGate (S : Finset P) (d : S) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) :
    PartyGate (Layout.mapOwner (finsetRetraction S d) (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ))
      (Layout.mapOwner (finsetRetraction S d)
        (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ')) :=
  mapOwnerGate (finsetRetraction S d) (selectedGate _ G hU) fun m hm => by
    obtain ⟨m₀, hm₀, rfl⟩ := mem_selectedGate hm
    exact effectParties_retraction_ne d m₀.2 (hU m₀ hm₀)

theorem isAllowed_retractedGate (S : Finset P) (d : S) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hA : ∀ m ∈ G, m.2.IsAllowed) (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) :
    ∀ m ∈ retractedGate S d G hU, m.2.IsAllowed := by
  intro m hm
  obtain ⟨m₁, hm₁, rfl⟩ := mem_mapOwnerGate hm
  obtain ⟨m₀, hm₀, rfl⟩ := mem_selectedGate hm₁
  exact PartyChain.isAllowed_mapOwner _ _ _
    (PartyChain.isAllowed_selectedPart _ _ _ (hA m₀ hm₀))

theorem effectCount_retractedGate_le (S : Finset P) (d : S) {ℓ ℓ' : Layout P}
    (G : PartyGate ℓ ℓ') (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) {r : ℕ}
    (hr : ∀ m ∈ G, m.2.toEffectChain.effectCount ≤ r) :
    ∀ m ∈ retractedGate S d G hU, m.2.toEffectChain.effectCount ≤ r := by
  intro m hm
  obtain ⟨m₁, hm₁, rfl⟩ := mem_mapOwnerGate hm
  obtain ⟨m₀, hm₀, rfl⟩ := mem_selectedGate hm₁
  rw [PartyChain.effectCount_mapOwner, PartyChain.effectCount_selectedPart]
  exact hr m₀ hm₀

theorem map_norm_retractedGate (S : Finset P) (d : S) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) :
    (retractedGate S d G hU).map (fun m => ‖m.1‖) = G.map fun m => ‖m.1‖ :=
  (map_norm_mapOwnerGate _ _ _).trans (map_norm_selectedGate _ _ _)

theorem length_retractedGate (S : Finset P) (d : S) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) :
    (retractedGate S d G hU).length = G.length :=
  (length_mapOwnerGate _ _ _).trans (length_selectedGate _ _ _)

theorem gate_retractedGate (S : Finset P) (d : S) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) :
    gate (toGate (retractedGate S d G hU)) =
      isoL (Layout.mapOwnerIso (finsetRetraction S d) _) ∘L
        gate (toGate (selectedGate _ G hU)) ∘L
          isoL (Layout.mapOwnerIso (finsetRetraction S d) _).symm := by
  have h : gate (toGate (retractedGate S d G hU)) ∘L
      isoL (Layout.mapOwnerIso (finsetRetraction S d) _) =
        isoL (Layout.mapOwnerIso (finsetRetraction S d) _) ∘L
          gate (toGate (selectedGate _ G hU)) :=
    gate_mapOwnerGate _ _ _
  ext x
  have := DFunLike.congr_fun h ((Layout.mapOwnerIso (finsetRetraction S d) _).symm x)
  simpa using this

/-! ### The gate before spectator registers -/

/-- A point of a nonempty finite set, used as the default label. -/
def nonemptyPoint {S : Finset P} (hS : S.Nonempty) : S := ⟨hS.choose, hS.choose_spec⟩

/-- The selected part of a sum of monomials using only the parties of `S`, as one operation on
the registers of `S` before spectator registers `T`: a private map if `S` has a single party,
and one nonprivate gate with participants `S` otherwise. -/
def coreGateCircuit (S : Finset P) (hS₀ : S.Nonempty) {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ')
    (hA : ∀ m ∈ G, m.2.IsAllowed) (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P) :
    OriginalCircuit (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ ++ T)
      (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ' ++ T) :=
  if hC : S.card = 1 then
    .privateMap (Finset.card_eq_one.mp hC).choose
      (fun r hr => Finset.mem_singleton.mp
        ((Finset.card_eq_one.mp hC).choose_spec ▸ owner_mem_of_mem_restrict hr))
      (fun r hr => Finset.mem_singleton.mp
        ((Finset.card_eq_one.mp hC).choose_spec ▸ owner_mem_of_mem_restrict hr))
      (gate (toGate (selectedGate _ G hU))) hN T
  else
    (OriginalCircuit.nonprivateGate (Function.Embedding.subtype (· ∈ S))
      (by rwa [Fintype.card_coe]) (retractedGate S (nonemptyPoint hS₀) G hU)
      (isAllowed_retractedGate S (nonemptyPoint hS₀) G hA hU)
      (by
        rw [gate_retractedGate]
        exact (norm_comp_isoL_le _ _ _).trans hN) T).castLayouts
      (congrArg (· ++ T) (mapOwner_val_finsetRetraction (nonemptyPoint hS₀) _
        fun _ hr => owner_mem_of_mem_restrict hr))
      (congrArg (· ++ T) (mapOwner_val_finsetRetraction (nonemptyPoint hS₀) _
        fun _ hr => owner_mem_of_mem_restrict hr))

omit [DecidableEq P] in
private theorem memCongr_append_left_symm {a a' T : Layout P} (h : a' = a) (y : Mem a)
    (z : Mem T) :
    (Layout.memCongr (congrArg (· ++ T) h)).symm ((appendIso a T).symm (y ⊗ₜ z)) =
      (appendIso a' T).symm ((Layout.memCongr h).symm y ⊗ₜ z) := by
  cases h
  rfl

omit [DecidableEq P] in
private theorem memCongr_append_left {a a' T : Layout P} (h : a' = a) (y : Mem a')
    (z : Mem T) :
    Layout.memCongr (congrArg (· ++ T) h) ((appendIso a' T).symm (y ⊗ₜ z)) =
      (appendIso a T).symm (Layout.memCongr h y ⊗ₜ z) := by
  cases h
  rfl

/-- The core gate acts as the selected part of the sum on the registers of `S`. -/
theorem eval_coreGateCircuit_appendIso_symm (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P)
    (y : Mem (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ)) (z : Mem T) :
    (coreGateCircuit S hS₀ G hA hU hN T).eval
        ((appendIso (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ) T).symm (y ⊗ₜ z)) =
      (appendIso (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ') T).symm
        (gate (toGate (selectedGate _ G hU)) y ⊗ₜ z) := by
  unfold coreGateCircuit
  split
  · simp [OriginalCircuit.eval]
  · have hA' : ∀ r ∈ Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ, r.owner ∈ S :=
      fun _ hr => owner_mem_of_mem_restrict hr
    have hB' : ∀ r ∈ Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ', r.owner ∈ S :=
      fun _ hr => owner_mem_of_mem_restrict hr
    rw [OriginalCircuit.eval_castLayouts]
    simp only [comp_apply, isoL_apply]
    rw [memCongr_append_left_symm (mapOwner_val_finsetRetraction (nonemptyPoint hS₀) _ hA'),
      OriginalCircuit.eval_nonprivateGate_appendIso_symm,
      memCongr_append_left (mapOwner_val_finsetRetraction (nonemptyPoint hS₀) _ hB')]
    congr 2
    have hy : (Layout.mapOwnerIso (Function.Embedding.subtype (· ∈ S))
        (Layout.mapOwner (finsetRetraction S (nonemptyPoint hS₀))
          (Layout.restrict (fun p ↦ decide (p ∈ S)) ℓ))).symm
        ((Layout.memCongr (mapOwner_val_finsetRetraction (nonemptyPoint hS₀) _ hA')).symm y) =
          Layout.mapOwnerIso (finsetRetraction S (nonemptyPoint hS₀)) _ y := by
      rw [LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.symm_apply_eq,
        memCongr_mapOwnerIso_val_finsetRetraction (nonemptyPoint hS₀) _ hA']
    rw [hy, gate_retractedGate]
    simp only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply]
    exact memCongr_mapOwnerIso_val_finsetRetraction (nonemptyPoint hS₀) _ hB' _

theorem nonprivateCount_coreGateCircuit_le (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P) :
    (coreGateCircuit S hS₀ G hA hU hN T).nonprivateCount ≤ 1 := by
  unfold coreGateCircuit
  split
  · exact Nat.zero_le 1
  · rw [OriginalCircuit.nonprivateCount_castLayouts]
    exact le_rfl

theorem participants_coreGateCircuit_subset (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P)
    (g : (coreGateCircuit S hS₀ G hA hU hN T).nonprivateLocations) :
    (↑((coreGateCircuit S hS₀ G hA hU hN T).participants g) : Set P) ⊆ ↑S := by
  revert g
  by_cases hC : S.card = 1
  · rw [coreGateCircuit, dite_eq_left hC]
    intro g
    exact nomatch g
  · rw [coreGateCircuit, dite_eq_right hC]
    intro g
    refine OriginalCircuit.participants_castLayouts_subset _ _ _ (fun g x hx => ?_) g
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    exact y.2

theorem isExpansionBounded_coreGateCircuit (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P) {r : ℕ} {s : ℝ}
    (hr : ∀ m ∈ G, m.2.toEffectChain.effectCount ≤ r) (hs : (G.map fun m => ‖m.1‖).sum ≤ s) :
    (coreGateCircuit S hS₀ G hA hU hN T).IsExpansionBounded r s := by
  unfold coreGateCircuit
  split
  · trivial
  · refine OriginalCircuit.isExpansionBounded_castLayouts _ _ _ ⟨?_, ?_⟩
    · exact effectCount_retractedGate_le S _ G hU hr
    · rw [map_norm_retractedGate]
      exact hs

theorem isMonomialBounded_coreGateCircuit (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P) :
    (coreGateCircuit S hS₀ G hA hU hN T).IsMonomialBounded G.length := by
  unfold coreGateCircuit
  split
  · trivial
  · exact OriginalCircuit.isMonomialBounded_castLayouts _ _ _ (length_retractedGate S _ G hU).le

/-! ### The whole sum of monomials -/

omit [DecidableEq P] in
/-- The registers outside a selection carry a nonzero vector when the whole memory does. -/
theorem nontrivial_mem_restrict_not (f : P → Bool) (ℓ : Layout P) (hne : Nontrivial (Mem ℓ)) :
    Nontrivial (Mem (Layout.restrict (fun p ↦ !f p) ℓ)) := by
  by_contra hB
  rw [not_nontrivial_iff_subsingleton] at hB
  have h0 : ∀ w : Mem (Layout.restrict f ℓ) ⊗[ℂ] Mem (Layout.restrict (fun p ↦ !f p) ℓ),
      w = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : Mem ℓ)
  apply hx
  rw [← (Layout.partitionIso f ℓ).map_eq_zero_iff]
  exact h0 _

/-- The selected part of a sum of monomials fixing the outside registers is a contraction when
the sum is. -/
theorem norm_gate_selectedGate_le (S : Finset P) {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    (G : PartyGate ℓ ℓ') (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hF : ∀ m (hm : m ∈ G), (m.2.complementPart (fun p ↦ decide (p ∈ S)) (hU m hm)).eval =
      isoL (Layout.memCongr h))
    (hN : ‖gate (toGate G)‖ ≤ 1) (hne : Nontrivial (Mem ℓ)) :
    ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1 := by
  have := nontrivial_mem_restrict_not (fun p ↦ decide (p ∈ S)) ℓ hne
  obtain ⟨z, hz⟩ := exists_ne (0 : Mem (Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ))
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hP := partitionIso_gate S h G hU hF
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  have key := DFunLike.congr_fun hP ((Layout.partitionIso _ ℓ).symm (y ⊗ₜ z))
  simp only [comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply,
    TensorProduct.mapL_tmul] at key
  have hle : ‖gate (toGate (selectedGate _ G hU)) y‖ * ‖z‖ ≤ ‖y‖ * ‖z‖ := by
    have h1 := congrArg norm key
    rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul, LinearIsometryEquiv.norm_map]
      at h1
    rw [← h1]
    calc ‖gate (toGate G) ((Layout.partitionIso _ ℓ).symm (y ⊗ₜ z))‖
        ≤ ‖gate (toGate G)‖ * ‖(Layout.partitionIso _ ℓ).symm (y ⊗ₜ z)‖ := le_opNorm _ _
      _ ≤ 1 * ‖(Layout.partitionIso _ ℓ).symm (y ⊗ₜ z)‖ := by gcongr
      _ = ‖y‖ * ‖z‖ := by
          rw [one_mul, LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]
  rw [one_mul]
  exact le_of_mul_le_mul_right hle hz'

omit [DecidableEq P] in
private theorem memCongr_self_symm_apply {a : Layout P} (h : a = a) (v : Mem a) :
    (Layout.memCongr h).symm v = v :=
  rfl

omit [DecidableEq P] in
private theorem memCongr_append_right {a T T' : Layout P} (h : T = T') (y : Mem a)
    (z : Mem T) :
    Layout.memCongr (congrArg (a ++ ·) h) ((appendIso a T).symm (y ⊗ₜ z)) =
      (appendIso a T').symm (y ⊗ₜ Layout.memCongr h z) := by
  cases h
  rfl

/-- **A sum of monomials on a list of parties as an original circuit.** The registers of `S` are
collected in front, the selected part of the sum acts on them as one gate, and the registers are
moved back. Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43, and
`06-geometry.tex`, lines 574–583. -/
def gateCircuit (S : Finset P) (hS₀ : S.Nonempty) {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) : OriginalCircuit ℓ ℓ' :=
  .comp ((Layout.partitionWord _ ℓ).toOriginalCircuit
      (Layout.isReordering_partitionWord _ ℓ).isAllowed)
    (.comp ((coreGateCircuit S hS₀ G hA hU hN _).castLayouts rfl (congrArg (_ ++ ·) h))
      ((Layout.unpartitionWord _ ℓ').toOriginalCircuit
        (Layout.isReordering_unpartitionWord _ ℓ').isAllowed))

theorem eval_gateCircuit (S : Finset P) (hS₀ : S.Nonempty) {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hF : ∀ m (hm : m ∈ G), (m.2.complementPart (fun p ↦ decide (p ∈ S)) (hU m hm)).eval =
      isoL (Layout.memCongr h))
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) :
    (gateCircuit S hS₀ h G hA hU hN).eval = gate (toGate G) := by
  have hP := partitionIso_gate S h G hU hF
  ext x
  obtain ⟨w, rfl⟩ := (Layout.partitionIso (fun p ↦ decide (p ∈ S)) ℓ).symm.surjective x
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul y z =>
      have hpw : (Layout.partitionWord (fun p ↦ decide (p ∈ S)) ℓ).eval
          ((Layout.partitionIso _ ℓ).symm (y ⊗ₜ z)) = (appendIso _ _).symm (y ⊗ₜ z) := by
        rw [LinearIsometryEquiv.eq_symm_apply, Layout.appendIso_eval_partitionWord,
          LinearIsometryEquiv.apply_symm_apply]
      have key := DFunLike.congr_fun hP ((Layout.partitionIso _ ℓ).symm (y ⊗ₜ z))
      simp only [comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply,
        TensorProduct.mapL_tmul] at key
      rw [← LinearIsometryEquiv.symm_apply_apply (Layout.partitionIso _ ℓ')
        (gate (toGate G) _), key]
      simp only [gateCircuit, OriginalCircuit.eval, comp_apply, Word.eval_toOriginalCircuit, hpw,
        OriginalCircuit.eval_castLayouts, isoL_apply]
      erw [memCongr_self_symm_apply]
      rw [eval_coreGateCircuit_appendIso_symm, memCongr_append_right,
        Layout.eval_unpartitionWord_appendIso_symm]

end TNLean.PEPS.PairEffect
