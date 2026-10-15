/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedPartyNetwork
import TNLean.PEPS.Approximation.DyadicProtocol
import TNLean.PEPS.Approximation.GroundStateApproximation
import TNLean.PEPS.Approximation.UniformApproximateSampledNetwork

/-!
# Compression of the dyadic distribution protocol

TEST
-/

noncomputable section

open scoped Matrix

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace EffectCircuit

/-- The exact operator of every recorded gate occurrence: the sum of its own monomial list. -/
def exactGateMaps : {a b : Layout P} → (w : EffectCircuit a b) → w.GateMaps
  | _, _, .id _ => PUnit.unit
  | _, _, .comp w v => (exactGateMaps w, exactGateMaps v)
  | _, _, .localMap .. => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ => PairEffect.gate (toGate L)
  | _, _, .swap .. => PUnit.unit
  | _, _, .frame _ w => exactGateMaps w

/-- The monomial lists already recorded at every gate occurrence. -/
def selfLists : {a b : Layout P} → (w : EffectCircuit a b) → w.GateLists
  | _, _, .id _ => PUnit.unit
  | _, _, .comp w v => (selfLists w, selfLists v)
  | _, _, .localMap .. => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ => L
  | _, _, .swap .. => PUnit.unit
  | _, _, .frame _ w => selfLists w

/-- Evaluating with the exact gate operators is the evaluation of the circuit. -/
theorem evalWithGateMaps_exactGateMaps {a b : Layout P} (w : EffectCircuit a b) :
    w.evalWithGateMaps w.exactGateMaps = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      exact congrArg₂ ContinuousLinearMap.comp ihv ihw
  | localMap => rfl
  | gate => rfl
  | swap => rfl
  | frame r w ih => exact congrArg (fun A ↦ A.lTensor r.space) ih

/-- Transport a circuit along equalities of its input and output layouts. -/
def castLayouts {a a' b b' : Layout P} (ha : a = a') (hb : b = b') (w : EffectCircuit a b) :
    EffectCircuit a' b' :=
  ha ▸ hb ▸ w

end EffectCircuit

namespace OriginalCircuit

variable {a b : Layout P}

theorem isGateApproximation_produce (w : OriginalCircuit a b) {δ : ℝ} (hδ : 0 ≤ δ) :
    (w.produce.reexpand w.produce.selfLists).IsGateApproximation δ
      (w.produce.reexpandGateMaps w.produce.selfLists w.produce.exactGateMaps) := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | privateMap p ha hb A hA tail => exact hA
  | nonprivateGate owner hC L hL hG tail =>
      refine ⟨hC, hL, hG, ?_⟩
      change ‖PairEffect.gate (toGate L) - PairEffect.gate (toGate L)‖ ≤ δ
      simpa only [sub_self, norm_zero] using hδ
  | swap => trivial
  | frame r w ih => exact ih

theorem isTermwiseBounded_produce (w : OriginalCircuit a b) {r : ℕ} {S S' : ℝ}
    (h : w.IsExpansionBounded r S) (hS : S ≤ S') :
    (w.produce.reexpand w.produce.selfLists).IsTermwiseBounded r S' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate owner hC L hL hG tail =>
      refine fun term hterm ↦ ⟨h.1 term hterm, (h.2.trans hS).trans' ?_⟩
      exact List.single_le_sum (fun x hx ↦ by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact norm_nonneg _) _ (List.mem_map_of_mem hterm)
  | swap => trivial
  | frame r w ih => exact ih h

theorem monomialCount_produce_le (w : OriginalCircuit a b) {K : ℕ}
    (h : w.IsMonomialBounded K) :
    ∀ g, (w.produce.reexpand w.produce.selfLists).monomialCount g ≤ K := by
  induction w with
  | id => intro g; exact nomatch g
  | comp w v ihw ihv =>
      rintro (g | g)
      · exact ihw h.1 g
      · exact ihv h.2 g
  | privateMap => intro g; exact nomatch g
  | nonprivateGate => intro _; exact h
  | swap => intro g; exact nomatch g
  | frame r w ih => exact ih h

variable {a' b' : Layout P}

theorem expandedGateCount_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) :
    (EffectCircuit.castLayouts ha hb w.produce).expandedGateCount = w.nonprivateCount := by
  subst ha hb
  exact w.expandedGateCount_produce

theorem exists_participants_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b)
    (g : (EffectCircuit.castLayouts ha hb w.produce).gateLocations) :
    ∃ g' : w.nonprivateLocations,
      (EffectCircuit.castLayouts ha hb w.produce).participants g = w.participants g' := by
  subst ha hb
  change w.produce.gateLocations at g
  change ∃ g' : w.nonprivateLocations, w.produce.participants g = w.participants g'
  exact ⟨w.produceLocationsEquiv.symm g, by
    rw [← w.participants_produce, Equiv.apply_symm_apply]⟩

theorem participationCount_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) (p : P) :
    Nat.card {g : (EffectCircuit.castLayouts ha hb w.produce).gateLocations //
      p ∈ (EffectCircuit.castLayouts ha hb w.produce).participants g} =
      w.participationCount p := by
  subst ha hb
  change Nat.card {g : w.produce.gateLocations // p ∈ w.produce.participants g} = _
  exact Nat.card_congr (w.produceLocationsEquiv.subtypeEquiv fun g ↦ by
    rw [w.participants_produce]).symm

theorem isGateApproximation_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) {δ : ℝ} (hδ : 0 ≤ δ) :
    let W := EffectCircuit.castLayouts ha hb w.produce
    (W.reexpand W.selfLists).IsGateApproximation δ
      (W.reexpandGateMaps W.selfLists W.exactGateMaps) := by
  subst ha hb
  exact w.isGateApproximation_produce hδ

theorem isTermwiseBounded_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) {r : ℕ} {S S' : ℝ} (h : w.IsExpansionBounded r S) (hS : S ≤ S') :
    let W := EffectCircuit.castLayouts ha hb w.produce
    (W.reexpand W.selfLists).IsTermwiseBounded r S' := by
  subst ha hb
  exact w.isTermwiseBounded_produce h hS

theorem monomialCount_castLayouts_produce_le (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) {K : ℕ} (h : w.IsMonomialBounded K) :
    let W := EffectCircuit.castLayouts ha hb w.produce
    ∀ g, (W.reexpand W.selfLists).monomialCount g ≤ K := by
  subst ha hb
  exact w.monomialCount_produce_le h

theorem evalWithGateMaps_castLayouts_produce (ha : a = a') (hb : b = b')
    (w : OriginalCircuit a b) (x : Mem a') :
    let W := EffectCircuit.castLayouts ha hb w.produce
    W.evalWithGateMaps W.exactGateMaps x =
      Layout.memCongr hb (w.eval (Layout.memCongr ha.symm x)) := by
  subst ha hb
  change w.produce.evalWithGateMaps w.produce.exactGateMaps x = w.eval x
  rw [EffectCircuit.evalWithGateMaps_exactGateMaps, eval_produce]

end OriginalCircuit

end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.Approximation.DyadicProtocol

open Finset TNLean.PEPS.PairEffect

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- The first `n` changes of a protocol, composed into one chronology. -/
def chain : (n : ℕ) → OriginalCircuit (D.layout 0) (D.layout n)
  | 0 => .id _
  | n + 1 => .comp (chain n) (D.step n)

theorem eval_chain_trajectory (n : ℕ) : (D.chain n).eval (D.trajectory 0) = D.trajectory n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (D.step n).eval ((D.chain n).eval (D.trajectory 0)) = _
      rw [ih]; rfl

theorem nonprivateCount_chain (n : ℕ) :
    (D.chain n).nonprivateCount = ∑ t ∈ range n, (D.step t).nonprivateCount := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sum_range_succ, ← ih]; rfl

theorem participationCount_chain (n : ℕ) (p : P) :
    (D.chain n).participationCount p = ∑ t ∈ range n, (D.step t).participationCount p := by
  induction n with
  | zero =>
      change Nat.card {g : Empty // _} = 0
      simp
  | succ n ih =>
      rw [sum_range_succ, ← ih]
      change Nat.card {g : (D.chain n).nonprivateLocations ⊕ (D.step n).nonprivateLocations //
        p ∈ Sum.elim (D.chain n).participants (D.step n).participants g} = _
      rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
      rfl

theorem exists_participants_chain (n : ℕ) (g : (D.chain n).nonprivateLocations) :
    ∃ t < n, ∃ g' : (D.step t).nonprivateLocations,
      (D.chain n).participants g = (D.step t).participants g' := by
  induction n with
  | zero => exact nomatch g
  | succ n ih =>
      rcases g with g | g
      · obtain ⟨t, ht, g', h⟩ := ih g
        exact ⟨t, by omega, g', h⟩
      · exact ⟨n, by omega, g, rfl⟩

theorem isExpansionBounded_chain {r : ℕ} {S : ℝ} (n : ℕ)
    (h : ∀ t < n, (D.step t).IsExpansionBounded r S) : (D.chain n).IsExpansionBounded r S := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih fun t ht ↦ h t (by omega), h n (by omega)⟩

theorem isMonomialBounded_chain {K : ℕ} (n : ℕ)
    (h : ∀ t < n, (D.step t).IsMonomialBounded K) : (D.chain n).IsMonomialBounded K := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih fun t ht ↦ h t (by omega), h n (by omega)⟩

/-- The protocol, read as one distributed construction of Theorem 5.2 whose gate operators are
the sums of their recorded monomial expansions. -/
def toGateMapConstruction (hL : 0 < L) : GateMapConstruction P where
  nonemptyParties := ⟨D.site (⟨0, hL⟩, ⟨0, hL⟩)⟩
  initialSpace := D.initialSpace
  finite_initialSpace := D.finite_initialSpace
  initialVector := D.initialVector
  norm_initialVector := D.norm_initialVector
  physicalDimension := D.physicalDimension
  physicalOrder := D.physicalOrder
  physicalOrder_nodup := D.physicalOrder_nodup
  mem_physicalOrder := D.mem_physicalOrder
  privateOutput := D.privateOutput
  finite_privateOutput := D.finite_privateOutput
  circuit := EffectCircuit.castLayouts D.layout_zero D.layout_changes (D.chain D.changes).produce
  gateMaps := EffectCircuit.exactGateMaps _

theorem physicalConfigEquiv_apply (f : (p : P) → Fin (D.physicalDimension p))
    (v : SquareLatticeVertex L L) :
    D.physicalConfigEquiv f v = Fin.cast (D.physicalDimension_site v) (f (D.site v)) := by
  simp only [physicalConfigEquiv]; rfl

theorem physicalDensity_toGateMapConstruction (hL : 0 < L) :
    (D.toGateMapConstruction hL).physicalDensity =
      D.physicalDensity.submatrix D.physicalConfigEquiv D.physicalConfigEquiv := by
  classical
  let := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
  set e := D.physicalConfigEquiv
  set J := familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
    D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput
  set w := J (Layout.memCongr D.layout_changes (D.trajectory D.changes))
  have hC : (D.toGateMapConstruction hL).physicalDensity =
      Matrix.partialTraceRight (Matrix.euclideanOuterProduct w w) := by
    have h := OriginalCircuit.evalWithGateMaps_castLayouts_produce D.layout_zero
      D.layout_changes (D.chain D.changes) (D.toGateMapConstruction hL).input.vector
    simp only at h
    change Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (J ((D.toGateMapConstruction hL).circuit.evalWithGateMaps
        (D.toGateMapConstruction hL).gateMaps (D.toGateMapConstruction hL).input.vector))
      (J ((D.toGateMapConstruction hL).circuit.evalWithGateMaps
        (D.toGateMapConstruction hL).gateMaps (D.toGateMapConstruction hL).input.vector))) = _
    have h' : (D.toGateMapConstruction hL).circuit.evalWithGateMaps
        (D.toGateMapConstruction hL).gateMaps (D.toGateMapConstruction hL).input.vector =
        Layout.memCongr D.layout_changes (D.trajectory D.changes) := by
      rw [← D.eval_chain_trajectory]
      exact h
    rw [h']
  have hD : D.physicalDensity = Matrix.partialTraceRight
      ((Matrix.euclideanOuterProduct w w).submatrix (e.prodCongr (Equiv.refl _)).symm
        (e.prodCongr (Equiv.refl _)).symm) := by
    unfold physicalDensity
    congr 1
  rw [hC, hD, Matrix.partialTraceRight_submatrix_prod_equiv, Matrix.submatrix_submatrix]
  ext x y
  simp

/-- Every party has a positive physical dimension when `q` is positive. -/
theorem physicalDimension_pos (hq : 0 < q) (p : P) : 0 < D.physicalDimension p := by
  by_cases hp : p ∈ Set.range D.site
  · obtain ⟨v, rfl⟩ := hp
    rw [D.physicalDimension_site]
    exact hq
  · rw [D.physicalDimension_eq_one p hp]
    exact one_pos

/-- The physical coordinate of a party read from a local index in `Fin q`: the index itself at
the unit-square party of a site, and the only coordinate elsewhere. -/
def physicalOut (p : P) (i : Fin q) : Fin (D.physicalDimension p) :=
  ⟨i % D.physicalDimension p, Nat.mod_lt _ (D.physicalDimension_pos i.pos p)⟩

/-- Reading every party at the fold of its anchor inverts the identification of the physical
configurations of the parties with the configurations of the square. -/
theorem physicalOut_foldVertex (hL : 0 < L) (x : Configuration L q) :
    (fun p ↦ D.physicalOut p (x (foldVertex hL (D.placement.anchor p)))) =
      D.physicalConfigEquiv.symm x := by
  rw [Equiv.eq_symm_apply]
  funext v
  rw [physicalConfigEquiv_apply]
  obtain ⟨h0, hx, hy⟩ := D.placement_site v
  have hanchor : D.placement.anchor (D.site v) = (v.1.1, v.2.1) := by
    simp [DyadicPlacement.anchor, dyadicAnchor, h0, hx, hy]
  rw [hanchor, foldVertex_of_lt hL v.1.2 v.2.2]
  ext
  simp [physicalOut, D.physicalDimension_site, Nat.mod_eq_of_lt (x v).2]

open DistributedOperatorContraction in
/-- **From a compressed density to an operator party network on dyadic anchors.** Let a
distributed operator contraction on the parties of a protocol be within `ε` of the physical
density of the protocol, with link alphabets of size at most `C₁ L ^ α`, at most `deg` links at
each party, and links only between parties of a common nonprivate gate. Enumerating its
alphabets gives an operator party network on the dyadic anchors of the protocol with these
bounds, the separation constant `b` of the protocol, and
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ ε + (2 C² + 2 C) L⁻¹⁰`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the conclusion of Theorem 5.2,
`04-compression.tex:150–175`, applied in §8.1, `07-assembly.tex:53–63`, with the density
estimate `eq:protocol-density`, `07-assembly.tex:33–41`. -/
theorem exists_partyNetwork_of_contractedOperator (hL : 0 < L) {Ω : StateSpace L q} {C : ℝ}
    {b k r : ℕ} (h : D.IsDistributionProtocol Ω C b k r) (hC : 0 ≤ C) (hΩ : ‖Ω‖ = 1)
    [DecidableEq P] {Gate : Type} [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset P) (root : Gate → P)
    (hroot : ∀ g ∈ gates, root g ∈ participants g) (Label : Gate → Type)
    [∀ g, Fintype (Label g)] (m : ℕ) (c : (g : Gate) → Label g → ℂ)
    (T : (p : P) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin m) →
        Matrix (Fin (D.physicalDimension p)) (Fin (D.physicalDimension p)) ℂ)
    {ε C₁ : ℝ} {α deg : ℕ}
    (herr : Matrix.rectangularTraceNorm
      (contractedOperator gates participants root hroot Label m c T -
        D.physicalDensity.submatrix D.physicalConfigEquiv D.physicalConfigEquiv) ≤ ε)
    (hdim : ∀ e : Link gates participants root,
      (Fintype.card (alphabet gates participants root Label m e) : ℝ) ≤ C₁ * (L : ℝ) ^ α)
    (hinc : ∀ j, (incidentDistributedLinks gates participants root j).card ≤ deg)
    (hloc : ∀ e : Link gates participants root, ∀ j l,
      j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
        ∃ t < D.changes, ∃ g, j ∈ (D.step t).participants g ∧ l ∈ (D.step t).participants g) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (N : PartyNetwork P Λ (q * q)),
      DyadicPlacement.DegreeBounded N.src N.tgt deg ∧
      D.placement.SeparationBounded N.src N.tgt b ∧
      (∀ ℓ, (N.dim ℓ : ℝ) ≤ C₁ * (L : ℝ) ^ α) ∧
      Matrix.rectangularTraceNorm
        (N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) -
          Matrix.euclideanOuterProduct Ω Ω) ≤ ε + (2 * (C * C) + 2 * C) / (L : ℝ) ^ 10 := by
  classical
  set e := D.physicalConfigEquiv
  let N := toPartyNetwork gates participants root hroot Label m c T D.physicalOut D.physicalOut
  have hmem : ∀ ℓ : Link gates participants root,
      src gates participants root ℓ ∈ distributedLinkParties root ℓ.1 ∧
        tgt gates participants root ℓ ∈ distributedLinkParties root ℓ.1 := fun ℓ ↦ by
    rw [← endpoints_eq]
    simp
  refine ⟨Link gates participants root, inferInstance, inferInstance, N, ?_, ?_, hdim, ?_⟩
  · intro p
    refine (Finset.card_le_card_of_injOn Subtype.val (fun ℓ hℓ ↦ ?_)
      Subtype.val_injective.injOn).trans (hinc p)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    simp only [incidentDistributedLinks, Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨ℓ.2, ?_⟩
    rw [← endpoints_eq]
    rcases hℓ with h' | h'
    · simp [N, toPartyNetwork] at h'
      simp [h']
    · simp [N, toPartyNetwork] at h'
      simp [h']
  · exact h.separationBounded _ _ fun ℓ ↦ hloc ℓ _ _ (hmem ℓ).1 (hmem ℓ).2
  · have hσ : N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) =
        (contractedOperator gates participants root hroot Label m c T).submatrix e.symm e.symm := by
      ext x y
      rw [operatorCoeff_toPartyNetwork, D.physicalOut_foldVertex hL x,
        D.physicalOut_foldVertex hL y]
      rfl
    have hsplit : N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) -
        Matrix.euclideanOuterProduct Ω Ω =
        Matrix.reindex e e (contractedOperator gates participants root hroot Label m c T -
          D.physicalDensity.submatrix e e) +
          (D.physicalDensity - Matrix.euclideanOuterProduct Ω Ω) := by
      rw [hσ]
      ext x y
      simp
    rw [hsplit]
    refine (Matrix.rectangularTraceNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.rectangularTraceNorm_reindex]
      exact herr
    · exact h.rectangularTraceNorm_physicalDensity_sub_le (Nat.one_le_iff_ne_zero.mpr hL.ne')
        hC hΩ

end TNLean.PEPS.Approximation.DyadicProtocol

namespace TNLean.PEPS.Approximation

open Finset TNLean.PEPS.PairEffect

/-- A protocol with the bounds of §8 for fixed constants, on a square of some side `L ≥ 2`,
together with its unit target vector. These instances form the family of constructions to which
Theorem 5.2 is applied. -/
private structure ProtocolInstance (q : ℕ) (C : ℝ) (b k r : ℕ) where
  size : ℕ
  two_le : 2 ≤ size
  Party : Type
  [fintype : Fintype Party]
  protocol : DyadicProtocol size q Party
  target : StateSpace size q
  norm_target : ‖target‖ = 1
  isDistributionProtocol : protocol.IsDistributionProtocol target C b k r

attribute [instance] ProtocolInstance.fintype

private theorem natCast_floor_le_max (x : ℝ) : (⌊x⌋₊ : ℝ) ≤ max x 0 := by
  rcases le_total 0 x with hx | hx
  · exact (Nat.floor_le hx).trans (le_max_left _ _)
  · rw [Nat.floor_eq_zero.mpr (hx.trans_lt one_pos)]
    simp

theorem largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences
    (hprot : LargeSizeDyadicProtocolConsequences) : LargeSizeDyadicOperatorNetwork := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, b, k, r, L₀, hall⟩ := hprot q hq J Δ hJ hΔ
  let size : ProtocolInstance q C b k r → ℝ := fun i ↦ i.size
  have hsize : ∀ i, 2 ≤ size i := fun i ↦ by
    change (2 : ℝ) ≤ (i.size : ℝ)
    exact_mod_cast i.two_le
  let C₀ : ∀ i : ProtocolInstance q C b k r, GateMapConstruction i.Party := fun i ↦
    i.protocol.toGateMapConstruction (by have := i.two_le; omega)
  have hN₀ : ∀ i, ((C₀ i).circuit.expandedGateCount : ℝ) ≤ (max C 0 * b) * size i ^ 3 := by
    intro i
    have hD := i.isDistributionProtocol
    have hcount : (C₀ i).circuit.expandedGateCount =
        (i.protocol.chain i.protocol.changes).nonprivateCount :=
      OriginalCircuit.expandedGateCount_castLayouts_produce _ _ _
    rw [hcount, DyadicProtocol.nonprivateCount_chain]
    have hsum : ∑ t ∈ range i.protocol.changes, (i.protocol.step t).nonprivateCount ≤
        i.protocol.changes * b := by
      simpa using Finset.sum_le_card_nsmul _ _ b fun t ht ↦
        hD.nonprivateCount_le t (Finset.mem_range.mp ht)
    calc ((∑ t ∈ range i.protocol.changes, (i.protocol.step t).nonprivateCount : ℕ) : ℝ)
        ≤ (i.protocol.changes : ℝ) * b := by exact_mod_cast hsum
      _ ≤ (max C 0 * size i ^ 3) * b := by
          gcongr
          exact hD.changes_le.trans (by gcongr; exact le_max_left _ _)
      _ = (max C 0 * b) * size i ^ 3 := by ring
  have hphysical₀ : ∀ i j, ((C₀ i).physicalDimension j : ℝ) ≤ q * size i ^ 0 := by
    intro i j
    change (i.protocol.physicalDimension j : ℝ) ≤ _
    rw [pow_zero, mul_one]
    by_cases hj : j ∈ Set.range i.protocol.site
    · obtain ⟨v, rfl⟩ := hj
      rw [i.protocol.physicalDimension_site]
    · rw [i.protocol.physicalDimension_eq_one j hj]
      exact_mod_cast (show 1 ≤ q by omega)
  have harity₀ : ∀ i g, ((C₀ i).circuit.participants g).card ≤ b := by
    intro i g
    obtain ⟨g', hg'⟩ : ∃ g' : (i.protocol.chain i.protocol.changes).nonprivateLocations,
        (C₀ i).circuit.participants g = _ :=
      OriginalCircuit.exists_participants_castLayouts_produce _ _ _ g
    obtain ⟨t, ht, g'', hg''⟩ := i.protocol.exists_participants_chain _ g'
    rw [hg', hg'']
    exact i.isDistributionProtocol.card_participants_le t ht g''
  have hlifetime₀ : ∀ i j, Nat.card {g : (C₀ i).circuit.gateLocations //
      j ∈ (C₀ i).circuit.participants g} ≤ b := by
    intro i j
    have : Nat.card {g : (C₀ i).circuit.gateLocations // j ∈ (C₀ i).circuit.participants g} =
        (i.protocol.chain i.protocol.changes).participationCount j :=
      OriginalCircuit.participationCount_castLayouts_produce _ _ _ j
    refine (this.trans ?_).trans_le (i.isDistributionProtocol.participation_le j)
    rw [DyadicProtocol.participationCount_chain]
    rfl
  have hExpansion : ∀ q' : ℕ, ∃ (r' : ℕ) (C_K C_C : ℝ) (u v : ℕ),
      0 ≤ C_K ∧ 0 ≤ C_C ∧ ∀ i,
        ∃ (lists : (C₀ i).circuit.GateLists) (K : ℕ),
          ((C₀ i).circuit.reexpand lists).IsTermwiseBounded r' (C_C * (size i) ^ v) ∧
          (∀ g, ((C₀ i).circuit.reexpand lists).monomialCount g ≤ K) ∧
          (K : ℝ) ≤ C_K * (size i) ^ u ∧
          ((C₀ i).circuit.reexpand lists).IsGateApproximation ((size i) ^ q')⁻¹
            ((C₀ i).circuit.reexpandGateMaps lists (C₀ i).gateMaps) := by
    intro q'
    refine ⟨r, max C 0, max C 0, k, k, le_max_right _ _, le_max_right _ _, fun i ↦ ?_⟩
    have hD := i.isDistributionProtocol
    have hpow : C * (size i) ^ k ≤ max C 0 * (size i) ^ k :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith [hsize i]) _)
    refine ⟨(C₀ i).circuit.selfLists, ⌊C * (size i) ^ k⌋₊, ?_, ?_, ?_, ?_⟩
    · exact OriginalCircuit.isTermwiseBounded_castLayouts_produce _ _ _
        (i.protocol.isExpansionBounded_chain _ hD.expansionBounded) hpow
    · exact OriginalCircuit.monomialCount_castLayouts_produce_le _ _ _
        (i.protocol.isMonomialBounded_chain _ hD.monomialBounded)
    · refine (natCast_floor_le_max _).trans (max_le hpow ?_)
      exact mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith [hsize i]) _)
    · exact OriginalCircuit.isGateApproximation_castLayouts_produce _ _ _
        (inv_nonneg.mpr (pow_nonneg (by linarith [hsize i]) _))
  obtain ⟨r', C_p, α, hCp, hα, hfam⟩ :=
    GateMapConstruction.exists_uniform_approximate_sampled_network size hsize
      (fun i ↦ i.Party) C₀ b 3 0 (max C 0 * b) q
      (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      hN₀ hphysical₀ harity₀ hlifetime₀ hExpansion 5 (by norm_num)
  sorry

end TNLean.PEPS.Approximation
