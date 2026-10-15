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

theorem isTermwiseBounded_produce (w : OriginalCircuit a b) {r : ℕ} {S : ℝ}
    (h : w.IsExpansionBounded r S) :
    (w.produce.reexpand w.produce.selfLists).IsTermwiseBounded r S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate owner hC L hL hG tail =>
      refine fun term hterm ↦ ⟨h.1 term hterm, h.2.trans' ?_⟩
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
    (w : OriginalCircuit a b) {r : ℕ} {S : ℝ} (h : w.IsExpansionBounded r S) :
    let W := EffectCircuit.castLayouts ha hb w.produce
    (W.reexpand W.selfLists).IsTermwiseBounded r S := by
  subst ha hb
  exact w.isTermwiseBounded_produce h

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

end TNLean.PEPS.Approximation.DyadicProtocol
