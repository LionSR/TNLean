/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EffectCircuitResources
import TNLean.PEPS.Approximation.EffectReplacementExpansion
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt

/-!
# Source-free exchange of the physical output block

The literal exchange moves the physical registers before the auxiliary registers.
Its tensor action is proved directly. The exchange introduces no gate or source
occurrences and preserves their labels, coefficients, endpoints and lifetime counts.

Source: polynomial-PEPS, `04-compression.tex`, lines 210–229.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-physicalfirstexchange-01
TNLean.PEPS.PairEffect.SourceCircuit.branchCoefficient_physicalFirstLocationsEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-02
TNLean.PEPS.PairEffect.SourceCircuit.branchLabels_physicalFirstLocationsEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-03
TNLean.PEPS.PairEffect.SourceCircuit.card_gateLocations_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-04
TNLean.PEPS.PairEffect.SourceCircuit.card_sourceLocations_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-05
TNLean.PEPS.PairEffect.SourceCircuit.endpoints_physicalFirstSourcesEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-06
TNLean.PEPS.PairEffect.SourceCircuit.eval_exchangeBlocks_operator
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-07
TNLean.PEPS.PairEffect.SourceCircuit.eval_exchangeBlocks_threeFactors
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-08
TNLean.PEPS.PairEffect.SourceCircuit.eval_exchangeBlocks_triple_tmul
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-09
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-10
TNLean.PEPS.PairEffect.SourceCircuit.isExpansionBounded_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-11
TNLean.PEPS.PairEffect.SourceCircuit.participants_physicalFirstLocationsEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-12
TNLean.PEPS.PairEffect.SourceCircuit.participationCount_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-13
TNLean.PEPS.PairEffect.SourceCircuit.physicalFirstLocationsEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-14
TNLean.PEPS.PairEffect.SourceCircuit.physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-15
TNLean.PEPS.PairEffect.SourceCircuit.physicalFirstParticipationEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-16
TNLean.PEPS.PairEffect.SourceCircuit.physicalFirstSourcesEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-17
TNLean.PEPS.PairEffect.SourceCircuit.slotCount_physicalFirstLocationsEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-18
TNLean.PEPS.PairEffect.SourceCircuit.sourceDims_physicalFirstSourcesEquiv
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-19
TNLean.PEPS.PairEffect.SourceCircuit.sourceOrder_exchangeBlocks
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-20
TNLean.PEPS.PairEffect.SourceCircuit.sourceOrder_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstexchange-21
TNLean.PEPS.PairEffect.SourceCircuit.sourceVectorAt_physicalFirstSourcesEquiv
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceCircuit
open ContinuousLinearMap
variable {P : Type}

/-- The literal source-free exchange moves the physical block before the
retained auxiliary block without changing their internal orders.
Source: polynomial-PEPS, `04-compression.tex:210–227`. -/
theorem eval_exchangeBlocks_triple_tmul (aux physical priv : Layout P)
    (u : Mem aux) (p : Mem physical) (v : Mem priv) :
    (exchangeBlocks aux physical priv).eval
      ((appendIso aux (physical ++ priv)).symm
        (u ⊗ₜ[ℂ] (appendIso physical priv).symm (p ⊗ₜ[ℂ] v))) =
      (appendIso physical (aux ++ priv)).symm
        (p ⊗ₜ[ℂ] (appendIso aux priv).symm (u ⊗ₜ[ℂ] v)) := by
  rw [eval_exchangeBlocks]
  exact Word.eval_exchangeBlocks_appendIso_symm aux physical priv u p v

/-- Linear extension of the actual three-block exchange to arbitrary vectors.
Source: polynomial-PEPS, `04-compression.tex:210–227`. -/
theorem eval_exchangeBlocks_threeFactors (aux physical priv : Layout P) :
    (exchangeBlocks aux physical priv).eval ∘L
        isoL (appendIso aux (physical ++ priv)).symm ∘L
          (isoL (appendIso physical priv).symm).lTensor (Mem aux) =
      isoL (appendIso physical (aux ++ priv)).symm ∘L
        (isoL (appendIso aux priv).symm).lTensor (Mem physical) ∘L
          leftCommL (Mem aux) (Mem physical) (Mem priv) := by
  apply clm_ext_tmul
  intro u pv
  induction pv using TensorProduct.inductionOn with
  | tmul p v =>
      exact eval_exchangeBlocks_triple_tmul aux physical priv u p v
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The actual exchange operator is the tensor-factor permutation on every
input vector. Source: polynomial-PEPS, `04-compression.tex:210–227`. -/
theorem eval_exchangeBlocks_operator (aux physical priv : Layout P) :
    (exchangeBlocks aux physical priv).eval =
      isoL (appendIso physical (aux ++ priv)).symm ∘L
        (isoL (appendIso aux priv).symm).lTensor (Mem physical) ∘L
          leftCommL (Mem aux) (Mem physical) (Mem priv) ∘L
            (isoL (appendIso physical priv)).lTensor (Mem aux) ∘L
              isoL (appendIso aux (physical ++ priv)) := by
  ext x
  have h := DFunLike.congr_fun (eval_exchangeBlocks_threeFactors aux physical priv)
    (((appendIso physical priv).lTensor (Mem aux)) ((appendIso aux (physical ++ priv)) x))
  simpa only [comp_apply, ← isoL_lTensor, isoL_apply,
    ← LinearIsometryEquiv.symm_lTensor, LinearIsometryEquiv.symm_apply_apply] using h

/-- Put the actual physical registers first using only the source-free block
exchange after the original source circuit. Source: polynomial-PEPS,
`04-compression.tex:210–227`. -/
def physicalFirstOutput (aux physical priv : Layout P) {a : Layout P}
    (w : SourceCircuit a (aux ++ (physical ++ priv))) :
    SourceCircuit a (physical ++ (aux ++ priv)) :=
  .comp w (exchangeBlocks aux physical priv)

/-- The appended exchange is allowed precisely when the preceding circuit is.
Source: polynomial-PEPS, `04-compression.tex:210–227`. -/
theorem isAllowed_physicalFirstOutput (aux physical priv : Layout P) {a : Layout P}
    (w : SourceCircuit a (aux ++ (physical ++ priv))) :
    (physicalFirstOutput aux physical priv w).IsAllowed ↔ w.IsAllowed :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, isAllowed_exchangeBlocks aux physical priv⟩⟩

/-- Each original gate occurrence remains at its literal left-summand position;
the final exchange has no gate occurrences. Source: polynomial-PEPS,
`04-compression.tex:210–229`. -/
def physicalFirstLocationsEquiv (aux physical priv : Layout P) {a : Layout P}
    (w : SourceCircuit a (aux ++ (physical ++ priv))) :
    w.gateLocations ≃ (physicalFirstOutput aux physical priv w).gateLocations where
  toFun g := Sum.inl g
  invFun
    | Sum.inl g => g
    | Sum.inr g => (exchangeBlocksLocationsEquivEmpty aux physical priv g).elim
  left_inv _ := rfl
  right_inv
    | Sum.inl _ => rfl
    | Sum.inr g => (exchangeBlocksLocationsEquivEmpty aux physical priv g).elim

/-- Source locations retain their actual common-slot indices as well as their
gate occurrences. Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
def physicalFirstSourcesEquiv (aux physical priv : Layout P) {a : Layout P}
    (w : SourceCircuit a (aux ++ (physical ++ priv))) :
    w.sourceLocations ≃ (physicalFirstOutput aux physical priv w).sourceLocations where
  toFun e := ⟨Sum.inl e.1, e.2⟩
  invFun
    | ⟨Sum.inl g, i⟩ => ⟨g, i⟩
    | ⟨Sum.inr g, _⟩ => (exchangeBlocksLocationsEquivEmpty aux physical priv g).elim
  left_inv _ := rfl
  right_inv
    | ⟨Sum.inl _, _⟩ => rfl
    | ⟨Sum.inr g, _⟩ => (exchangeBlocksLocationsEquivEmpty aux physical priv g).elim

variable (aux physical priv : Layout P) {a : Layout P}
  (w : SourceCircuit a (aux ++ (physical ++ priv)))

/-- The actual gate participants are unchanged by the final exchange.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem participants_physicalFirstLocationsEquiv (g : w.gateLocations) :
    (physicalFirstOutput aux physical priv w).participants
      (physicalFirstLocationsEquiv aux physical priv w g) = w.participants g := rfl

/-- Every common source slot of the original gate is retained.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem slotCount_physicalFirstLocationsEquiv (g : w.gateLocations) :
    (physicalFirstOutput aux physical priv w).slotCount
      (physicalFirstLocationsEquiv aux physical priv w g) = w.slotCount g := rfl

/-- The original branch labels are retained at the same gate occurrences.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem branchLabels_physicalFirstLocationsEquiv (g : w.gateLocations) :
    (physicalFirstOutput aux physical priv w).branchLabels
      (physicalFirstLocationsEquiv aux physical priv w g) = w.branchLabels g := rfl

/-- The original scalar branch coefficients are unchanged.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem branchCoefficient_physicalFirstLocationsEquiv (g : w.gateLocations)
    (ξ : w.branchLabels g) :
    (physicalFirstOutput aux physical priv w).branchCoefficient
      (physicalFirstLocationsEquiv aux physical priv w g) ξ = w.branchCoefficient g ξ := rfl

/-- Source endpoints are the actual original parties after the exchange.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem endpoints_physicalFirstSourcesEquiv (e : w.sourceLocations) :
    (physicalFirstOutput aux physical priv w).endpoints
      (physicalFirstSourcesEquiv aux physical priv w e) = w.endpoints e := rfl

/-- The fixed endpoint dimensions of every actual source are unchanged.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem sourceDims_physicalFirstSourcesEquiv (e : w.sourceLocations) :
    (physicalFirstOutput aux physical priv w).sourceDims
      (physicalFirstSourcesEquiv aux physical priv w e) = w.sourceDims e := rfl

/-- Every actual prepared source vector is unchanged, not merely its norm or
coordinate dimension. Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem sourceVectorAt_physicalFirstSourcesEquiv (e : w.sourceLocations)
    (ξ : w.branchLabels e.1) :
    (physicalFirstOutput aux physical priv w).sourceVectorAt
      (physicalFirstSourcesEquiv aux physical priv w e) ξ = w.sourceVectorAt e ξ := rfl

/-- A source-free block exchange has no positions in the source preparation order.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem sourceOrder_exchangeBlocks : (exchangeBlocks aux physical priv).sourceOrder = [] := by
  cases h : (exchangeBlocks aux physical priv).sourceOrder with
  | nil => rfl
  | cons e es => exact (exchangeBlocksLocationsEquivEmpty aux physical priv e.1).elim

/-- The source preparation order is preserved under the literal source-location
inclusion. Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem sourceOrder_physicalFirstOutput :
    (physicalFirstOutput aux physical priv w).sourceOrder =
      w.sourceOrder.map (physicalFirstSourcesEquiv aux physical priv w) := by
  simp only [physicalFirstOutput, sourceOrder, sourceOrder_exchangeBlocks,
    List.map_nil, List.nil_append]
  rfl

/-- The gate occurrence cardinality is unchanged.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem card_gateLocations_physicalFirstOutput :
    Fintype.card (physicalFirstOutput aux physical priv w).gateLocations =
      Fintype.card w.gateLocations :=
  (Fintype.card_congr (physicalFirstLocationsEquiv aux physical priv w)).symm

/-- The actual source occurrence cardinality is unchanged.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem card_sourceLocations_physicalFirstOutput :
    Fintype.card (physicalFirstOutput aux physical priv w).sourceLocations =
      Fintype.card w.sourceLocations :=
  (Fintype.card_congr (physicalFirstSourcesEquiv aux physical priv w)).symm

/-- The occurrence set involving a given party is preserved by the actual
gate-location inclusion. Source: polynomial-PEPS, `04-compression.tex:140–142`
and `210–229`. -/
def physicalFirstParticipationEquiv (p : P) :
    {g : w.gateLocations // p ∈ w.participants g} ≃
      {g : (physicalFirstOutput aux physical priv w).gateLocations //
        p ∈ (physicalFirstOutput aux physical priv w).participants g} :=
  (physicalFirstLocationsEquiv aux physical priv w).subtypeEquiv (fun _ ↦ Iff.rfl)

/-- Reordering retained registers preserves whole-lifetime party participation.
Source: polynomial-PEPS, `04-compression.tex:140–142` and `210–229`. -/
theorem participationCount_physicalFirstOutput (p : P) :
    (physicalFirstOutput aux physical priv w).participationCount p =
      w.participationCount p :=
  (Nat.card_congr (physicalFirstParticipationEquiv aux physical priv w p)).symm

/-- The original expansion bounds remain exactly equivalent after reordering.
Source: polynomial-PEPS, `04-compression.tex:210–229`. -/
theorem isExpansionBounded_physicalFirstOutput (K : ℕ) (S : ℝ) :
    (physicalFirstOutput aux physical priv w).IsExpansionBounded K S ↔
      w.IsExpansionBounded K S :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, isExpansionBounded_exchangeBlocks aux physical priv K S⟩⟩

end TNLean.PEPS.PairEffect.SourceCircuit
