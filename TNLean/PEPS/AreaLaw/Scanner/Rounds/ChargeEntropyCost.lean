/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Histories.DesignatedMoveCost
import TNLean.PEPS.AreaLaw.Scanner.Rounds.PhysicalBandCommutation
import QICLean.ManyBody.Replica.BandMetric.MoveEntropy
import QICLean.ManyBody.Replica.BandMetric.SplitEntropy

/-!
# Conditional mutual information sampled by the actual charge

The classical move cost is specialized to actual regional conditional mutual
information on the physical and auxiliary factors. Arbitrary trial sets are
intersected with the old middle before taking their entropy. On an actual
moved set that intersection disappears, and the cost is exactly the entropy
of the scanner's selected-side quantum move, including disabled choices.

The resulting good-history inequality is pointwise in a single pure vector.
All conditional choices use the same old partition and vector. Classical
history weights are not identified with coherent or Fourier measures. No
pre-vector, transported state, or complete scanner data is assumed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 321–330, and `08-scanner.tex`, lines 331–337
and 442–451, at `openai/math@adc7f124`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSplitIncidenceCost_eq_sum_splitEta`: designated
  incidence costs and old-leaf split entropy.
-/

section ChargeEntropyCost

open ManyBody (ambientDilation planeDomainGraph ambientDepth supDist)

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower TensorPower.ReplicaTransport
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
/-- An arbitrary trial set gives nonnegative cost because only its old-middle
part moves; it is disjoint from both old receiving sides. -/
theorem augmentedMove_eta_nonneg (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V)
    (side : Bool) (B : Finset V) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    0 ≤ moveEta n (augmentedPartition σ) (augmentedMove σ side B) θ :=
  moveEta_nonneg n _ (augmentedPartition_isPartition σ) _
    (augmentedMove_isValid σ side B) θ

omit [Fintype I] [LinearOrder I] in
/-- An empty physical move has zero entropy on either side. -/
@[simp] theorem augmentedMove_eta_empty (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V)
    (side : Bool) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    moveEta n (augmentedPartition σ) (augmentedMove σ side ∅) θ = 0 := by
  cases side <;> simp [augmentedMove]

namespace CollarScan

variable (S : CollarScan V I) (n : V ⊕ Bool → ℕ)

/-- The side-dependent regional entropy cost of the old-middle part of a trial
set. The auxiliary factors remain fixed on their respective sides. -/
noncomputable def chargeEntropyCost {k : ℕ} (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) : Fin S.K → Bool → Finset V → ℝ :=
  fun g side B => moveEta n (augmentedPartition (S.oldChargeState h g))
    (augmentedMove (S.oldChargeState h g) side B) θ

/-- Nonnegativity holds for every trial set, as required by the classical
expected-cost inequality, before any actual-move inclusion is used. -/
theorem chargeEntropyCost_nonneg {k : ℕ} (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) (g : Fin S.K) (side : Bool) (B : Finset V) :
    0 ≤ S.chargeEntropyCost n h θ g side B :=
  augmentedMove_eta_nonneg n _ side B θ

/-- Only a proved inclusion in the old middle permits removal of the
intersection from the entropy cost. The conditioning side is retained. -/
theorem chargeEntropyCost_eq_cmi_of_subset {k : ℕ} (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) (g : Fin S.K) (side : Bool) (B : Finset V)
    (hB : B ⊆ middle (S.oldChargeState h g)) :
    S.chargeEntropyCost n h θ g side B =
      if side then
        ManyBody.conditionalMutualInformation (fun v => Fin (n v)) θ
          (B.map ⟨Sum.inl, Sum.inl_injective⟩)
          (augmentedPartition (S.oldChargeState h g)).P
          (augmentedPartition (S.oldChargeState h g)).F
      else
        ManyBody.conditionalMutualInformation (fun v => Fin (n v)) θ
          (B.map ⟨Sum.inl, Sum.inl_injective⟩)
          (augmentedPartition (S.oldChargeState h g)).F
          (augmentedPartition (S.oldChargeState h g)).P := by
  cases side <;> simp [chargeEntropyCost, augmentedMove, moveEta,
    Finset.inter_eq_left.mpr hB]

/-- The actual charge entropy is the entropy of its removed old-middle set.
Disabled choices stay put and have the same zero entropy as an empty move. -/
theorem quantumChargeMove_eta (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    moveEta n (augmentedPartition σ) (S.quantumChargeMove g r k c σ) θ =
      moveEta n (augmentedPartition σ)
        (augmentedMove σ c.1 (middle σ \ middle (S.chargeStep g r k c σ))) θ := by
  cases hs : S.selected g r k c with
  | none =>
    simp only [quantumChargeMove, chargeStep, hs, moveEta, Finset.sdiff_self]
    exact (augmentedMove_eta_empty n σ c.1 θ).symm
  | some i =>
    by_cases hi : (S.ball i ∩ receiving σ c.1).Nonempty ∧
        (S.ball i ∩ middle σ).Nonempty
    · rw [S.chargeStep_moves_middle_part g r k c σ i hs hi]
      simp only [quantumChargeMove, hs, hi]
      congr 1
      cases c.1 <;> simp [augmentedMove, Finset.inter_assoc]
    · have hstep : S.chargeStep g r k c σ = σ := by simp [chargeStep, hs, charge, hi]
      simp only [quantumChargeMove, hs, hi, ↓reduceIte, hstep, Finset.sdiff_self, moveEta]
      exact (augmentedMove_eta_empty n σ c.1 θ).symm

/-- The actual classical removed-set cost is the sum of actual selected-side
quantum move entropies at the same old history and vector. -/
theorem chargeMoveCost_chargeEntropyCost {k : ℕ} (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) (c : ChargeChoices S.K S.M) :
    S.chargeMoveCost h (S.chargeEntropyCost n h θ) c =
      ∑ g, moveEta n (augmentedPartition (S.oldChargeState h g))
        (S.quantumChargeMove g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)) θ := by
  unfold chargeMoveCost chargeEntropyCost
  apply Finset.sum_congr rfl
  intro g _
  rw [state_extendHistory]
  exact (S.quantumChargeMove_eta n g (h.1 g) (k + 1) (c g)
    (S.oldChargeState h g) θ).symm

/-- Good actual histories sample the canonical regional entropy cost of each
designated splitting incidence with coefficient `c / (nD)`, where
`c = 1 / (2(C₁ + 1))`. Equal anchors retain their distinct interaction labels.
This is a pointwise entropy inequality, before coherent or Fourier integration. -/
theorem good_designatedEntropyCost_le_expected_chargeEta_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x => ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (n : ↥Λ ⊕ Bool → ℕ)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v)))
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    (hgood : S.IsGoodOldHistory h) :
    0 < 1 / (2 * (S.C₁ + 1)) ∧
      ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
          S.designatedSplitIncidenceCost L h (S.chargeEntropyCost n h θ) ≤
        ∑ c : ChargeChoices S.K S.M, chargeWeight c *
          ∑ g, moveEta n (augmentedPartition (S.oldChargeState h g))
            (S.quantumChargeMove g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)) θ := by
  have hbound := good_designatedSplitIncidenceCost_le_expected_chargeMoveCost_planeDomainGraph
    hT S hgraph hdepth h (S.chargeEntropyCost n h θ) (S.chargeEntropyCost_nonneg n h θ)
    hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood
  simpa only [S.chargeMoveCost_chargeEntropyCost n h θ] using hbound

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

end ChargeEntropyCost

section SplitEntropyCost

/-!
## Designated incidence costs and old-leaf split entropy

For compatible designated supports, the actual side-labelled incidence sum
equals the transport definition of split entropy at the old leaf. All sums
retain interaction labels, including distinct labels sharing an anchor.
The assertion is algebraic; the actual geometric compatibility theorem is
supplied separately before specializing this identity to the scanner.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 336–347, and `08-scanner.tex`, lines 331–337,
at `openai/math@adc7f124`.
-/

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport
namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
private theorem lifted_inter_part (σ : PhysicalPartition V) (B : Finset V)
    (part : Option Bool) :
    B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
        Finset.univ.filter (fun x => augmentedState σ x = part) =
      (B ∩ Finset.univ.filter (fun x => σ x = part)).map
        (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyB, hyp⟩ := Finset.mem_inter.mp hy
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_map.mp hyB
    exact Finset.mem_map.mpr ⟨x, Finset.mem_inter.mpr
      ⟨hxB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hyp).2⟩⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨hxB, hxp⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_map.mpr ⟨x, hxB, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxp).2⟩⟩

omit [Fintype I] [LinearOrder I] in
open Classical in
private theorem physical_incidence_sum (n : V ⊕ Bool → ℕ)
    (σ : PhysicalPartition V) (B : Finset V)
    (hcase : (augmentedPartition σ).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (augmentedPartition σ).SplitsToP (B.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (augmentedPartition σ).SplitsToF (B.map ⟨Sum.inl, Sum.inl_injective⟩))
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    (∑ side : Bool, if (B ∩ receiving σ side).Nonempty ∧ (B ∩ middle σ).Nonempty then
      moveEta n (augmentedPartition σ) (augmentedMove σ side (B ∩ middle σ)) θ else 0) =
      if (augmentedPartition σ).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩) then 0 else
        splitBandEta n (augmentedPartition σ) (B.map ⟨Sum.inl, Sum.inl_injective⟩) θ := by
  classical
  have hY : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).Y = (B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B none
  have hP : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).P = (B ∩ receiving σ false).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B (some false)
  have hF : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).F = (B ∩ receiving σ true).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B (some true)
  have heq := incidence_sum_eq_splitBandEta n (augmentedPartition σ)
    (augmentedPartition_isPartition σ) (B.map ⟨Sum.inl, Sum.inl_injective⟩) hcase θ
  rw [Fintype.sum_bool]
  simpa only [hY, hP, hF, Finset.map_nonempty, augmentedMove,
    Finset.inter_assoc, Finset.inter_self, Bool.false_eq_true, ↓reduceIte] using heq

namespace CollarScan

variable (S : CollarScan V I) (n : V ⊕ Bool → ℕ)

/-- Compatible physically embedded supports identify the labelled incidence
cost with the actual old-leaf split entropy. Compatibility is a generic
premise here; the physical specialization derives it from scanner geometry. -/
theorem designatedSplitIncidenceCost_eq_sum_splitEta {k L : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (E : EnergyTerms (V ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hcompat : (S.chargeTransportData histTree choiceTree).SupportCompatible E)
    (h : History S.K S.m S.M k) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    S.designatedSplitIncidenceCost L h (S.chargeEntropyCost n h θ) =
      ∑ i, (S.chargeTransportData histTree choiceTree).splitEta E i ⟨h, none⟩ θ := by
  classical
  unfold designatedSplitIncidenceCost TransportData.splitEta
  simp only [designatedSplitIncidences, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro i _
  have hcase := hcompat ⟨h, none⟩ i g
  have hcase' : ((S.chargeTransportData histTree choiceTree).old h g).Contains (E.support i) ∨
      ((S.chargeTransportData histTree choiceTree).old h g).SplitsToP (E.support i) ∨
      ((S.chargeTransportData histTree choiceTree).old h g).SplitsToF (E.support i) :=
    hcase.imp_right And.left
  rw [hsupport i] at hcase' ⊢
  have hphysical := physical_incidence_sum n (S.oldChargeState h g)
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) hcase' θ
  have hconditional (P : Prop) (η : ℝ) :
      (if P then 0 else η) = (if ¬ P then η else 0) := by
    by_cases hP : P
    · rw [ite_eq_left hP, ite_eq_right (show ¬ ¬ P from fun hn => hn hP)]
    · rw [ite_eq_right hP, ite_eq_left hP]
  have hsplit := hphysical.trans (hconditional
    ((augmentedPartition (S.oldChargeState h g)).Contains
      ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩))
    (splitBandEta n (augmentedPartition (S.oldChargeState h g))
      ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) θ))
  delta chargeEntropyCost TransportData.leafPart chargeTransportData
  exact hsplit

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

end SplitEntropyCost
