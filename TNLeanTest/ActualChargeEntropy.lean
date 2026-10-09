/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeEntropyCost
import TNLean.PEPS.AreaLaw.Scan.ActualChargeData

/-!
# Actual charge entropy regressions

These tests preserve the two receiving sides, the old-middle intersection on
arbitrary trial sets, and the distinction between disabled and empty moves.
No normalization assumption is available for the one-copy vector.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport
open Entropy (SiteConfig)
open scoped BigOperators
open TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ActualChargeEntropy

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

-- Trial sets may meet both old sides. The middle intersection is retained.
example (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V) (B : Finset V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n (augmentedPartition σ) (augmentedMove σ false B) θ =
      FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ
        ((B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩)
        (augmentedPartition σ).F (augmentedPartition σ).P := rfl

-- The far move exchanges the target and conditioning sides, not its vector.
example (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V) (B : Finset V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n (augmentedPartition σ) (augmentedMove σ true B) θ =
      FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ
        ((B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩)
        (augmentedPartition σ).P (augmentedPartition σ).F := rfl

example (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V) (side : Bool)
    (B : Finset V) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    0 ≤ moveEta n (augmentedPartition σ) (augmentedMove σ side B) θ :=
  augmentedMove_eta_nonneg n σ side B θ

-- Equality of entropy does not identify the empty move and stay constructors.
example : (Move.toP (∅ : Finset (Fin 2))) ≠ Move.stay := by
  intro h
  cases h

example (n : V → ℕ) (π : PYF V) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toP ∅) θ = moveEta n π .stay θ := by
  simp [moveEta]

example (n : V → ℕ) (π : PYF V) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toF ∅) θ = moveEta n π .stay θ := by
  simp [moveEta]

-- A blank actual padded slot is a genuine stay and has zero entropy.
example (S : CollarScan V I) (n : V ⊕ Bool → ℕ) (g r k : ℕ)
    (c : Bool × Fin S.M) (σ : PhysicalPartition V)
    (hslot : S.selected g r k c = none) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n (augmentedPartition σ) (S.quantumChargeMove g r k c σ) θ = 0 := by
  simp [CollarScan.quantumChargeMove, hslot, moveEta]

-- A selected label that does not split the receiving side and middle is disabled.
example (S : CollarScan V I) (n : V ⊕ Bool → ℕ) (g r k : ℕ)
    (c : Bool × Fin S.M) (σ : PhysicalPartition V) (i : I)
    (hslot : S.selected g r k c = some i)
    (hdisabled : ¬ ((S.ball i ∩ receiving σ c.1).Nonempty ∧
      (S.ball i ∩ middle σ).Nonempty)) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n (augmentedPartition σ) (S.quantumChargeMove g r k c σ) θ = 0 := by
  simp [CollarScan.quantumChargeMove, hslot, hdisabled, moveEta]

-- A nonempty trial set made entirely of assigned sites still has zero cost.
example (n : V ⊕ Bool → ℕ) (σ : PhysicalPartition V) (side : Bool)
    (B : Finset V) (hB : B ∩ middle σ = ∅)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n (augmentedPartition σ) (augmentedMove σ side B) θ = 0 := by
  cases side <;> simp [augmentedMove, hB]

-- The actual removed-set identity covers arbitrary histories and both sides.
example (S : CollarScan V I) (n : V ⊕ Bool → ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (c : ChargeChoices S.K S.M)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    S.chargeMoveCost h (S.chargeEntropyCost n h θ) c =
      ∑ g, moveEta n (augmentedPartition (S.oldChargeState h g))
        (S.quantumChargeMove g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)) θ :=
  S.chargeMoveCost_chargeEntropyCost n h θ c

-- Both pure-state identities retain the actual remaining middle complement.
example (n : V → ℕ) (π : PYF V) (hπ : π.IsPartition) (x : Finset V)
    (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toP x) θ =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ π.P) -
        FiniteProduct.entropy (fun v => Fin (n v)) θ π.P +
      FiniteProduct.entropy (fun v => Fin (n v)) θ π.Y -
        FiniteProduct.entropy (fun v => Fin (n v)) θ (π.Y \ x) :=
  moveEta_toP_eq_entropy_difference n π hπ x hx θ

example (n : V → ℕ) (π : PYF V) (hπ : π.IsPartition) (x : Finset V)
    (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toF x) θ =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ π.F) -
        FiniteProduct.entropy (fun v => Fin (n v)) θ π.F +
      FiniteProduct.entropy (fun v => Fin (n v)) θ π.Y -
        FiniteProduct.entropy (fun v => Fin (n v)) θ (π.Y \ x) :=
  moveEta_toF_eq_entropy_difference n π hπ x hx θ

-- Zero bands contribute zero cost without imposing positive dimensions or a unit vector.
example (S : CollarScan V I) (hK : S.K = 0) (n : V ⊕ Bool → ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (c : ChargeChoices S.K S.M)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    S.chargeMoveCost h (S.chargeEntropyCost n h θ) c = 0 := by
  unfold CollarScan.chargeMoveCost
  apply Finset.sum_eq_zero
  intro g _
  have hg := g.isLt
  omega

-- Equal anchors remain two labelled summands, rather than one deduplicated support.
example (S : CollarScan V (Fin 2)) (hanchor : S.anchor 1 = S.anchor 0)
    (n : V ⊕ Bool → ℕ) {k : ℕ} (L : ℕ) (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    S.designatedSplitIncidenceCost L h (S.chargeEntropyCost n h θ) =
      2 * ∑ g, ∑ side : Bool, if (side, 0) ∈ S.designatedSplitIncidences L h g then
        S.chargeEntropyCost n h θ g side
          (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor 0) ∩
            middle (S.oldChargeState h g)) else 0 := by
  classical
  simp only [CollarScan.designatedSplitIncidenceCost, CollarScan.designatedSplitIncidences,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two, hanchor,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro side _
  ring

-- Admission uses exact recursively retained weights rather than a positivity certificate.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    (S.actualChargeData hm hM k).IsAdmissible :=
  S.actualChargeData_isAdmissible hm hM k

end TNLeanTest.ActualChargeEntropy
