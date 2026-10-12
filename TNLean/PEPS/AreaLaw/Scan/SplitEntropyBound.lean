/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TransportRound
import TNLean.PEPS.AreaLaw.Scan.RegionalMoveEntropy
import QICLean.Entropy.ConditionalTwoFamilies

/-!
# The physical-support upper bound for split entropy

The split entropy of one compatible leaf is at most twice the logarithmic
size of its designated support. The proof bounds the entropy only of the
moved subsystem, which is contained in that support. Auxiliary factors are
not bounded. For the actual scanner, the support cap is derived separately
from the physical geometry whenever a split leaf exists.

Source: the area-law manuscript, `08-scanner.tex`, lines 431–440 and 503–506,
at `openai/math@adc7f124`. Independently written from the entropy argument.
-/

open scoped BigOperators
open TensorPower Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]
  (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The entropy of a subsystem is bounded using any containing support. -/
private theorem entropy_le_logDim_of_subset (θ : EuclideanSpace ℂ (SiteConfig n))
    (hθ : ‖θ‖ = 1) {R B : Finset V} (hRB : R ⊆ B) :
    FiniteProduct.entropy (fun v => Fin (n v)) θ R ≤ logDim n B := by
  have hρ := FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v)) θ R
  have htr := FiniteProduct.trace_reducedPure (fun v => Fin (n v)) θ hθ R
  have hcard : Fintype.card (FiniteProduct.Configuration (fun v => Fin (n v)) R) ≤
      ∏ v ∈ B, n v := by
    calc
      _ = ∏ v ∈ R, n v := by
        simp only [FiniteProduct.Configuration, Fintype.card_pi, Fintype.card_fin,
          Finset.prod_coe_sort]
      _ ≤ ∏ v ∈ B, n v := Finset.prod_le_prod_of_subset_of_one_le hRB
        (fun v _ _ => Nat.one_le_iff_ne_zero.mpr (NeZero.ne (n v)))
  have hlog := Real.log_le_log
    (Nat.cast_pos.mpr (hρ.rank_pos_of_trace_one htr))
    (Nat.cast_le.mpr ((Matrix.rank_le_card_width
      (FiniteProduct.reducedPure (fun v => Fin (n v)) θ R)).trans hcard))
  have hprod : 0 < ∏ v ∈ B, (n v : ℝ) := Finset.prod_pos fun v _ =>
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (n v)))
  simp only [Nat.cast_prod] at hlog
  calc
    FiniteProduct.entropy (fun v => Fin (n v)) θ R ≤
        Real.log (FiniteProduct.reducedPure (fun v => Fin (n v)) θ R).rank :=
      vonNeumannEntropy_le_log_rank hρ htr
    _ ≤ Real.log (∏ v ∈ B, (n v : ℝ)) := hlog
    _ ≤ logDim n B := by
      rw [logDim, Real.log_mul (Real.exp_pos 1).ne' hprod.ne', Real.log_exp]
      linarith

/-- Both choices of the receiving side have nonnegative split entropy. -/
theorem splitBandEta_nonneg (π : PYF V) (hπ : π.IsPartition) (B : Finset V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : 0 ≤ splitBandEta n π B θ := by
  classical
  unfold splitBandEta
  split_ifs
  · exact moveEta_nonneg n π hπ (.toP (B ∩ π.Y)) Finset.inter_subset_right θ
  · exact moveEta_nonneg n π hπ (.toF (B ∩ π.Y)) Finset.inter_subset_right θ

/-- The cost of the exceptional band is bounded by its physical support, even
when the other tensor factors have unrestricted dimensions. -/
theorem splitBandEta_le_two_mul_logDim (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (θ : EuclideanSpace ℂ (SiteConfig n)) (hθ : ‖θ‖ = 1) :
    splitBandEta n π B θ ≤ 2 * logDim n B := by
  classical
  have hYP : Disjoint (B ∩ π.Y) π.P := hπ.1.symm.mono_left Finset.inter_subset_right
  have hYF : Disjoint (B ∩ π.Y) π.F := hπ.2.2.1.mono_left Finset.inter_subset_right
  have hcost : splitBandEta n π B θ ≤
      2 * FiniteProduct.entropy (fun v => Fin (n v)) θ (B ∩ π.Y) := by
    unfold splitBandEta
    split_ifs
    · exact FiniteProduct.conditionalMutualInformation_le_two_entropy _ θ hθ
        (B ∩ π.Y) π.F π.P hYF hYP
    · exact FiniteProduct.conditionalMutualInformation_le_two_entropy _ θ hθ
        (B ∩ π.Y) π.P π.F hYP hYF
  exact hcost.trans (mul_le_mul_of_nonneg_left
    (entropy_le_logDim_of_subset n θ hθ Finset.inter_subset_left) (by norm_num))

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]
  (D : TransportData V K H C) {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι)

/-- Split entropy is nonnegative at every leaf of admissible transport data. -/
theorem splitEta_nonneg (hD : D.IsAdmissible) (i : ι) (j : Σ h, Option (C h))
    (θ : EuclideanSpace ℂ (SiteConfig n)) : 0 ≤ D.splitEta E i j θ := by
  classical
  unfold splitEta
  exact Finset.sum_nonneg fun g _ =>
    splitBandEta_nonneg n _ (D.isPartition_leafPart hD j g) _ θ

/-- A compatible leaf's entropy is bounded by twice the support cap. The cap
is needed only for supports having a split leaf; all other symbols vanish. -/
theorem splitEta_le_two_mul_of_logDim_le (hD : D.IsAdmissible)
    (hcompat : D.SupportCompatible E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ)
    (i : ι) (j : Σ h, Option (C h)) (θ : CoherentSphere (SiteConfig n)) :
    D.splitEta E i j θ.1 ≤ 2 * ℓ := by
  classical
  by_cases hj : j ∈ D.splitLeaves E i
  · obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hj).2
    rw [D.splitEta_eq_splitBandEta E hcompat hg]
    exact (splitBandEta_le_two_mul_logDim n _ (D.isPartition_leafPart hD j g)
      _ θ.1 θ.2).trans (mul_le_mul_of_nonneg_left (hsupp i ⟨j, hj⟩) (by norm_num))
  · have hzero : D.splitEta E i j θ.1 = 0 := by
      simp [splitEta, D.forall_contains_of_not_mem_splitLeaves E hj]
    rw [hzero]
    exact mul_nonneg (by norm_num) hℓ

/-- The actual split symbol restricted to the coherent sphere is measurable. -/
theorem measurable_splitEta_sphere (i : ι) (j : Σ h, Option (C h)) :
    Measurable (fun θ : CoherentSphere (SiteConfig n) => D.splitEta E i j θ.1) := by
  classical
  have hcont : Continuous (fun θ : SiteConfig n → ℂ =>
      D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ)) := by
    unfold splitEta
    exact continuous_finsetSum _ fun g _ => continuous_splitBandEta _ _
  exact (hcont.comp continuous_coherentSphere_coe).measurable

end TransportData
end TensorPower.ReplicaTransport
