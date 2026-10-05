/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoByTwoPhysicalBlocking
import TNLean.PEPS.RegularTorusSectors

/-!
# Nonvanishing of the original fine and coarse regular PEPS

For a homogeneous regular G-isometric tensor, the native identity-closure
state is nonzero. Four-coordinate basis permutations transfer the existing
closure-sector theorem to arbitrary finite physical alphabets. Consequently
both the actual fine state and the original-tensor coarse graph state have
nonzero norm and can be normalized, without a supplied nonvanishing assumption.

Source: SCP10, arXiv:1001.3807, Theorem 5.9 and Observation 6.6,
lines 1582–1621 and 1888–1909.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G P : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype P]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The homogeneous bond-indexed regular state is nonzero for every pair of
positive periods, with an arbitrary finite physical alphabet.
Source: SCP10, Theorem 5.9, the identity closure sector. -/
theorem IsGIsometric.torusBondNetwork_one_ne_zero
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    (fun σ : TorusVertex width height → P =>
      torusBondNetwork (fun v c => a ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1) ≠ 0 := by
  let b : G → G → G → G → P → ℂ := fun t r d l => a ![t, r, d, l]
  have hb : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap b) := by
    refine ha.of_coordinateEquiv (finFourArrowEquiv G).symm (Equiv.refl P) ?_ ?_
    · intro g x
      funext η
      simp only [Function.comp_apply, Equiv.symm_symm, regularLegRepresentation_apply,
        torusLegRep_leftRegularMatrix_apply, finFourArrowEquiv_smul]
    · intro x
      funext s
      change (∑ η : G × G × G × G, a ![η.1, η.2.1, η.2.2.1, η.2.2.2] s * x η) =
        ∑ η : Fin 4 → G, a η s * x (finFourArrowEquiv G η)
      rw [← (finFourArrowEquiv G).sum_comp]
      apply Finset.sum_congr rfl
      intro η _
      congr 2
      exact (finFourArrowEquiv G).symm_apply_apply η
  have hclosure : torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) b 1 1 = fun σ : TorusVertex width height → P =>
        torusBondNetwork (fun v c => a ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 := by
    funext σ
    simp only [torusGClosure, b]
    congr 1
    · funext v
      simp [torusHorizontalClosure]
    · funext v
      simp [torusVerticalClosure]
  rw [← hclosure]
  exact hb.torusGClosure_ne_zero 1 1

/-- The actual fine state of a homogeneous regular G-isometric tensor is
nonzero before any physical regrouping or disentangling.
Source: SCP10, Observation 6.6 and the identity sector of Theorem 5.9. -/
theorem IsGIsometric.twoByTwoFineState_ne_zero
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    twoByTwoFineState (width := width) (height := height) (fun _ => a) ≠ 0 :=
  ha.torusBondNetwork_one_ne_zero

variable [Fact (2 < width)] [Fact (2 < height)]

omit [DecidableEq G] in
/-- The original homogeneous tensor gives a nonzero actual coarse graph
state. Source: SCP10, the coarse original-tensor state in Observation 6.6. -/
theorem IsGIsometric.graphBondNetwork_torusIncidentFamily_ne_zero
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    graphBondNetwork (torusIncidentFamily (fun _ : TorusVertex width height => a)) ≠ 0 := by
  classical
  have h := ha.torusBondNetwork_one_ne_zero (width := width) (height := height)
  simpa only [← graphBondNetwork_torusIncidentFamily (fun _ : TorusVertex width height => a)]
    using h

end TNLean.PEPS
