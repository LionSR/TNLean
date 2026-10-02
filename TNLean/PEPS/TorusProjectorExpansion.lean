/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusGramExpansion
import TNLean.PEPS.GInjectiveTorusProjector

/-!
# Expanding the actual torus projector contraction

The identity site map exposes its four virtual coordinates as physical coordinates.
Its torus contraction is therefore the product of the entries of the bond operators.
Expanding the averaging projector at each site replaces these operators by their
vertex-dependent changes of basis and sums the group labels at the vertices.

This is the finite-coordinate expansion needed for the local-inverse argument of
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 5.9,
`Papers/1001.3807/paper_v3.tex`, lines 1582–1621. The expansion itself does not
assume semi-regularity or a contracted-region Gram identity.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} {width height : ℕ} [NeZero width] [NeZero height]

/-- Reorder all bond-end coordinates into the four coordinates read at each site.
This is a bijection even when a torus circumference is one. -/
def torusBondSiteLabelsEquiv :
    (TorusVertex width height → V × V × V × V) ≃
      (TorusVertex width height → V × V × V × V) where
  toFun := torusBondSiteLabels
  invFun σ v := ((σ v).2.1, (σ (v.1 + 1, v.2)).2.2.2,
    (σ (v.1, v.2 + 1)).2.2.1, (σ v).1)
  left_inv β := by
    funext v
    simp only [torusBondSiteLabels, add_sub_cancel_right]
  right_inv σ := by
    funext v
    simp only [torusBondSiteLabels, sub_add_cancel]

variable [Fintype V] [DecidableEq V]

/-- The identity site's actual torus coefficient is the product of its bond entries.
Source: SCP10, the projector contraction in Theorem 5.9, lines 1582–1621. -/
theorem torusBondNetwork_single (σ : TorusVertex width height → V × V × V × V)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v => Pi.single (σ v) 1) Oh Ov =
      ∏ v, Oh v (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
        Ov v (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 := by
  classical
  change (∑ β : TorusVertex width height → V × V × V × V,
    (∏ v, Oh v (β v).2.1 (β v).1 * Ov v (β v).2.2.2 (β v).2.2.1) *
      ∏ v, Pi.single (M := fun _ : V × V × V × V => ℂ) (σ v) 1
        (torusBondSiteLabels β v)) = _
  rw [← (torusBondSiteLabelsEquiv (V := V) (width := width) (height := height)).symm.sum_comp
    (fun (β : TorusVertex width height → V × V × V × V) =>
      (∏ v, Oh v (β v).2.1 (β v).1 * Ov v (β v).2.2.2 (β v).2.2.1) *
      ∏ v, Pi.single (M := fun _ : V × V × V × V => ℂ) (σ v) 1 (torusBondSiteLabels β v))]
  simp only [torusBondSiteLabelsEquiv, Equiv.coe_fn_symm_mk, torusBondSiteLabels,
    sub_add_cancel, Prod.eta, Pi.single_apply, Fintype.prod_boole, ← funext_iff]
  simp

omit [DecidableEq V] in
/-- Expanding one finite sum at each site sums over all vertex labels.
Source: SCP10, the averaging-projector contraction in Theorem 5.9, lines 1582–1621. -/
theorem torusBondNetwork_sum {I : Type*} [Fintype I]
    (A : I → TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c => ∑ i, A i v c) Oh Ov =
      ∑ q : TorusVertex width height → I, torusBondNetwork (fun v => A (q v) v) Oh Ov := by
  simp_rw [torusBondNetwork, Fintype.prod_sum, Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq V] in
/-- Scaling each local site scales the full contraction by the product of the scalars.
Source: SCP10, the averaging-projector contraction in Theorem 5.9, lines 1582–1621. -/
theorem torusBondNetwork_mul (c : TorusVertex width height → ℂ)
    (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v x => c v * A v x) Oh Ov =
      (∏ v, c v) * torusBondNetwork A Oh Ov := by
  simp only [torusBondNetwork, Finset.prod_mul_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- A basis row absorbs the four-leg operator by taking that operator's row. -/
theorem torusDress_single (U : G →* Matrix V V ℂ) (x : G)
    (s : V × V × V × V) :
    torusDress (U x) (U x⁻¹) (Pi.single s 1) = torusLegMatrix U x s := by
  ext c
  simp [torusDress, Matrix.vecMul, torusLegMatrix]

/-- Expanding the actual averaging-site contraction gives one group label per vertex.
Source: SCP10, the projector contraction in Theorem 5.9, lines 1582–1621. -/
theorem torusBondNetwork_averagingSite (U : G →* Matrix V V ℂ)
    (σ : TorusVertex width height → V × V × V × V)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
        ∑ q : TorusVertex width height → G, ∏ v,
          (U (q (v.1 + 1, v.2)) * Oh v * U ((q v)⁻¹))
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (U (q v) * Ov v * U ((q (v.1, v.2 + 1))⁻¹))
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 := by
  simp only [averagingSite_apply, Prod.eta]
  rw [torusBondNetwork_mul, torusBondNetwork_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  simpa only [torusDress_single] using
    (torusBondNetwork_gauge (fun v => Pi.single (σ v) 1) Oh Ov
      (fun v => U (q v)) (fun v => U ((q v)⁻¹))).symm.trans
      (torusBondNetwork_single σ
        (fun v => U (q (v.1 + 1, v.2)) * Oh v * U ((q v)⁻¹))
        (fun v => U (q v) * Ov v * U ((q (v.1, v.2 + 1))⁻¹)))

end TNLean.PEPS
