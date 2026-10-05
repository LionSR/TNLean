/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusThetaBondState
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Regrouping the original torus physical legs by bonds

The four physical coordinates at each site can instead be grouped into the
physical endpoint pair on each horizontal or vertical bond. The first endpoint
is always the head, hence the row index of the bond matrix; the second is its
tail, hence the column index. Horizontal bonds point right and vertical bonds
point down. The existing torus bond-to-site coordinate equivalence supplies
this regrouping. Its induced coordinate permutation is a linear isometry.

The actual averaging-site and fourth-root-weighted torus contractions therefore
become coherent sums of bond vectors in these regrouped coordinates. No
coefficient equality or physical isometry is supplied as a hypothesis.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
local source lines 2977–3019. The coordinate identities hold for all positive
torus periods, including one.

**Local fix (group-average normalization):** The displayed source tensors sum
over the group. The averaging sites here divide that sum by |G|, so the actual
state carries |G|⁻ᴺ. This convention is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} {width height : ℕ}
local notation "X" => TorusVertex width height

private def bondEndPairEquiv : (V × V × V × V) ≃ (Bool → V × V) where
  toFun c b := if b then (c.2.2.2, c.2.2.1) else (c.2.1, c.1)
  invFun f := ((f false).2, (f false).1, (f true).2, (f true).1)
  left_inv c := by rcases c with ⟨a, b, c, d⟩; rfl
  right_inv f := by funext b; cases b <;> rfl

/-- Group the actual four physical legs by oriented bonds. `false` denotes
horizontal bonds and `true` vertical bonds; each pair is ordered head, tail.
Source: SCP10, Section 7, lines 2977–3019. -/
def torusSiteBondEndpointEquiv :
    (X → V × V × V × V) ≃ ((X × Bool) → V × V) :=
  torusBondSiteLabelsEquiv.symm.trans
    ((Equiv.piCongrRight fun _ => bondEndPairEquiv).trans (Equiv.curry X Bool (V × V)).symm)

/-- A horizontal physical bond reads the left leg at its head and the right
leg at its tail. Source: SCP10, Section 7, lines 2977–3007. -/
@[simp] theorem torusSiteBondEndpointEquiv_apply_horizontal
    (σ : X → V × V × V × V) (v : X) :
    torusSiteBondEndpointEquiv σ (v, false) =
      ((σ (v.1 + 1, v.2)).2.2.2, (σ v).2.1) := rfl

/-- A downward physical bond reads the top leg at its head and the bottom
leg at its tail. Source: SCP10, Section 7, lines 2977–3007. -/
@[simp] theorem torusSiteBondEndpointEquiv_apply_vertical
    (σ : X → V × V × V × V) (v : X) :
    torusSiteBondEndpointEquiv σ (v, true) =
      ((σ v).1, (σ (v.1, v.2 + 1)).2.2.1) := rfl

/-- Recover every original site leg from its actual incident bond endpoint.
Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem torusSiteBondEndpointEquiv_symm_apply
    (β : (X × Bool) → V × V) (v : X) :
    torusSiteBondEndpointEquiv.symm β v =
      ((β (v, true)).1, (β (v, false)).2,
        (β ((v.1, v.2 - 1), true)).2, (β ((v.1 - 1, v.2), false)).1) := rfl

/-- The coefficient-space linear equivalence induced by regrouping original
physical legs into bond endpoint pairs. Source: SCP10, Section 7, lines 2977–3019. -/
def torusBondRegrouping : ((X → V × V × V × V) → ℂ) ≃ₗ[ℂ]
    (((X × Bool) → V × V) → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) torusSiteBondEndpointEquiv

/-- The regrouped coefficient is the original coefficient at the recovered
site configuration. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem torusBondRegrouping_apply (ψ : (X → V × V × V × V) → ℂ)
    (β : (X × Bool) → V × V) :
    torusBondRegrouping ψ β = ψ (torusSiteBondEndpointEquiv.symm β) := rfl

variable [NeZero width] [NeZero height]

/-- The product over the actual horizontal and vertical bond positions is
exactly the product of the two bond factors at each vertex. Source: SCP10,
Section 7, lines 2977–3019. -/
theorem torusBond_product (F : X × Bool → ℂ) :
    (∏ v, F (v, false) * F (v, true)) = ∏ e, F e := by
  symm
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  apply Finset.prod_congr rfl
  intro v _
  exact mul_comm _ _

variable [Fintype V]

/-- Regrouping is a Hilbert-space isometry, since it is a permutation of the
actual physical basis configurations. Source: SCP10, Section 7, lines 2977–3019. -/
noncomputable def torusBondRegroupingIsometry :
    EuclideanSpace ℂ (X → V × V × V × V) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((X × Bool) → V × V) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ torusSiteBondEndpointEquiv

/-- The Hilbert-space isometry is the same literal physical coefficient
reindexing. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem torusBondRegroupingIsometry_apply
    (ψ : EuclideanSpace ℂ (X → V × V × V × V)) (β : (X × Bool) → V × V) :
    torusBondRegroupingIsometry ψ β = ψ (torusSiteBondEndpointEquiv.symm β) := rfl

/-- Every physical overlap is preserved by the site-to-bond regrouping.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondRegrouping_dotProduct (ψ φ : (X → V × V × V × V) → ℂ) :
    star (torusBondRegrouping ψ) ⬝ᵥ torusBondRegrouping φ = star ψ ⬝ᵥ φ :=
  torusSiteBondEndpointEquiv.symm.sum_comp (fun σ => star (ψ σ) * φ σ)

variable [DecidableEq V] {G : Type*} [Group G] [Fintype G]

/-- Regroup the actual normalized averaging-site torus contraction into
its horizontal and vertical physical bond vectors. Source: SCP10, Section 7,
lines 2977–3019; inserted bond matrices are also permitted. -/
theorem torusBondRegrouping_averagingSite (U : G →* Matrix V V ℂ)
    (Oh Ov : X → Matrix V V ℂ) (β : (X × Bool) → V × V) :
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov) β =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X *
        ∑ q : X → G, ∏ v,
          (U (q (v.1 + 1, v.2)) * Oh v * U ((q v)⁻¹))
            (β (v, false)).1 (β (v, false)).2 *
          (U (q v) * Ov v * U ((q (v.1, v.2 + 1))⁻¹))
            (β (v, true)).1 (β (v, true)).2 := by
  rw [torusBondRegrouping_apply, torusBondNetwork_averagingSite]
  simp only [torusSiteBondEndpointEquiv_symm_apply, add_sub_cancel_right]

/-- Regroup the actual torus contraction of sites dressed by a commuting
virtual weight. Two endpoint weights become W² on each physical bond.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondRegrouping_dressedAveragingSite (U : G →* Matrix V V ℂ)
    (W : Matrix V V ℂ) (hc : ∀ g, Commute W (U g))
    (β : (X × Bool) → V × V) :
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v => torusDress W W
        (fun c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))) 1 1) β =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X *
        ∑ q : X → G, ∏ v,
          (W ^ 2 * U (q (v.1 + 1, v.2) * (q v)⁻¹))
            (β (v, false)).1 (β (v, false)).2 *
          (W ^ 2 * U (q v * (q (v.1, v.2 + 1))⁻¹))
            (β (v, true)).1 (β (v, true)).2 := by
  rw [torusBondRegrouping_apply, torusBondNetwork_dressedAveragingSite U W hc]
  simp only [torusSiteBondEndpointEquiv_symm_apply, add_sub_cancel_right]

/-- Regroup the actual fourth-root-weighted torus state into its physical
bond vectors, whose weights are Θ². Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondRegrouping_thetaWeightedAveragingSite (U : G →* Matrix V V ℂ)
    (β : (X × Bool) → V × V) :
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v c => thetaWeightedAveragingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) 1 1) β =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X *
        ∑ q : X → G, ∏ v,
          (thetaMatrix U ^ 2 * U (q (v.1 + 1, v.2) * (q v)⁻¹))
            (β (v, false)).1 (β (v, false)).2 *
          (thetaMatrix U ^ 2 * U (q v * (q (v.1, v.2 + 1))⁻¹))
            (β (v, true)).1 (β (v, true)).2 := by
  rw [torusBondRegrouping_apply, torusBondNetwork_thetaWeightedAveragingSite]
  simp only [torusSiteBondEndpointEquiv_symm_apply, add_sub_cancel_right]

end TNLean.PEPS
