/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusProjectorExpansion
import TNLean.Algebra.RepresentationTheta
import TNLean.Algebra.MonoidHomCommutingWeight

/-!
# Moving fourth-root site weights onto the actual torus bonds

The canonical averaging site is weighted on each virtual leg by Θ. In its
actual torus contraction, the two endpoint weights combine to Θ² on every
bond. Expanding the site averages then gives a coherent sum over vertex group
labels of products of the weighted relative representation matrices.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2974–3007. For the multiplicity-one
representation, Θ² has the square-root dimension weights displayed there.
The statement uses the existing torus tensor and contraction. It proves the
site-to-bond coefficient identity; restoration of multiplicity spaces is separate.
The algebraic identity also permits arbitrary virtual representations and
positive torus circumferences, including one.

**Local fix (group-average normalization):** The displayed source tensor H
uses a sum over G. The averaging site used here divides that sum by |G|,
so its torus contraction carries |G|⁻ᴺ, where N is the number of vertices.
The fourth-root normalization is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Dressing the native averaging site by a commuting weight combines the two
endpoint weights on each bond. Source: SCP10, Section 7, lines 2977–3007. -/
theorem torusBondNetwork_dressedAveragingSite (U : G →* Matrix V V ℂ) (W : Matrix V V ℂ)
    (hc : ∀ g, Commute W (U g))
    (σ : TorusVertex width height → V × V × V × V) :
    torusBondNetwork (fun v => torusDress W W
      (fun c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))) 1 1 =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
        ∑ q : TorusVertex width height → G, ∏ v,
          (W ^ 2 * U (q (v.1 + 1, v.2) * (q v)⁻¹))
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (W ^ 2 * U (q v * (q (v.1, v.2 + 1))⁻¹))
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 := by
  have hnetwork := torusBondNetwork_gauge
    (fun v c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
    1 1 (fun _ => W) (fun _ => W)
  simp only [Pi.one_apply, Matrix.mul_one, ← pow_two] at hnetwork
  rw [← hnetwork, torusBondNetwork_averagingSite]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.prod_congr rfl
  intro v _
  rw [U.mul_commuting_pow_mul W hc, U.mul_commuting_pow_mul W hc]

/-- The matrix of the fourth-root weight operator in the native virtual basis.
Source: SCP10, Section 7, the displayed Θ, lines 2962–2977. -/
noncomputable def thetaMatrix (U : G →* Matrix V V ℂ) : Matrix V V ℂ :=
  LinearMap.toMatrix' (Representation.thetaOperator
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))

/-- The canonical averaging site with Θ on each of its four virtual legs.
Source: SCP10, equation `eq:ex:V-Theta-double-def`, lines 2974–2977,
with a normalized group average. -/
noncomputable def thetaWeightedAveragingSite (U : G →* Matrix V V ℂ)
    (t r b l : V) (s : V × V × V × V) : ℂ :=
  torusDress (thetaMatrix U) (thetaMatrix U)
    (fun c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 s) (t, r, b, l)

/-- The actual weighted-site torus coefficient is a coherent product of bonds
weighted by Θ². Source: SCP10, Section 7, lines 2977–3007. -/
theorem torusBondNetwork_thetaWeightedAveragingSite (U : G →* Matrix V V ℂ)
    (σ : TorusVertex width height → V × V × V × V) :
    torusBondNetwork (fun v c =>
      thetaWeightedAveragingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) 1 1 =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
        ∑ q : TorusVertex width height → G, ∏ v,
          (thetaMatrix U ^ 2 * U (q (v.1 + 1, v.2) * (q v)⁻¹))
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (thetaMatrix U ^ 2 * U (q v * (q (v.1, v.2 + 1))⁻¹))
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 := by
  apply torusBondNetwork_dressedAveragingSite
  intro g
  let E : Matrix V V ℂ ≃ₐ[ℂ] Module.End ℂ (V → ℂ) := Matrix.toLinAlgEquiv'
  have hc := (Representation.thetaOperator_commute (E.toMonoidHom.comp U) g).map E.symm
  change Commute (E.symm (Representation.thetaOperator (E.toMonoidHom.comp U)))
    (E.symm (E (U g))) at hc
  rw [E.symm_apply_apply] at hc
  change Commute (thetaMatrix U) (U g) at hc
  exact hc

end TNLean.PEPS
