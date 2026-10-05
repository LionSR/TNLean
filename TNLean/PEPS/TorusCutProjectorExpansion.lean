/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutLocalInverse

/-!
# Expanding the canonical cut tensor with its original boundary

After applying the local G-injective inverses, expand one averaging projector
at each of the four sites. This gives four independent group labels and keeps
the original correlated boundary tensor, including all its coefficients.
The formula also applies to larger tori and to site-dependent virtual actions.

Source: SCP10, Theorem 5.5, `eq:2d:closure-inv` and `eq:2d:close-in-in`.
The further contraction and comparison of different cut boundaries is a
separate, presently unproved step.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V Phys : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Expand local finite sums before the contraction while retaining one
arbitrary correlated boundary tensor. -/
theorem torusCutCoeff_sum {I : Type*} [Fintype I]
    (a : I → TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ)
    (σ : TorusVertex width height → Phys) :
    torusCutCoeff (fun v t r b l s ↦ ∑ i, a i v t r b l s) c r M σ =
      ∑ q : TorusVertex width height → I,
        torusCutCoeff (fun v ↦ a (q v) v) c r M σ := by
  simp_rw [torusCutCoeff, Fintype.prod_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- Local scalar normalizations multiply to the global normalization. -/
theorem torusCutCoeff_mul
    (z : TorusVertex width height → ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ)
    (σ : TorusVertex width height → Phys) :
    torusCutCoeff (fun v t r b l s ↦ z v * a v t r b l s) c r M σ =
      (∏ v, z v) * torusCutCoeff a c r M σ := by
  simp only [torusCutCoeff, Finset.prod_mul_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The local canonical tensor is the normalized sum of the actual local
representation matrices, allowing a different action at each site. -/
theorem representationAveragingSite_apply
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ))
    (t r b l : V) (s : V × V × V × V) :
    representationAveragingSite ρ t r b l s =
      (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, LinearMap.toMatrix' (ρ g) s (t, r, b, l) := by
  rw [representationAveragingSite, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, invOf_eq_inv, smul_eq_mul,
    LinearMap.toMatrix'_apply]

/-- The canonical cut contraction expands into independent vertex group
labels, keeping the same arbitrary boundary tensor throughout. At size two
there are exactly four labels and the normalization is `|G|⁻⁴`. -/
theorem torusCutCoeff_representationAveragingSite
    (ρ : TorusVertex width height → Representation ℂ G ((V × V × V × V) → ℂ))
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ)
    (σ : TorusVertex width height → V × V × V × V) :
    torusCutCoeff (fun v ↦ representationAveragingSite (ρ v)) c r M σ =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
        ∑ q : TorusVertex width height → G,
          torusCutCoeff
            (fun v t r b l s ↦ LinearMap.toMatrix' (ρ v (q v)) s (t, r, b, l)) c r M σ := by
  have h : (fun v ↦ representationAveragingSite (ρ v)) =
      (fun v t r b l (s : V × V × V × V) ↦ (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, LinearMap.toMatrix' (ρ v g) s (t, r, b, l)) := by
    funext v t r b l s
    exact representationAveragingSite_apply (ρ v) t r b l s
  rw [h, torusCutCoeff_mul, torusCutCoeff_sum]
  simp only [Finset.prod_const, Finset.card_univ]

end TNLean.PEPS
