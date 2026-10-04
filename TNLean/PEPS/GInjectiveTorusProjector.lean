/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusSite
import TNLean.PEPS.TorusPhysicalMap

/-!
# Canonical averaging sites and G-injective physical maps

For any finite-dimensional virtual representation, the group average gives a canonical
G-injective four-leg site. A local G-injective left inverse sends actual closure vectors
to the closures of this projector site. Conversely, the original invariant site map
recovers the original closures from the canonical ones. These identities require no
unitarity or local isometry and make no assertion that the physical maps are globally
inverse or surjective.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1,
lines 1278–1296, and the local-left-inverse argument in Theorem 5.9, lines 1582–1621.
The identities also allow noncommuting pairs and size-one torus dimensions as algebraic
extensions; no parent-Hamiltonian or ground-space assertion is made.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix
open Matrix LinearMap Representation GroupAlgebra

namespace TNLean.PEPS

section Coefficients

variable {V Phys Out : Type*} [Fintype V]

/-- The four-leg coefficients are uniquely determined by their site map. -/
theorem siteMap_injective :
    Function.Injective (siteMap (V := V) (Phys := Phys)) := by
  classical
  intro a b h
  have hmat := congrArg LinearMap.toMatrix' h
  simp only [toMatrix_siteMap_regular] at hmat
  funext t r d l s
  exact congrFun (congrFun hmat s) (t, r, d, l)

variable [Fintype Phys]

/-- Applying a physical matrix to the coefficients is equivalent to composing site maps.
Source: SCP10, local left-inverse operation in Theorem 5.9, lines 1582–1621. -/
theorem physicalMapSite_eq_iff_siteMap_comp (F : Matrix Out Phys ℂ)
    (a : V → V → V → V → Phys → ℂ) (b : V → V → V → V → Out → ℂ) :
    physicalMapSite F a = b ↔ Matrix.mulVecLin F ∘ₗ siteMap a = siteMap b := by
  rw [← siteMap_physicalMapSite]
  exact siteMap_injective.eq_iff.symm

end Coefficients

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The invariant projector of the four virtual legs, expressed as a site whose physical
basis is the four-leg virtual basis. Source: SCP10, Definition 5.1, lines 1278–1296. -/
noncomputable def averagingSite (U : G →* Matrix V V ℂ)
    (t r b l : V) (s : V × V × V × V) : ℂ :=
  LinearMap.toMatrix' (torusLegRep U).averageMap s (t, r, b, l)

/-- The canonical site's coefficient map is exactly the existing averaging map. -/
theorem siteMap_averagingSite (U : G →* Matrix V V ℂ) :
    siteMap (averagingSite U) = (torusLegRep U).averageMap := by
  apply LinearMap.toMatrix'.injective
  rw [toMatrix_siteMap_regular]
  rfl

/-- The canonical site's coefficients are the average of the four-leg representation
matrices. Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem averagingSite_apply (U : G →* Matrix V V ℂ)
    (t r b l : V) (s : V × V × V × V) :
    averagingSite U t r b l s =
      (Fintype.card G : ℂ)⁻¹ * ∑ q : G, torusLegMatrix U q s (t, r, b, l) := by
  rw [averagingSite, LinearMap.toMatrix'_apply, Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, torusLegRep_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, invOf_eq_inv, smul_eq_mul]

/-- The canonical averaging site is invariant under the existing four-leg representation.
Source: SCP10, Definition 5.1(i), lines 1278–1296. -/
theorem averagingSite_invariant (U : G →* Matrix V V ℂ) (g : G) :
    siteMap (averagingSite U) ∘ₗ torusLegRep U g = siteMap (averagingSite U) := by
  rw [siteMap_averagingSite]
  change (torusLegRep U).averageMap * torusLegRep U g = (torusLegRep U).averageMap
  rw [Representation.averageMap, ← asAlgebraHom_single_one, ← map_mul, mul_average_right]

/-- The averaging site is G-injective on its invariant virtual subspace, without a
unitarity hypothesis. Source: SCP10, Definition 5.1(ii), lines 1278–1296. -/
theorem isGInjective_averagingSite (U : G →* Matrix V V ℂ) :
    IsGInjective (torusLegRep U) (siteMap (averagingSite U)) := by
  refine ⟨averagingSite_invariant U, ?_⟩
  intro x hx hzero
  rw [siteMap_averagingSite, (torusLegRep U).averageMap_id x hx] at hzero
  exact hzero

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Fintype Phys]

/-- A local G-injective left inverse sends every actual closure to the corresponding
canonical projector closure. Source: SCP10, Theorem 5.9, lines 1582–1621. -/
theorem IsGInjective.exists_torusGClosure_averagingSite
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a)) :
    ∃ F : Matrix (V × V × V × V) Phys ℂ, ∀ g h : G,
      torusPhysicalMap (width := width) (height := height) F (torusGClosure U a g h) =
        torusGClosure U (averagingSite U) g h := by
  classical
  obtain ⟨_, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).mp ha
  let F := LinearMap.toMatrix' L
  have hcoeff : physicalMapSite F a = averagingSite U := by
    apply (physicalMapSite_eq_iff_siteMap_comp F a (averagingSite U)).mpr
    rw [siteMap_averagingSite]
    change Matrix.toLin' (LinearMap.toMatrix' L) ∘ₗ siteMap a = (torusLegRep U).averageMap
    rw [Matrix.toLin'_toMatrix', hL]
  refine ⟨F, fun g h => ?_⟩
  rw [torusPhysicalMap_torusGClosure, hcoeff]

omit [Fintype Phys] in
/-- The original invariant site map recovers its actual closures from the canonical
projector closures. No global inverse is asserted. Source: SCP10, Theorem 5.9,
lines 1582–1621, and the local deformation in Corollary 6.10, lines 2074–2090. -/
theorem torusPhysicalMap_averagingSite (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (hinv : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a) (g h : G) :
    torusPhysicalMap (width := width) (height := height) (LinearMap.toMatrix' (siteMap a))
        (torusGClosure U (averagingSite U) g h) = torusGClosure U a g h := by
  have hTP : siteMap a ∘ₗ (torusLegRep U).averageMap = siteMap a :=
    LinearMap.ext (apply_averageMap_of_forall_comp_eq hinv)
  have hcoeff : physicalMapSite (LinearMap.toMatrix' (siteMap a)) (averagingSite U) = a := by
    apply (physicalMapSite_eq_iff_siteMap_comp _ _ _).mpr
    rw [siteMap_averagingSite]
    change Matrix.toLin' (LinearMap.toMatrix' (siteMap a)) ∘ₗ _ = siteMap a
    rw [Matrix.toLin'_toMatrix']
    exact hTP
  rw [torusPhysicalMap_torusGClosure, hcoeff]

end TNLean.PEPS
