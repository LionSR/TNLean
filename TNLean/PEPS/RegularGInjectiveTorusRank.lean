/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGInjectiveTorus
import TNLean.PEPS.PhysicalProductCut

/-!
# Schmidt-rank transport for regular G-injective torus closures

A local G-injective left inverse sends the actual torus closure vectors to those of
the regular averaging-projector tensor. The original site map recovers these vectors.
The corresponding tensor products of physical maps act on every finite linear combination
and factor across any vertex partition. The two coefficient matrices therefore have the
same rank, even when the superposition vanishes.

This proves the local-deformation step in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Corollary 6.10, source lines 2074–2090.

**Scope restriction (regular native closures):** this is a comparison with the canonical
regular projector tensor, not the numerical boundary-rank formula for an arbitrary disk.
The latter geometric step remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. Noncommuting closure pairs and
size-one torus dimensions are permitted as algebraic extensions; no ground-space assertion
is made.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Finite Phys] {S : Type*} [Fintype S]

/-- Every finite superposition of actual regular G-injective torus closures has the same
Schmidt rank across any vertex partition as the corresponding canonical projector
superposition. No nonvanishing, commutativity, or isometry hypothesis is needed.
Source: SCP10, the local-deformation argument of Corollary 6.10, lines 2074–2090. -/
theorem IsGInjective.rank_physicalCutMatrix_torusGClosure_sum
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (χ : TorusVertex width height → Prop) [DecidablePred χ]
    (p : S → G × G) (w : S → ℂ) :
    let _ := Fintype.ofFinite Phys
    (physicalCutMatrix χ
      (∑ s, w s • torusGClosure (leftRegularMatrix G) a (p s).1 (p s).2)).rank =
    (physicalCutMatrix χ
      (∑ s, w s • torusGClosure (leftRegularMatrix G)
        (averagingSite (leftRegularMatrix G)) (p s).1 (p s).2)).rank := by
  let _ := Fintype.ofFinite Phys
  obtain ⟨F, hF⟩ := ha.exists_torusGClosure_averagingSite
    (width := width) (height := height)
  have hforward : physicalProductMap (TorusVertex width height) F
      (∑ s, w s • torusGClosure (leftRegularMatrix G) a (p s).1 (p s).2) =
      ∑ s, w s • torusGClosure (leftRegularMatrix G)
        (averagingSite (leftRegularMatrix G)) (p s).1 (p s).2 := by
    change torusPhysicalMap F _ = _
    simp only [map_sum, map_smul, hF]
  have hreverse : physicalProductMap (TorusVertex width height)
      (LinearMap.toMatrix' (siteMap a))
      (∑ s, w s • torusGClosure (leftRegularMatrix G)
        (averagingSite (leftRegularMatrix G)) (p s).1 (p s).2) =
      ∑ s, w s • torusGClosure (leftRegularMatrix G) a (p s).1 (p s).2 := by
    change torusPhysicalMap (LinearMap.toMatrix' (siteMap a)) _ = _
    simp only [map_sum, map_smul,
      torusPhysicalMap_averagingSite (leftRegularMatrix G) a ha.invariant]
  exact (rank_physicalCutMatrix_eq_of_physicalProductMaps χ F
    (LinearMap.toMatrix' (siteMap a)) _ _ hforward hreverse).symm

end TNLean.PEPS
