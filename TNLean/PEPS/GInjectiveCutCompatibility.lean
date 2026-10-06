/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveCutRange

/-!
# Compatibility of virtual comparisons across a regular cut

Equality of two regular G-injective cut states determines physical ranges
on both sides. Left inverses of the second pair of open maps then produce
virtual comparison maps. They recover the first pair of open maps and
preserve the boundary pairing: the product of one comparison matrix and
the transpose of the other is the invariant-boundary projector.

This is a local consequence of the left inverses in Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Definition 5.1, and the regular cut in the
proof of Theorem 6.9, lines 1278–1296 and 2043–2076. It concerns an entire
boundary; factorization into individual bond maps requires further work.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G Phys Out : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype Phys] [Fintype Out]

noncomputable local instance instInvertibleCardCutCompatibility :
    Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Fintype Phys] [Fintype Out] in
/-- Equal regular cut coefficients yield equal physical ranges on the
complementary side as well. Source: SCP10, Definition 5.1 and the cut in
Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem range_right_eq_of_regularBoundaryCutMatrix_eq [Finite Phys] (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S S' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hS : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S)
    (hT' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T')
    (hS' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S')
    (hcut : regularBoundaryCutMatrix n T S = regularBoundaryCutMatrix n T' S') :
    S.range = S'.range := by
  let _ := Fintype.ofFinite Phys
  apply range_eq_of_regularBoundaryCutMatrix_eq n n hS hT hS' hT'
  simpa only [regularBoundaryCutMatrix, Matrix.transpose_mul,
    Matrix.transpose_transpose] using congrArg Matrix.transpose hcut

omit [Fintype Phys] [DecidableEq G] in
/-- A left inverse of a G-injective map recovers another invariant map
with the same physical range. Source: local consequence of SCP10,
Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_leftInverse_of_range_eq (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T')
    (hRange : T.range = T'.range)
    (L : (Phys → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ))
    (hL : L ∘ₗ T' = (regularBoundaryRepresentation (G := G) (n + 1)).averageMap) :
    T' ∘ₗ (L ∘ₗ T) = T := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hRange ▸ (show T x ∈ T.range from ⟨x, rfl⟩)
  change T' (L (T x)) = T x
  rw [← hy, show L (T' y) = _ from LinearMap.congr_fun hL y,
    apply_averageMap_of_forall_comp_eq hT'.invariant y, hy]

omit [Fintype Phys] [DecidableEq G] in
/-- A boundary comparison induced by a left inverse takes values in the
invariant boundary when the physical ranges agree. Source: local
consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem averageMap_comp_leftInverse_of_range_eq (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hRange : T.range = T'.range)
    (L : (Phys → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ))
    (hL : L ∘ₗ T' = (regularBoundaryRepresentation (G := G) (n + 1)).averageMap) :
    (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ (L ∘ₗ T) =
      L ∘ₗ T := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hRange ▸ (show T x ∈ T.range from ⟨x, rfl⟩)
  change (regularBoundaryRepresentation (G := G) (n + 1)).averageMap (L (T x)) = L (T x)
  rw [← hy, show L (T' y) = _ from LinearMap.congr_fun hL y]
  exact Representation.averageMap_id _ _ (Representation.averageMap_invariant _ _)

omit [Fintype Phys] [DecidableEq G] in
/-- A supported virtual comparison is uniquely specified by its physical
image. Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.supported_comparison_unique (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T')
    {F K : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ)}
    (hF : T' ∘ₗ F = T) (hK : T' ∘ₗ K = T)
    (hPF : (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ F = F)
    (hPK : (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ K = K) :
    F = K := by
  apply LinearMap.ext
  intro x
  have hmemF : F x ∈ (regularBoundaryRepresentation (G := G) (n + 1)).invariants := by
    rw [← LinearMap.congr_fun hPF x]
    exact Representation.averageMap_invariant _ _
  have hmemK : K x ∈ (regularBoundaryRepresentation (G := G) (n + 1)).invariants := by
    rw [← LinearMap.congr_fun hPK x]
    exact Representation.averageMap_invariant _ _
  have hz := hT'.injOn_invariants _ (Submodule.sub_mem _ hmemF hmemK)
    (show T' (F x - K x) = 0 by
      rw [map_sub, show T' (F x) = _ from LinearMap.congr_fun hF x,
        show T' (K x) = _ from LinearMap.congr_fun hK x, sub_self])
  exact sub_eq_zero.mp hz

omit [Fintype Phys] [DecidableEq G] in
/-- Equal physical ranges determine one supported virtual comparison.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.existsUnique_supportedComparison (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T')
    (hRange : T.range = T'.range) :
    ∃! F : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ),
      T' ∘ₗ F = T ∧
      (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ F = F := by
  obtain ⟨_, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).mp hT'
  have hRec := hT'.comp_leftInverse_of_range_eq n hRange L hL
  have hAvg := averageMap_comp_leftInverse_of_range_eq n hRange L hL
  refine ⟨L ∘ₗ T, ⟨hRec, hAvg⟩, ?_⟩
  intro F hF
  exact hT'.supported_comparison_unique n hF.1 hRec hF.2 hAvg

omit [Fintype Phys] [Fintype Out] in
/-- Comparisons induced by left inverses on the two sides of equal regular
cuts preserve their common invariant pairing. Source: local consequence
of SCP10, Definition 5.1 and the cut in Theorem 6.9,
lines 1278–1296 and 2043–2076. -/
theorem regularBoundaryComparison_pairing [Finite Phys] [Finite Out] (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S S' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (L : (Phys → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ))
    (K : (Out → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ))
    (hL : L ∘ₗ T' = (regularBoundaryRepresentation (G := G) (n + 1)).averageMap)
    (hK : K ∘ₗ S' = (regularBoundaryRepresentation (G := G) (n + 1)).averageMap)
    (hcut : regularBoundaryCutMatrix n T S = regularBoundaryCutMatrix n T' S') :
    LinearMap.toMatrix' (L ∘ₗ T) * (LinearMap.toMatrix' (K ∘ₗ S)).transpose =
      regularBoundaryProjector (G := G) (n + 1) := by
  classical
  let _ := Fintype.ofFinite Phys
  let _ := Fintype.ofFinite Out
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, Matrix.transpose_mul]
  calc
    _ = LinearMap.toMatrix' L * regularBoundaryCutMatrix n T S *
        (LinearMap.toMatrix' K).transpose := by
      simp only [regularBoundaryCutMatrix, Matrix.mul_assoc]
    _ = LinearMap.toMatrix' L * regularBoundaryCutMatrix n T' S' *
        (LinearMap.toMatrix' K).transpose := by rw [hcut]
    _ = LinearMap.toMatrix' (L ∘ₗ T') *
        (LinearMap.toMatrix' (K ∘ₗ S')).transpose := by
      simp only [regularBoundaryCutMatrix, LinearMap.toMatrix'_comp,
        Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hL, hK]
      change regularBoundaryProjector (n + 1) *
        (regularBoundaryProjector (n + 1)).transpose = _
      rw [regularBoundaryProjector_transpose, regularBoundaryProjector_mul_self]

omit [Fintype Phys] [Fintype Out] in
/-- Equal regular G-injective cut states admit compatible virtual boundary
comparisons. The comparisons recover both open maps and pair to the
invariant projector. This is a local statement about the whole boundary,
derived from SCP10, Definition 5.1 and Theorem 6.9,
lines 1278–1296 and 2043–2076. -/
theorem exists_regularBoundaryComparison_of_cut_eq [Finite Phys] [Finite Out] (n : ℕ)
    {T T' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S S' : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hS : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S)
    (hT' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T')
    (hS' : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S')
    (hcut : regularBoundaryCutMatrix n T S = regularBoundaryCutMatrix n T' S') :
    ∃ F K : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ),
      T' ∘ₗ F = T ∧ S' ∘ₗ K = S ∧
      LinearMap.toMatrix' F * (LinearMap.toMatrix' K).transpose =
        regularBoundaryProjector (G := G) (n + 1) ∧
      (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ F = F ∧
      (regularBoundaryRepresentation (G := G) (n + 1)).averageMap ∘ₗ K = K := by
  obtain ⟨_, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).mp hT'
  obtain ⟨_, K, hK⟩ := (isGInjective_iff_exists_leftInverse _ _).mp hS'
  have hleft := range_eq_of_regularBoundaryCutMatrix_eq n n hT hS hT' hS' hcut
  have hright := range_right_eq_of_regularBoundaryCutMatrix_eq n hT hS hT' hS' hcut
  exact ⟨L ∘ₗ T, K ∘ₗ S,
    hT'.comp_leftInverse_of_range_eq n hleft L hL,
    hS'.comp_leftInverse_of_range_eq n hright K hK,
    regularBoundaryComparison_pairing n L K hL hK hcut,
    averageMap_comp_leftInverse_of_range_eq n hleft L hL,
    averageMap_comp_leftInverse_of_range_eq n hright K hK⟩

end TNLean.PEPS
