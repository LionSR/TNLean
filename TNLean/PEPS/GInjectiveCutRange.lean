/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveRangeEquivalence
import TNLean.PEPS.RegularBoundaryState

/-!
# Physical ranges recovered from a regular G-injective cut

Suppose two open-region maps share a boundary of regular group labels and are
G-injective for its simultaneous regular action. Contracting their boundary
indices gives a bipartite coefficient matrix whose column space is exactly
the physical range of the first region map. Thus the bipartite state determines
that physical range, despite the kernel forced by the virtual symmetry.

This is an auxiliary linear-algebra consequence of the open-boundary cut and
G-injectivity in Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1
and the cut in the proof of Theorem 6.9, local source lines 1278–1296 and
2043–2076. The identification of a particular PEPS cut with these regular
boundary maps is a separate geometric assertion.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G Phys Out : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype Phys] [DecidableEq Phys] [Fintype Out] [DecidableEq Out]

noncomputable local instance instInvertibleCardCutRange : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Contract the common regular boundary of two open physical maps.
Source: SCP10, proof of Theorem 6.9, lines 2043–2076. -/
noncomputable def regularBoundaryCutMatrix (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ))
    (S : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)) : Matrix Phys Out ℂ :=
  LinearMap.toMatrix' T * (LinearMap.toMatrix' S).transpose

omit [Fintype Phys] [DecidableEq Phys] [DecidableEq Out] in
/-- The column space of a contracted regular G-injective cut is exactly the
range of its first open-region map. This is an auxiliary consequence of SCP10,
Definition 5.1 and the cut in Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem IsGInjective.range_regularBoundaryCutMatrix (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hS : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S) :
    (Matrix.mulVecLin (regularBoundaryCutMatrix n T S)).range = T.range := by
  classical
  obtain ⟨_, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).mp hS
  have hTavg : T ∘ₗ (regularBoundaryRepresentation (G := G) (n + 1)).averageMap = T :=
    LinearMap.ext (apply_averageMap_of_forall_comp_eq hT.invariant)
  have hrecover : regularBoundaryCutMatrix n T S * (LinearMap.toMatrix' L).transpose =
      LinearMap.toMatrix' T := by
    rw [regularBoundaryCutMatrix, Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← LinearMap.toMatrix'_comp, hL]
    rw [show (LinearMap.toMatrix'
        (regularBoundaryRepresentation (G := G) (n + 1)).averageMap).transpose =
        LinearMap.toMatrix' (regularBoundaryRepresentation (G := G) (n + 1)).averageMap
      from regularBoundaryProjector_transpose n, ← LinearMap.toMatrix'_comp, hTavg]
  have hforward : Matrix.mulVecLin (regularBoundaryCutMatrix n T S) =
      T ∘ₗ Matrix.mulVecLin (LinearMap.toMatrix' S).transpose := by
    simp only [regularBoundaryCutMatrix, ← Matrix.toLin'_apply',
      Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  have hreverse : T = Matrix.mulVecLin (regularBoundaryCutMatrix n T S) ∘ₗ
      Matrix.mulVecLin (LinearMap.toMatrix' L).transpose := by
    simpa only [← Matrix.toLin'_apply', Matrix.toLin'_mul, Matrix.toLin'_toMatrix'] using
      congrArg Matrix.toLin' hrecover.symm
  exact le_antisymm
    ((congrArg LinearMap.range hforward).le.trans (LinearMap.range_comp_le_range _ _))
    ((congrArg LinearMap.range hreverse).le.trans (LinearMap.range_comp_le_range _ _))

omit [Fintype Phys] [DecidableEq Phys] [DecidableEq Out] in
/-- A cut between two regular G-injective open maps has Schmidt rank equal
to the invariant-boundary dimension. Source: SCP10, the boundary dimension
calculation in Theorem 6.9, lines 2043–2076. This assertion concerns the
specified open maps, without an isometry assumption. -/
theorem IsGInjective.rank_regularBoundaryCutMatrix (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hS : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S) :
    (regularBoundaryCutMatrix n T S).rank = Fintype.card G ^ n := by
  change Module.finrank ℂ (Matrix.mulVecLin (regularBoundaryCutMatrix n T S)).range = _
  rw [hT.range_regularBoundaryCutMatrix n hS, hT.finrank_range,
    finrank_regularBoundaryInvariants_succ]

variable {H : Type*} [Group H] [Fintype H] [DecidableEq H]

omit [Fintype Phys] [Fintype Out] [DecidableEq Phys] [DecidableEq Out] in
/-- Equal bipartite coefficients determine equal physical ranges when both
factorizations are regular G-injective cuts. The virtual groups and boundary
sizes may differ. This is an auxiliary local comparison following SCP10,
Definition 5.1 and the cut in Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem range_eq_of_regularBoundaryCutMatrix_eq [Finite Out] (n m : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    {T' : ((Fin (m + 1) → H) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    {S' : ((Fin (m + 1) → H) → ℂ) →ₗ[ℂ] (Out → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hS : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) S)
    (hT' : IsGInjective (regularBoundaryRepresentation (G := H) (m + 1)) T')
    (hS' : IsGInjective (regularBoundaryRepresentation (G := H) (m + 1)) S')
    (hcut : regularBoundaryCutMatrix n T S = regularBoundaryCutMatrix m T' S') :
    T.range = T'.range := by
  let _ := Fintype.ofFinite Out
  exact (hT.range_regularBoundaryCutMatrix n hS).symm.trans
    ((congrArg (fun M => (Matrix.mulVecLin M).range) hcut).trans
      (hT'.range_regularBoundaryCutMatrix m hS'))

end TNLean.PEPS
