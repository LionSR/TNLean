/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Martingale differences of nested ground-space projections

This file formalizes the projection resolution used in Nachtergaele's
martingale method (cond-mat/9410110, equation (En) and the proof of Theorem
2.1(i)). For a decreasing family of orthogonal ground-space projections
\(G_n\), its martingale differences are

\[
E_n = G_n-G_{n+1}.
\]

Each \(E_n\) is an orthogonal projection, distinct differences are mutually
orthogonal, and their finite sums telescope. With the source endpoint
conventions \(G_0=\mathrm{id}\) and \(G_{N+1}=0\), the complete sum is the
identity. If \(v\perp\operatorname{range}(G_N)\), the truncated resolution
reconstructs \(v\) and gives the Pythagorean decomposition

\[
v=\sum_{n=0}^{N-1}E_nv,
\qquad
\lVert v\rVert^2=\sum_{n=0}^{N-1}\lVert E_nv\rVert^2.
\]
-/

open scoped BigOperators InnerProductSpace

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A decreasing family of orthogonal projections, abstracting the nested
finite-volume ground-space projections \(G_{\Lambda_n}\). -/
structure NestedGroundProjections where
  /-- The ground-space projection at level \(n\). -/
  projection : ℕ → E →ₗ[ℂ] E
  /-- Each ground-space operator is an orthogonal projection. -/
  isSymmetricProjection : ∀ n, (projection n).IsSymmetricProjection
  /-- Ground-space ranges decrease as the volume grows. -/
  antitone_range : Antitone fun n ↦ LinearMap.range (projection n)

namespace NestedGroundProjections

variable (G : NestedGroundProjections (E := E))

/-- Nachtergaele's martingale difference \(E_n=G_n-G_{n+1}\). -/
def martingaleDifference (n : ℕ) : E →ₗ[ℂ] E :=
  G.projection n - G.projection (n + 1)

private theorem projection_comp_eq_of_le {m n : ℕ} (hmn : m ≤ n) :
    (G.projection m).comp (G.projection n) = G.projection n :=
  (LinearMap.IsIdempotentElem.comp_eq_right_iff
    (G.isSymmetricProjection m).isIdempotentElem (G.projection n)).mpr
      (G.antitone_range hmn)

private theorem projection_comp_eq_of_ge {m n : ℕ} (hmn : m ≤ n) :
    (G.projection n).comp (G.projection m) = G.projection n := by
  ext x
  apply ext_inner_left ℂ
  intro y
  calc
    ⟪y, G.projection n (G.projection m x)⟫_ℂ =
        ⟪G.projection n y, G.projection m x⟫_ℂ :=
      ((G.isSymmetricProjection n).isSymmetric y (G.projection m x)).symm
    _ = ⟪G.projection m (G.projection n y), x⟫_ℂ :=
      ((G.isSymmetricProjection m).isSymmetric (G.projection n y) x).symm
    _ = ⟪G.projection n y, x⟫_ℂ := by
      rw [← LinearMap.comp_apply, G.projection_comp_eq_of_le hmn]
    _ = ⟪y, G.projection n x⟫_ℂ :=
      (G.isSymmetricProjection n).isSymmetric y x

/-- A difference of two consecutive nested ground-space projections is itself
an orthogonal projection. -/
theorem martingaleDifference_isSymmetricProjection (n : ℕ) :
    (G.martingaleDifference n).IsSymmetricProjection :=
  (G.isSymmetricProjection (n + 1)).sub_of_range_le_range
    (G.isSymmetricProjection n) (G.antitone_range (Nat.le_succ n))

/-- Distinct martingale differences have zero product. This is the
\(E_nE_m=0\) part of equation (En). -/
theorem martingaleDifference_comp_eq_zero {m n : ℕ} (hmn : m ≠ n) :
    (G.martingaleDifference m).comp (G.martingaleDifference n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · simp only [martingaleDifference, LinearMap.sub_comp, LinearMap.comp_sub]
    rw [G.projection_comp_eq_of_le hmn.le,
      G.projection_comp_eq_of_le (hmn.le.trans (Nat.le_succ n)),
      G.projection_comp_eq_of_le hmn,
      G.projection_comp_eq_of_le (Nat.succ_le_succ hmn.le)]
    simp
  · simp only [martingaleDifference, LinearMap.sub_comp, LinearMap.comp_sub]
    rw [G.projection_comp_eq_of_ge hnm.le,
      G.projection_comp_eq_of_ge hnm,
      G.projection_comp_eq_of_ge (hnm.le.trans (Nat.le_succ m)),
      G.projection_comp_eq_of_ge (Nat.succ_le_succ hnm.le)]
    simp

/-- The complete product rule
\(E_nE_m=\delta_{n,m}E_n\) for martingale differences. -/
theorem martingaleDifference_comp (m n : ℕ) :
    (G.martingaleDifference m).comp (G.martingaleDifference n) =
      if m = n then G.martingaleDifference m else 0 := by
  split_ifs with hmn
  · subst n
    simpa [Module.End.mul_eq_comp] using
      (G.martingaleDifference_isSymmetricProjection m).isIdempotentElem.eq
  · exact G.martingaleDifference_comp_eq_zero hmn

/-- Images under distinct martingale differences are orthogonal. -/
theorem inner_martingaleDifference_eq_zero {m n : ℕ} (hmn : m ≠ n) (x y : E) :
    ⟪G.martingaleDifference m x, G.martingaleDifference n y⟫_ℂ = 0 := by
  rw [(G.martingaleDifference_isSymmetricProjection m).isSymmetric]
  change ⟪x, ((G.martingaleDifference m).comp (G.martingaleDifference n)) y⟫_ℂ = 0
  rw [G.martingaleDifference_comp_eq_zero hmn]
  simp

/-- A vector fixed by the ground-space projection at level \(n_0\) is
annihilated by every earlier martingale difference. This is the vanishing that
the proof of Nachtergaele's Theorem 2.1(i) (arXiv:cond-mat/9410110, lines
1195--1259) needs at the indices below the lower endpoints of its conditions
C2 and C3. -/
theorem martingaleDifference_apply_eq_zero_of_lt {n₀ n : ℕ} (hn : n < n₀)
    (v : E) (hv : G.projection n₀ v = v) : G.martingaleDifference n v = 0 := by
  have hfix : ∀ m, m ≤ n₀ → G.projection m v = v := by
    intro m hm
    calc
      G.projection m v = G.projection m (G.projection n₀ v) := by rw [hv]
      _ = ((G.projection m).comp (G.projection n₀)) v := rfl
      _ = G.projection n₀ v := by rw [G.projection_comp_eq_of_le hm]
      _ = v := hv
  simp only [martingaleDifference, LinearMap.sub_apply, hfix n hn.le,
    hfix (n + 1) hn, sub_self]

/-- The finite martingale-difference sum telescopes with both endpoints shown
explicitly. -/
theorem sum_martingaleDifference (N : ℕ) :
    ∑ n ∈ Finset.range N, G.martingaleDifference n =
      G.projection 0 - G.projection N := by
  simpa [martingaleDifference] using Finset.sum_range_sub' G.projection N

/-- Under the source conventions \(G_0=\mathrm{id}\) and \(G_{N+1}=0\),
the martingale differences \(E_0,\ldots,E_N\) sum to the identity. -/
theorem sum_martingaleDifference_eq_id (N : ℕ)
    (hzero : G.projection 0 = LinearMap.id)
    (hfinal : G.projection (N + 1) = 0) :
    ∑ n ∈ Finset.range (N + 1), G.martingaleDifference n = LinearMap.id := by
  rw [G.sum_martingaleDifference, hzero, hfinal, sub_zero]

/-- The squared norm of a martingale-difference sum over any finite index set
is the sum of the squared norms of its terms. -/
theorem norm_sq_sum_martingaleDifference_finset (s : Finset ℕ) (v : E) :
    ‖∑ n ∈ s, G.martingaleDifference n v‖ ^ 2 =
      ∑ n ∈ s, ‖G.martingaleDifference n v‖ ^ 2 := by
  let V : (n : ℕ) →
      LinearMap.range (G.martingaleDifference n) →ₗᵢ[ℂ] E :=
    fun n ↦ (LinearMap.range (G.martingaleDifference n)).subtypeₗᵢ
  have hV : OrthogonalFamily ℂ
      (fun n : ℕ ↦ LinearMap.range (G.martingaleDifference n)) V := by
    intro m n hmn x y
    obtain ⟨x', hx⟩ := x.property
    obtain ⟨y', hy⟩ := y.property
    change ⟪(x : E), (y : E)⟫_ℂ = 0
    rw [← hx, ← hy]
    exact G.inner_martingaleDifference_eq_zero hmn x' y'
  simpa [V] using hV.norm_sum
    (fun n ↦ ⟨G.martingaleDifference n v, ⟨v, rfl⟩⟩) s

/-- The squared norm of an initial martingale-difference sum is the sum of the
squared norms of its terms. -/
theorem norm_sq_sum_martingaleDifference (N : ℕ) (v : E) :
    ‖∑ n ∈ Finset.range N, G.martingaleDifference n v‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖G.martingaleDifference n v‖ ^ 2 :=
  G.norm_sq_sum_martingaleDifference_finset (Finset.range N) v

/-- A vector orthogonal to the final ground space is reconstructed by the
truncated martingale-difference sum. This is `resolutionpsi` in the proof of
Nachtergaele's Theorem 2.1(i). -/
theorem sum_martingaleDifference_apply_of_mem_orthogonal (N : ℕ) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ) :
    ∑ n ∈ Finset.range N, G.martingaleDifference n v = v := by
  rw [(G.isSymmetricProjection N).isSymmetric.orthogonal_range] at hv
  have hvzero : G.projection N v = 0 := LinearMap.mem_ker.mp hv
  calc
    ∑ n ∈ Finset.range N, G.martingaleDifference n v =
        (∑ n ∈ Finset.range N, G.martingaleDifference n) v := by simp
    _ = (G.projection 0 - G.projection N) v := by rw [G.sum_martingaleDifference]
    _ = v := by simp [hzero, hvzero]

/-- The Pythagorean norm-square decomposition `resolutionnormpsi` in the proof
of Nachtergaele's Theorem 2.1(i). -/
theorem norm_sq_eq_sum_martingaleDifference_of_mem_orthogonal (N : ℕ) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ) :
    ‖v‖ ^ 2 = ∑ n ∈ Finset.range N, ‖G.martingaleDifference n v‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 = ‖∑ n ∈ Finset.range N, G.martingaleDifference n v‖ ^ 2 := by
      rw [G.sum_martingaleDifference_apply_of_mem_orthogonal N v hzero hv]
    _ = ∑ n ∈ Finset.range N, ‖G.martingaleDifference n v‖ ^ 2 :=
      G.norm_sq_sum_martingaleDifference N v

end NestedGroundProjections

end FrustrationFree
