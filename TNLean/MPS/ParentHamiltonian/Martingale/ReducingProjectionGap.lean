/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Gap transfer across a reducing projection

Let \(H\le K\) be positive operators which agree on the range of an
orthogonal projection \(Q\), with \(QH=HQ\) and \(1-Q\le 2H\).
The penalty forces every vector in \(\ker H\) into the range of \(Q\),
so \(H\) and \(K\) have the same kernel. A norm gap \(\delta\) for
\(K\) then gives the norm gap \(\min(\delta,1/2)\) for \(H\).

These are the finite-dimensional operator estimates used in the endpoint
sector decomposition of GLM23, arXiv:2203.12563, Section 5, lines 1690–1692
and 1695–1777. The physical application must derive the reducing projection,
the exact agreement on its range, and the penalty inequality.
-/

open scoped InnerProductSpace ComplexOrder

namespace Submodule

/-- A self-adjoint operator preserving a subspace commutes with its
orthogonal projection. -/
theorem commute_starProjection_of_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (Q : E →ₗ[ℂ] E) (hQ : Q.IsSymmetric) (hS : S.map Q ≤ S) :
    Commute Q S.starProjection.toLinearMap := by
  have hmem (v : E) (hv : v ∈ S) : Q v ∈ S := hS ⟨v, hv, rfl⟩
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  change Q (S.starProjection v) = S.starProjection (Q v)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := S)
  · exact hmem _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hQ]
    exact Submodule.starProjection_inner_eq_zero (K := S) v (Q w) (hmem w hw)

end Submodule

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The product of commuting orthogonal projections is an orthogonal
projection. -/
theorem IsSymmetricProjection.mul_of_commute
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hQ : Q.IsSymmetricProjection) (hPQ : Commute P Q) :
    (P * Q).IsSymmetricProjection :=
  ⟨hP.isIdempotentElem.mul_of_commute hPQ hQ.isIdempotentElem,
    hP.isSymmetric.mul_of_commute hQ.isSymmetric hPQ⟩

/-- The complement of a product of commuting orthogonal projections is
bounded by the sum of their complements. -/
theorem IsSymmetricProjection.one_sub_mul_le_add_one_sub
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hQ : Q.IsSymmetricProjection) (hPQ : Commute P Q) :
    1 - P * Q ≤ (1 - P) + (1 - Q) := by
  have hPComplement : (1 - P).IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hP.isSymmetric⟩
  have hQComplement : (1 - Q).IsSymmetricProjection :=
    ⟨hQ.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hQ.isSymmetric⟩
  have hComm : Commute (1 - P) (1 - Q) :=
    (Commute.one_left (1 - Q)).sub_left ((Commute.one_right P).sub_right hPQ)
  have hpos := (hPComplement.mul_of_commute hQComplement hComm).isPositive
  rw [LinearMap.le_def]
  convert hpos using 1
  noncomm_ring

/-- For three commuting orthogonal projections, the complement of their
product is bounded by the sum of the three complementary projections. -/
theorem IsSymmetricProjection.one_sub_mul_mul_le
    {P R C : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hR : R.IsSymmetricProjection) (hC : C.IsSymmetricProjection)
    (hRC : Commute R C) (hRP : Commute R P) (hCP : Commute C P) :
    1 - R * C * P ≤ (1 - P) + (1 - R) + (1 - C) := by
  have h₁ := (hR.mul_of_commute hC hRC).one_sub_mul_le_add_one_sub hP
    (hRP.mul_left hCP)
  have h₂ := hR.one_sub_mul_le_add_one_sub hC hRC
  change ((1 - R * C) + (1 - P) - (1 - R * C * P)).IsPositive at h₁
  change ((1 - R) + (1 - C) - (1 - R * C)).IsPositive at h₂
  rw [LinearMap.le_def]
  convert h₁.add h₂ using 1
  abel

/-- Two ordered operators agree on a vector when their positive difference
is bounded by an operator annihilating that vector. -/
theorem apply_eq_of_le_of_sub_le_of_apply_eq_zero
    {H K T : E →ₗ[ℂ] E} (hHK : H ≤ K) (hDifference : K - H ≤ T)
    {v : E} (hv : T v = 0) : H v = K v := by
  have hzero := (LinearMap.le_def.mp hHK).ker_le_of_le hDifference
    (LinearMap.mem_ker.mpr hv)
  have hsub : K v - H v = 0 := LinearMap.mem_ker.mp hzero
  exact (sub_eq_zero.mp hsub).symm

/-- A projection whose complementary penalty is bounded by \(2H\) fixes
every vector in \(\ker H\). No commutation hypothesis is needed. -/
theorem IsSymmetricProjection.apply_eq_self_of_one_sub_le_twice_of_mem_ker
    {H Q : E →ₗ[ℂ] E} (hQ : Q.IsSymmetricProjection)
    (hPenalty : 1 - Q ≤ (2 : ℂ) • H) {v : E} (hv : v ∈ LinearMap.ker H) :
    Q v = v := by
  have hComplement : (1 - Q).IsSymmetricProjection :=
    ⟨hQ.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hQ.isSymmetric⟩
  have hvScaled : v ∈ LinearMap.ker ((2 : ℂ) • H) := by
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.mem_ker.mp hv,
      smul_zero]
  have hvComplement := hComplement.isPositive.ker_le_of_le hPenalty hvScaled
  have hzero : v - Q v = 0 := LinearMap.mem_ker.mp hvComplement
  exact (sub_eq_zero.mp hzero).symm

/-- The bound \(1-Q\le 2H\) gives energy at least \(1/2\) on
vectors annihilated by \(Q\). -/
theorem re_inner_ge_half_of_one_sub_le_twice
    {H Q : E →ₗ[ℂ] E} (hPenalty : 1 - Q ≤ (2 : ℂ) • H)
    (v : E) (hv : Q v = 0) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
  have hbound : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (⟪v, H v⟫_ℂ).re := by
    have hpos := (LinearMap.le_def.mp hPenalty).re_inner_nonneg_right v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv,
      sub_zero, inner_sub_right, inner_smul_right, map_sub, inner_self_eq_norm_sq] at hpos
    norm_num at hpos
    linarith
  calc
    _ ≤ (⟪v, H v⟫_ℂ).re := hbound
    _ = _ := inner_re_symm (𝕜 := ℂ) v (H v)

namespace IsPositive

/-- If \(H\le K\), the two operators agree on the range of \(Q\),
and \(1-Q\le 2H\), then \(\ker H=\ker K\). -/
theorem ker_eq_of_le_of_eq_on_projection
    {H K Q : E →ₗ[ℂ] E} (hH : H.IsPositive) (hQ : Q.IsSymmetricProjection)
    (hHK : H ≤ K) (hActive : H * Q = K * Q)
    (hPenalty : 1 - Q ≤ (2 : ℂ) • H) :
    LinearMap.ker H = LinearMap.ker K := by
  apply le_antisymm
  · intro v hv
    have hQv := hQ.apply_eq_self_of_one_sub_le_twice_of_mem_ker hPenalty hv
    have hEq : H (Q v) = K (Q v) := LinearMap.congr_fun hActive v
    rw [hQv, LinearMap.mem_ker.mp hv] at hEq
    exact LinearMap.mem_ker.mpr hEq.symm
  · exact hH.ker_le_of_le hHK

/-- A positive operator agreeing with a gapped comparison operator on a
reducing projection inherits the gap \(\min(\delta,1/2)\), when its
complementary projection is bounded by \(2H\). -/
theorem norm_gap_of_reducing_projection [FiniteDimensional ℂ E]
    {H K Q : E →ₗ[ℂ] E} (hH : H.IsPositive) (hK : K.IsPositive)
    (hQ : Q.IsSymmetricProjection) (hComm : Commute Q H)
    (hHK : H ≤ K) (hActive : H * Q = K * Q)
    (hPenalty : 1 - Q ≤ (2 : ℂ) • H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ v ∈ (LinearMap.ker K)ᗮ, δ * ‖v‖ ≤ ‖K v‖) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, min δ (1 / 2) * ‖v‖ ≤ ‖H v‖ := by
  have hker := hH.ker_eq_of_le_of_eq_on_projection hQ hHK hActive hPenalty
  have hCommApply (z : E) : H (Q z) = Q (H z) :=
    LinearMap.congr_fun hComm.eq.symm z
  intro v hv
  let x := Q v
  let y := v - x
  have hsum : x + y = v := by dsimp [y]; abel
  have hQx : Q x = x := LinearMap.congr_fun hQ.isIdempotentElem.eq v
  have hQy : Q y = 0 := by
    change Q (v - x) = 0
    rw [map_sub, hQx]
    exact sub_self x
  have horth (z : E) : ⟪Q z, y⟫_ℂ = 0 := by
    rw [hQ.isSymmetric, hQy, inner_zero_right]
  have hx : x ∈ (LinearMap.ker K)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hzH : z ∈ LinearMap.ker H := by rwa [hker]
    change ⟪z, Q v⟫_ℂ = 0
    calc
      _ = ⟪Q z, v⟫_ℂ := (hQ.isSymmetric z v).symm
      _ = ⟪z, v⟫_ℂ := by
        rw [hQ.apply_eq_self_of_one_sub_le_twice_of_mem_ker hPenalty hzH]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal hzH hv
  have hHx : H x = K x := LinearMap.congr_fun hActive v
  have hcrossLeft : ⟪H x, y⟫_ℂ = 0 := by
    change ⟪H (Q v), y⟫_ℂ = 0
    rw [hCommApply]
    exact horth (H v)
  have hcrossRight : ⟪H y, x⟫_ℂ = 0 := by
    rw [hH.isSymmetric]
    exact inner_eq_zero_symm.mpr hcrossLeft
  have henergy : (⟪H v, v⟫_ℂ).re =
      (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
    calc
      _ = (⟪H (x + y), x + y⟫_ℂ).re := by rw [hsum]
      _ = _ := by
        rw [map_add, inner_add_left, inner_add_right, inner_add_right,
          hcrossLeft, hcrossRight, hHx]
        simp
  have hnorm : ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    calc
      _ = ‖x + y‖ ^ 2 := by rw [hsum]
      _ = _ := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y (horth v)
  have hactive := hK.re_inner_ge_of_norm_gap hδ hGap x hx
  have hinactive := re_inner_ge_half_of_one_sub_le_twice hPenalty y hQy
  have hquadratic : min δ (1 / 2) * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
    rw [hnorm, henergy, mul_add]
    exact add_le_add
      ((mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hactive)
      ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans hinactive)
  have hbound := hquadratic.trans (re_inner_le_norm (𝕜 := ℂ) (H v) v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact le_of_mul_le_mul_right
      (by simpa only [pow_two, mul_assoc] using hbound) (norm_pos_iff.mpr hv0)

end IsPositive
end LinearMap
