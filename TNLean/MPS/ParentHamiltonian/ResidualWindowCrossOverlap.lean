/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinsetNormSumCauchySchwarz
import TNLean.MPS.ParentHamiltonian.ResidualWindowCoordinates
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceOverlap
import QICLean.Analysis.TwoProjectionCompression
/-!
# Cross-sector overlaps of residual windows

Fixing the outer blocked prefix and the original tail of a residual window
leaves a vector on the common middle interval. A right window in one sector
and a left window in another sector therefore have inner product equal to
a sum of middle-interval sector pairings. Finite Cauchy--Schwarz transfers
a relative prefix-angle bound to the two full window ranges with exactly
the same coefficient, independently of both outer lengths.

For primitive inequivalent middle tensors with faithful invariant matrices,
the resulting product of orthogonal range projections tends to zero as the
middle length diverges. Both outer lengths may vary arbitrarily. No boundary
inverse, tail normalization, or letter intertwining is needed for this
cross-sector estimate. It supplies the off-diagonal part of the projection
comparison; the same-sector defect remains a separate estimate.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint,
lines 1744--1820, and Lemma commutation (ii), lines 2442--2531;
the residual coordinates follow DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D E F L : ℕ}

private noncomputable def windowMiddleFiber {K M r : ℕ}
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r)))
    (u : Cfg (blockPhysDim d L) K) (τ : Cfg d r) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d L) M) :=
  WithLp.toLp 2 fun v => x (u, (v, τ))

private theorem inner_eq_sum_windowMiddleFiber {K M r : ℕ}
    (x y : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r))) :
    ⟪x, y⟫_ℂ = ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
      ⟪windowMiddleFiber x u τ, windowMiddleFiber y u τ⟫_ℂ := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, windowMiddleFiber]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.sum_comm

private theorem sum_norm_sq_windowMiddleFiber {K M r : ℕ}
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r))) :
    ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
      ‖windowMiddleFiber x u τ‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [map_sum, ← norm_sq_eq_re_inner] using
    (congrArg (RCLike.re : ℂ →+ ℝ) (inner_eq_sum_windowMiddleFiber x x)).symm

private theorem windowMiddleFiber_rightMap
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (u : Cfg (blockPhysDim d L) K) (τ : Cfg d r) :
    windowMiddleFiber (residualWindowRightMapES A B V K M r x) u τ =
      groundSpaceMapES B M (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
        (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x)) := by
  ext v
  change Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
    Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u x) = _
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply]
  change Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
    Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u x) =
    Matrix.trace (Kraus.evalWord B (List.ofFn v) *
      (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x))
  simp only [Matrix.mul_assoc]

private theorem windowMiddleFiber_leftMap
    (B : MPSTensor (blockPhysDim d L) F) (K M r : ℕ)
    (y : BoundaryFamilySpace (D := F) (Cfg d r))
    (u : Cfg (blockPhysDim d L) K) (τ : Cfg d r) :
    windowMiddleFiber (residualWindowLeftMapES B K M r y) u τ =
      groundSpaceMapES B M (Matrix.frobeniusEquivEuclidean (Fin F) (Fin F)
        (boundaryFamilyEquiv (D := F) (Cfg d r) y τ *
          Kraus.evalWord B (List.ofFn u))) := by
  ext v
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply]
  change Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v)) *
    boundaryFamilyEquiv (D := F) (Cfg d r) y τ) =
    Matrix.trace (Kraus.evalWord B (List.ofFn v) *
      (boundaryFamilyEquiv (D := F) (Cfg d r) y τ * Kraus.evalWord B (List.ofFn u)))
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (Kraus.evalWord B (List.ofFn u))
    (Kraus.evalWord B (List.ofFn v) * boundaryFamilyEquiv (D := F) (Cfg d r) y τ)

/-- The mixed inner product of a right residual window and a left window is the sum of their
middle-interval boundary pairings. The sector bond dimensions may differ, and every length
may be zero. -/
theorem inner_residualWindowRightMapES_leftMapES_cross_sector
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (B' : MPSTensor (blockPhysDim d L) F) (V : Matrix (Fin D) (Fin E) ℂ)
    (K M r : ℕ)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (y : BoundaryFamilySpace (D := F) (Cfg d r)) :
    ⟪residualWindowRightMapES A B V K M r x, residualWindowLeftMapES B' K M r y⟫_ℂ =
      ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
        ⟪groundSpaceMapES B M (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x)),
          groundSpaceMapES B' M (Matrix.frobeniusEquivEuclidean (Fin F) (Fin F)
            (boundaryFamilyEquiv (D := F) (Cfg d r) y τ *
              Kraus.evalWord B' (List.ofFn u)))⟫_ℂ := by
  simpa only [windowMiddleFiber_rightMap, windowMiddleFiber_leftMap] using
    inner_eq_sum_windowMiddleFiber (residualWindowRightMapES A B V K M r x)
      (residualWindowLeftMapES B' K M r y)

private theorem norm_inner_le_of_windowMiddleFiber_bound {K M r : ℕ}
    (x y : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r))) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ u : Cfg (blockPhysDim d L) K, ∀ τ : Cfg d r,
      ‖⟪windowMiddleFiber x u τ, windowMiddleFiber y u τ⟫_ℂ‖ ≤
        ε * ‖windowMiddleFiber x u τ‖ * ‖windowMiddleFiber y u τ‖) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  rw [inner_eq_sum_windowMiddleFiber]
  simpa only [Fintype.sum_prod_type, sum_norm_sq_windowMiddleFiber, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_assoc] using
    Finset.norm_sum_le_mul_sqrt_mul_sqrt Finset.univ
      (fun p : Cfg (blockPhysDim d L) K × Cfg d r =>
        ⟪windowMiddleFiber x p.1 p.2, windowMiddleFiber y p.1 p.2⟫_ℂ)
      (fun p => ‖windowMiddleFiber x p.1 p.2‖) (fun p => ‖windowMiddleFiber y p.1 p.2‖)
      hε (fun p _ => h p.1 p.2)

/-- A relative middle-interval angle bound transfers to the full right and left window ranges
with the same coefficient. No normalization, injectivity, or boundary inverse is assumed. -/
theorem norm_inner_residualWindowRightMapES_leftMapES_le_of_prefix_bound
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (B' : MPSTensor (blockPhysDim d L) F) (V : Matrix (Fin D) (Fin E) ℂ)
    {K M r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hAngle : ∀ x ∈ groundSpaceES B M, ∀ y ∈ groundSpaceES B' M,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    {x y : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r))}
    (hx : x ∈ (residualWindowRightMapES A B V K M r).range)
    (hy : y ∈ (residualWindowLeftMapES B' K M r).range) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  apply norm_inner_le_of_windowMiddleFiber_bound _ _ hε
  intro u τ
  change ‖⟪windowMiddleFiber (residualWindowRightMapES A B V K M r x) u τ,
    windowMiddleFiber (residualWindowLeftMapES B' K M r y) u τ⟫_ℂ‖ ≤
      ε * ‖windowMiddleFiber (residualWindowRightMapES A B V K M r x) u τ‖ *
        ‖windowMiddleFiber (residualWindowLeftMapES B' K M r y) u τ‖
  rw [windowMiddleFiber_rightMap A B V K M r x u τ,
    windowMiddleFiber_leftMap B' K M r y u τ]
  apply hAngle
  · rw [← range_groundSpaceMapES]
    exact ⟨_, rfl⟩
  · rw [← range_groundSpaceMapES]
    exact ⟨_, rfl⟩

/-- A relative middle-interval angle bound controls the product of the right and left orthogonal
range projections with the same coefficient. -/
theorem norm_residualWindowRightMapES_projection_comp_leftMapES_projection_le
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (B' : MPSTensor (blockPhysDim d L) F) (V : Matrix (Fin D) (Fin E) ℂ)
    {K M r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hAngle : ∀ x ∈ groundSpaceES B M, ∀ y ∈ groundSpaceES B' M,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖) :
    ‖(residualWindowRightMapES A B V K M r).range.starProjection.comp
      (residualWindowLeftMapES B' K M r).range.starProjection‖ ≤ ε := by
  have h := Submodule.norm_starProjection_comp_sub_starProjection_le_of_relative_overlap
    (residualWindowRightMapES A B V K M r).range
    (residualWindowLeftMapES B' K M r).range ⊥ bot_le bot_le hε
    (fun x hx _ y hy _ =>
      norm_inner_residualWindowRightMapES_leftMapES_le_of_prefix_bound A B B' V hε hAngle hx hy)
  simpa only [Submodule.starProjection_bot, sub_zero] using h

/-- Inequivalent primitive middle tensors with faithful invariant matrices have uniformly small
cross-sector window projections once the middle interval is sufficiently long. The bound
holds simultaneously for every outer blocked-prefix length and original-tail length. Source:
Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint, lines 1744--1820. -/
theorem IsPrimitiveMPS.eventually_norm_residualWindow_cross_projection_le_of_inequivalent
    [NeZero E] [NeZero F]
    (A : MPSTensor d D) {B : MPSTensor (blockPhysDim d L) E}
    {B' : MPSTensor (blockPhysDim d L) F} (V : Matrix (Fin D) (Fin E) ℂ)
    {ρ : Matrix (Fin E) (Fin E) ℂ} {σ : Matrix (Fin F) (Fin F) ℂ}
    (hB : IsPrimitiveMPS B ρ) (hB' : IsPrimitiveMPS B' σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ e : F = E, ¬ GaugePhaseEquiv (e ▸ B') B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in Filter.atTop, ∀ K r : ℕ,
      ‖(residualWindowRightMapES A B V K M r).range.starProjection.comp
        (residualWindowLeftMapES B' K M r).range.starProjection‖ ≤ ε := by
  filter_upwards [hB.eventually_norm_inner_groundSpaceES_le_of_inequivalent
    hB' hρ hσ hDistinct hε] with M hM
  exact fun K r =>
    norm_residualWindowRightMapES_projection_comp_leftMapES_projection_le
      A B B' V (K := K) (r := r) hε.le hM

/-- Cross-sector window projection products tend to zero along any diverging middle interval,
while both outer lengths may vary arbitrarily. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma disjoint, lines 1744--1820. -/
theorem IsPrimitiveMPS.residualWindow_cross_projection_tendsto_zero_of_inequivalent
    [NeZero E] [NeZero F]
    (A : MPSTensor d D) {B : MPSTensor (blockPhysDim d L) E}
    {B' : MPSTensor (blockPhysDim d L) F} (V : Matrix (Fin D) (Fin E) ℂ)
    {ρ : Matrix (Fin E) (Fin E) ℂ} {σ : Matrix (Fin F) (Fin F) ℂ}
    (hB : IsPrimitiveMPS B ρ) (hB' : IsPrimitiveMPS B' σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ e : F = E, ¬ GaugePhaseEquiv (e ▸ B') B)
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ}
    (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun i =>
      ‖(residualWindowRightMapES A B V (K i) (M i) (r i)).range.starProjection.comp
        (residualWindowLeftMapES B' (K i) (M i) (r i)).range.starProjection‖) f (nhds 0) := by
  apply tendsto_order.2
  constructor
  · exact fun a ha => Filter.Eventually.of_forall fun _ => ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [hM.eventually
      (hB.eventually_norm_residualWindow_cross_projection_le_of_inequivalent
        A V hB' hρ hσ hDistinct (half_pos hε))] with i hi
    exact (hi (K i) (r i)).trans_lt (half_lt_self hε)
end MPSTensor
