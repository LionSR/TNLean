/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicResidualGroundSpace
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.GroundSpaceSectorCompressionDecay

/-!
# Overlaps of correlated residual boundary spaces

Fixing the original tail of a rectangular residual boundary vector gives
an ordinary blocked-prefix ground vector. Summing these fibers and applying
Cauchy--Schwarz transfers any prefix angle bound to the residual ranges with
exactly the same coefficient, uniformly in the tail length. The tail remains
correlated with its virtual boundary throughout the argument.

For primitive inequivalent prefix tensors, the resulting residual angles tend
to zero. For a finite such family, the sum of the residual-sector projections
therefore approaches the projection onto their joint span. These conclusions
hold for arbitrary tail lengths; no inverse residual Gram matrix is used.
The finite estimate requires no normalization or intertwining hypothesis.
The primitive consequences explicitly assume primitive prefix tensors with
faithful invariant matrices and pairwise gauge-phase inequivalence. No
periodic-tensor projection defect or all-residue spectral gap is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint,
lines 1744--1820, and Lemma commutation (i), lines 2442--2531;
the correlated residual coordinates extend the blocking calculation in
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D E F L : ℕ}

private noncomputable def residualConfigEquiv (d N L r : ℕ) :
    Cfg (blockPhysDim d L) N × Cfg d r ≃ Cfg d (N * L + r) :=
  (Equiv.prodCongr (blockedConfigEquiv d N L) (Equiv.refl (Cfg d r))).trans
    (Fin.appendEquiv (N * L) r)

private noncomputable def residualPrefixFiber {N r : ℕ}
    (x : EuclideanSpace ℂ (Cfg d (N * L + r))) (τ : Cfg d r) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d L) N) :=
  WithLp.toLp 2 fun σ => x (residualConfigEquiv d N L r (σ, τ))

private theorem residualPrefixFiber_boundaryMap
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ)
    (Y : Matrix (Fin D) (Fin E) ℂ) (τ : Cfg d r) :
    residualPrefixFiber (L := L)
      (blockedResidualBoundaryMapES A L B V N r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)) τ =
      groundSpaceMapES B N (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
        (Vᴴ * Kraus.evalWord A (List.ofFn τ) * Y)) := by
  rw [blockedResidualBoundaryMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  ext σ
  simp [residualPrefixFiber, residualConfigEquiv, blockedResidualBoundaryMap,
    groundSpaceMap_apply, Matrix.mul_assoc, Fin.appendEquiv, Function.comp_def]

private theorem inner_eq_sum_residualPrefixFiber {N r : ℕ}
    (x y : EuclideanSpace ℂ (Cfg d (N * L + r))) :
    ⟪x, y⟫_ℂ = ∑ τ : Cfg d r,
      ⟪residualPrefixFiber (L := L) x τ, residualPrefixFiber (L := L) y τ⟫_ℂ := by
  rw [PiLp.inner_apply]
  trans ∑ p : Cfg (blockPhysDim d L) N × Cfg d r,
    ⟪x (residualConfigEquiv d N L r p), y (residualConfigEquiv d N L r p)⟫_ℂ
  · symm
    exact Fintype.sum_equiv (residualConfigEquiv d N L r) _ _ (fun _ => rfl)
  · simp only [Fintype.sum_prod_type, PiLp.inner_apply, residualPrefixFiber]
    exact Finset.sum_comm

/-- The inner product of two correlated residual vectors is the sum of
prefix boundary-map inner products, with the original tail retained in each
virtual boundary. This exact identity includes zero prefix and tail lengths.
It requires no letter intertwining or normalization.
Source: the residual coordinate decomposition of DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451, and
Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint, lines 1744--1820. -/
theorem inner_blockedResidualBoundaryMapES_eq_sum_groundSpaceMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ)
    (Y Z : Matrix (Fin D) (Fin E) ℂ) :
    ⟪blockedResidualBoundaryMapES A L B V N r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y),
      blockedResidualBoundaryMapES A L B V N r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Z)⟫_ℂ =
      ∑ τ : Cfg d r,
        ⟪groundSpaceMapES B N (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (Vᴴ * Kraus.evalWord A (List.ofFn τ) * Y)),
          groundSpaceMapES B N (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (Vᴴ * Kraus.evalWord A (List.ofFn τ) * Z))⟫_ℂ := by
  simpa only [residualPrefixFiber_boundaryMap] using
    inner_eq_sum_residualPrefixFiber (L := L)
      (blockedResidualBoundaryMapES A L B V N r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y))
      (blockedResidualBoundaryMapES A L B V N r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Z))

private theorem sum_norm_sq_residualPrefixFiber {N r : ℕ}
    (x : EuclideanSpace ℂ (Cfg d (N * L + r))) :
    ∑ τ : Cfg d r, ‖residualPrefixFiber (L := L) x τ‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [map_sum, ← norm_sq_eq_re_inner] using
    (congrArg (RCLike.re : ℂ →+ ℝ) (inner_eq_sum_residualPrefixFiber (L := L) x x)).symm

private theorem norm_inner_le_of_residualPrefixFiber_bound {N r : ℕ}
    (x y : EuclideanSpace ℂ (Cfg d (N * L + r))) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ τ : Cfg d r,
      ‖⟪residualPrefixFiber (L := L) x τ, residualPrefixFiber (L := L) y τ⟫_ℂ‖ ≤
        ε * ‖residualPrefixFiber (L := L) x τ‖ * ‖residualPrefixFiber (L := L) y τ‖) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  rw [inner_eq_sum_residualPrefixFiber (L := L) x y]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun τ _ => h τ)).trans ?_)
  simp only [mul_assoc, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hε
  simpa only [sum_norm_sq_residualPrefixFiber, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun τ => ‖residualPrefixFiber (L := L) x τ‖)
      (fun τ => ‖residualPrefixFiber (L := L) y τ‖)

private theorem residualPrefixFiber_mem_groundSpaceES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) {N r : ℕ}
    {x : EuclideanSpace ℂ (Cfg d (N * L + r))}
    (hx : x ∈ (blockedResidualBoundaryMapES A L B V N r).range) (τ : Cfg d r) :
    residualPrefixFiber (L := L) x τ ∈ groundSpaceES B N := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective z
  change residualPrefixFiber (L := L)
    (blockedResidualBoundaryMapES A L B V N r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)) τ ∈ groundSpaceES B N
  rw [residualPrefixFiber_boundaryMap A B V N r Y τ, ← range_groundSpaceMapES]
  exact ⟨_, rfl⟩

/-- A prefix-space angle bound controls the correlated residual boundary
ranges with the same coefficient, uniformly in the original tail length.
No normalization, injectivity, or letter intertwining is assumed.
Source: the fiberwise consequence of Nachtergaele,
arXiv:cond-mat/9410110, Lemma disjoint, lines 1744--1820, in the residual
coordinates of DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary. -/
theorem norm_inner_blockedResidualBoundaryMapES_le_of_prefix_bound {D₂ : ℕ}
    (A : MPSTensor d D) (C : MPSTensor d D₂)
    (B : MPSTensor (blockPhysDim d L) E) (B' : MPSTensor (blockPhysDim d L) F)
    (V : Matrix (Fin D) (Fin E) ℂ) (W : Matrix (Fin D₂) (Fin F) ℂ)
    {N r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hAngle : ∀ x ∈ groundSpaceES B N, ∀ y ∈ groundSpaceES B' N,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    {x y : EuclideanSpace ℂ (Cfg d (N * L + r))}
    (hx : x ∈ (blockedResidualBoundaryMapES A L B V N r).range)
    (hy : y ∈ (blockedResidualBoundaryMapES C L B' W N r).range) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  apply norm_inner_le_of_residualPrefixFiber_bound x y hε
  exact fun τ => hAngle _ (residualPrefixFiber_mem_groundSpaceES A B V hx τ)
    _ (residualPrefixFiber_mem_groundSpaceES C B' W hy τ)

/-- Inequivalent normalized primitive prefixes have asymptotically
orthogonal correlated residual ranges, uniformly over every original tail
length. The original tensors supplying the tail need no normalization.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint,
lines 1744--1820, followed by the exact fiberwise residual bound. -/
theorem IsPrimitiveMPS.eventually_norm_inner_blockedResidualBoundaryMapES_le_of_inequivalent
    [NeZero E] [NeZero F] {D₂ : ℕ}
    (A : MPSTensor d D) (C : MPSTensor d D₂)
    {B : MPSTensor (blockPhysDim d L) E} {B' : MPSTensor (blockPhysDim d L) F}
    (V : Matrix (Fin D) (Fin E) ℂ) (W : Matrix (Fin D₂) (Fin F) ℂ)
    {ρ : Matrix (Fin E) (Fin E) ℂ} {σ : Matrix (Fin F) (Fin F) ℂ}
    (hB : IsPrimitiveMPS B ρ) (hB' : IsPrimitiveMPS B' σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ e : F = E, ¬ GaugePhaseEquiv (e ▸ B') B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop, ∀ r,
      ∀ x ∈ (blockedResidualBoundaryMapES A L B V N r).range,
      ∀ y ∈ (blockedResidualBoundaryMapES C L B' W N r).range,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  filter_upwards [hB.eventually_norm_inner_groundSpaceES_le_of_inequivalent
    hB' hρ hσ hDistinct hε] with N hN
  exact fun r x hx y hy =>
    norm_inner_blockedResidualBoundaryMapES_le_of_prefix_bound A C B B' V W hε.le hN hx hy

/-- For a finite inequivalent primitive prefix family, the sum of the
correlated residual-sector projections approaches the projection onto their
joint range when the prefix length tends to infinity. The tail length may
vary arbitrarily along the filter.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (i),
lines 2442--2531, applied to the residual overlap estimate. -/
theorem tendsto_norm_residual_sector_projection_sum_sub_iSup_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    {κ : Type*} {f : Filter κ} {N r : κ → ℕ} (hN : Filter.Tendsto N f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(∑ j, ((blockedResidualBoundaryMapES A L (B j) (V j) (N n) (r n)).range).starProjection) -
        (⨆ j, (blockedResidualBoundaryMapES A L (B j) (V j) (N n) (r n)).range).starProjection‖)
      f (nhds 0) := by
  apply Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero
    (E := fun n => EuclideanSpace ℂ (Cfg d (N n * L + r n)))
  intro ε hε
  filter_upwards [hN.eventually (Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun hij =>
      (hP i).eventually_norm_inner_blockedResidualBoundaryMapES_le_of_inequivalent
        A A (V i) (V j) (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε)] with n hn
  exact fun i j hij => hn i j hij (r n)

end MPSTensor
