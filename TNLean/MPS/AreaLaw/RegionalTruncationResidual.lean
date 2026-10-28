/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.SeparatedQuadraticForms
import QICLean.Analysis.SpectralExponentialWeights
import QICLean.Analysis.WeightedProjection
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.NearestNeighbourImaginaryTime

/-!
# Residual estimates for regional energy truncation

The original nearest-neighbour bond sum supplies boundary exponential estimates. Restricting
the actual weighted projection gives a Sylvester equation between spectral subspaces. Its norm
bound controls the regional truncation excess on the specified low-energy space.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

section

section

section

section

section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open scoped Matrix.Norms.L2Operator

open scoped Matrix.Norms.L2Operator

open scoped BigOperators

namespace TNLean.MPS.AreaLaw

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The sum of supplied original nearest-neighbour boundary bonds has
short-time conjugation norm at most twice their number, even after a scalar
energy shift. Supporting AKL14, arXiv:1406.3898, low70.tex, lines 817–877.
No conjugation or residual estimate is supplied as a hypothesis. -/
private theorem norm_exp_conjugation_nearestNeighbour_boundary_sum_le
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ I, h i
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * (∑ j ∈ J, h j) *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * (J.card : ℝ) := by
  intro H
  have hsI : ∀ i ∈ I, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)) :=
    fun i hi ↦ hs i (Finset.mem_union_left J hi)
  have h0I : ∀ i ∈ I, 0 ≤ h i := fun i hi ↦ h0 i (Finset.mem_union_left J hi)
  have h1I : ∀ i ∈ I, h i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_union_left J hi)
  have hnorm1 : ‖(1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _
      (IsStarProjection.one (Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  have hterm (j : Fin (L - 1)) (hj : j ∈ J) :
      ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
        NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 := by
    have hjunion : j ∈ I ∪ J := Finset.mem_union_right I hj
    have hjnorm : ‖h j‖ ≤ 1 :=
      (CStarAlgebra.norm_le_norm_of_le_of_nonneg (h1 j hjunion) (h0 j hjunion)).trans
        hnorm1
    calc
      ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
          NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖h j‖ :=
        norm_exp_conjugation_nearest_neighbour_shift_le_two (c := j.val)
          I h hsI h0I h1I (h j) (hs j hjunion) z t ht0 ht
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hjnorm (by norm_num)
      _ = 2 := mul_one 2
  calc
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * (∑ j ∈ J, h j) *
        NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ =
        ‖∑ j ∈ J, NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
          NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ j ∈ J, ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
        NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, (2 : ℝ) := Finset.sum_le_sum hterm
    _ = (J.card : ℝ) * 2 := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (J.card : ℝ) := mul_comm _ _
end TNLean.MPS.AreaLaw

open scoped Matrix.Norms.L2Operator

open scoped Matrix.Norms.L2Operator

open scoped Matrix.Norms.L2Operator

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The actual high-energy compression and forcing term are bounded by twice
the number of original boundary bonds for times between zero and one eighth.
Auxiliary to the weighted truncation argument for ALVV,
arXiv:1602.08828v2, Theorem t:ais, lines 1010–1024, and AKL14,
arXiv:1406.3898, low70.tex, lines 817–877.
All norm, projection and weight relations are derived from the local bonds. -/
private theorem nearestNeighbour_boundary_weight_norms_le
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (c s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) :
    let A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ I, h i
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ j ∈ J, h j
    let W := NormedSpace.exp (s • (A - c • (1 : Matrix (Fin L → Fin q)
      (Fin L → Fin q) ℂ)))
    let Winv := NormedSpace.exp (-(s • (A - c • (1 : Matrix (Fin L → Fin q)
      (Fin L → Fin q) ℂ))))
    let Q := Matrix.spectralProjectionGE A c
    ‖Q * W * Y * Winv * Q‖ ≤ 2 * (J.card : ℝ) ∧
      ‖W * Q * Y * (1 - Q)‖ ≤ 2 * (J.card : ℝ) := by
  intro A Y W Winv Q
  have hAnonneg : 0 ≤ A :=
    Finset.sum_nonneg fun i hi ↦ h0 i (Finset.mem_union_left J hi)
  have hA : A.IsHermitian := (IsSelfAdjoint.of_nonneg hAnonneg).isHermitian
  have hQ : IsStarProjection Q := hA.isStarProjection_spectralProjectionGE c
  obtain ⟨hWQ, _hAW, _hAQ, hInv⟩ :=
    hA.regionalWeight_relations A (Commute.refl A) s c
  have hconj : ‖W * Y * Winv‖ ≤ 2 * (J.card : ℝ) := by
    simpa only [Complex.coe_smul] using
      (norm_exp_conjugation_nearestNeighbour_boundary_sum_le
        I J h hs h0 h1 (c : ℂ) s hs0 hs1)
  have hlow : ‖W * (1 - Q)‖ ≤ 1 :=
    hA.norm_exp_mul_sub_const_mul_lowProjection_le_one s c hs0
  refine ⟨(Matrix.norm_projection_conjugated_mul_projection_le Q W Y Winv hQ).trans
    hconj, ?_⟩
  calc
    ‖W * Q * Y * (1 - Q)‖ ≤ ‖W * Y * Winv‖ * ‖W * (1 - Q)‖ :=
      Matrix.norm_weighted_projection_forcing_le Q W Y Winv hQ hWQ hInv
    _ ≤ (2 * (J.card : ℝ)) * 1 :=
      mul_le_mul hconj hlow (norm_nonneg _) ((norm_nonneg _).trans hconj)
    _ = 2 * (J.card : ℝ) := mul_one _
end TNLean.MPS.AreaLaw
end

namespace TNLean.MPS.AreaLaw

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The actual exponential weight on the original regional sum has a small
restriction from the actual low spectral span to the original high projection
range. All commutations, range memberships, quadratic bounds and boundary norms
are derived. The structural commutation and matrix order must be established
from the spatial decomposition in a physical application.

This is an auxiliary weighted spectral estimate for ALVV,
arXiv:1602.08828v2, Theorem t:ais, lines 1010--1024, and AKL14,
arXiv:1406.3898, Theorem lowspec, lines 1102--1168. It is not the full physical
truncation-error or subspace-closeness theorem. -/
private theorem exists_nearestNeighbour_weighted_low_restriction
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (r u e s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8)
    (hXA : Commute X (∑ i ∈ I, h i))
    (horder : u • Matrix.spectralProjectionGE (∑ i ∈ I, h i) (r + u) ≤ X)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ
      (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ j, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + ∑ j ∈ J, h j) (b j) = (a j : ℂ) • b j)
    (hgap : 2 * (J.card : ℝ) < u - e) :
    let A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ I, h i
    let Q := Matrix.spectralProjectionGE A (r + u)
    let W := NormedSpace.exp (s • (A - (r + u) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)))
    let T := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    let U := (T Q).range
    ∃ Z : G →L[ℂ] U,
      U.subtypeL ∘L Z = (T W * T Q).domRestrict G ∧
      ‖Z‖ ≤ (2 * (J.card : ℝ)) / (u - e - 2 * (J.card : ℝ)) := by
  intro A Q W T G U
  let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ j ∈ J, h j
  let Winv := NormedSpace.exp (-(s • (A - (r + u) •
    (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))))
  let R := G.starProjection
  let C : ℝ := 2 * (J.card : ℝ)
  have hAnonneg : 0 ≤ A :=
    Finset.sum_nonneg fun i hi ↦ h0 i (Finset.mem_union_left J hi)
  have hA : A.IsHermitian := (IsSelfAdjoint.of_nonneg hAnonneg).isHermitian
  have hQmat : IsStarProjection Q := hA.isStarProjection_spectralProjectionGE (r + u)
  obtain ⟨hWQ, hXW, hXQ, hInv⟩ := hA.regionalWeight_relations X hXA s (r + u)
  have hWQT : Commute (T W) (T Q) := by
    change T W * T Q = T Q * T W
    simpa only [map_mul] using congrArg T hWQ.eq
  have hXWT : Commute (T X) (T W) := by
    change T X * T W = T W * T X
    simpa only [map_mul] using congrArg T hXW.eq
  have hXQT : Commute (T X) (T Q) := by
    change T X * T Q = T Q * T X
    simpa only [map_mul] using congrArg T hXQ.eq
  have hInvT : T Winv * T W = 1 := by
    simpa only [map_mul, map_one] using congrArg T hInv
  have hQT : IsIdempotentElem (T Q) := by
    change T Q * T Q = T Q
    simpa only [map_mul] using congrArg T hQmat.isIdempotentElem.eq
  have hRT : IsIdempotentElem R := G.isIdempotentElem_starProjection
  have hEigenT : ∀ j, (T X + T Y) (b j) = (a j : ℂ) • b j := by
    intro j
    simpa only [map_add] using hEigen j
  have hRH : Commute R (T X + T Y) :=
    Submodule.commute_starProjection_spectralSpanLE b a (T X + T Y) hEigenT e
  have hOrderT : (u : ℂ) • T Q ≤ T X := by
    have hm : (u : ℂ) • Q ≤ X := by simpa only [Complex.coe_smul] using horder
    have h := Matrix.toEuclideanCLM_le_of_le hm
    simpa only [map_smul] using h
  let Pkg : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) → Prop := fun S ↦
      ∃ (B : S →L[ℂ] S) (XU : U →L[ℂ] U) (Z : S →L[ℂ] U)
          (V : U →L[ℂ] U) (F : S →L[ℂ] U),
        S.subtypeL ∘L B = (T X + T Y).domRestrict S ∧
        U.subtypeL ∘L XU = (T X).domRestrict U ∧
        U.subtypeL ∘L Z = (T W * T Q).domRestrict S ∧
        U.subtypeL ∘L V = (T Q * T W * T Y * T Winv * T Q).domRestrict U ∧
        U.subtypeL ∘L F = (T W * T Q * T Y * (1 - T Q)).domRestrict S ∧
        XU ∘L Z - Z ∘L B = -(V ∘L Z) - F
  have hRrange :
      (R : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin L → Fin q)).range = G := by
    change G.starProjection.range = G
    exact Submodule.range_starProjection G
  have hrestr0 : Pkg ((R : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q)).range) :=
    ContinuousLinearMap.exists_restricted_weighted_sylvester
      (T X) (T Y) (T W) (T Winv) (T Q) R hQT hRT
      hWQT hXWT hXQT hRH hInvT
  have hrestr : Pkg G := Eq.mp (congrArg Pkg hRrange) hrestr0
  obtain ⟨B, XU, Z, V, F, hB, hXU, hZ, hV, hF, hEq⟩ := hrestr
  obtain ⟨XU0, hXU0, hLower0⟩ :=
    ContinuousLinearMap.exists_restrict_range_quadratic_lower
      (T Q) (T X) hQT hXQT u hOrderT
  have hLower : ∀ y : U, u * ‖y‖ ^ 2 ≤ (inner ℂ y (XU y)).re := by
    intro y
    have hpoint := congrArg (fun f : U →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) ↦ f y)
      (hXU0.trans hXU.symm)
    change (XU0 y : EuclideanSpace ℂ (Fin L → Fin q)) = (XU y : _) at hpoint
    have hl := hLower0 y
    change u * ‖(y : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (Fin L → Fin q))
        (XU0 y : EuclideanSpace ℂ (Fin L → Fin q))).re at hl
    change u * ‖(y : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (Fin L → Fin q))
        (XU y : EuclideanSpace ℂ (Fin L → Fin q))).re
    rw [hpoint] at hl
    exact hl
  have hUpper : ∀ x : G, (inner ℂ x (B x)).re ≤ e * ‖x‖ ^ 2 := by
    intro x
    have hpoint := congrArg (fun f : G →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) ↦ f x) hB
    change (B x : EuclideanSpace ℂ (Fin L → Fin q)) =
      (T X + T Y) (x : EuclideanSpace ℂ (Fin L → Fin q)) at hpoint
    change (inner ℂ (x : EuclideanSpace ℂ (Fin L → Fin q))
      (B x : EuclideanSpace ℂ (Fin L → Fin q))).re ≤
        e * ‖(x : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2
    rw [hpoint]
    have hxG : (x : EuclideanSpace ℂ (Fin L → Fin q)) ∈
        Submodule.spectralSpanLE b a e := x.property
    exact Submodule.re_inner_apply_le_of_mem_spectralSpanLE
      (E := EuclideanSpace ℂ (Fin L → Fin q)) (n := Fin L → Fin q)
      b a (T X + T Y).toLinearMap hEigenT e
      (x := (x : EuclideanSpace ℂ (Fin L → Fin q))) hxG
  have hBoundary : ‖Q * W * Y * Winv * Q‖ ≤ C ∧
      ‖W * Q * Y * (1 - Q)‖ ≤ C :=
    nearestNeighbour_boundary_weight_norms_le (L := L) (q := q)
      I J h hs h0 h1 (r + u) s hs0.le hs1
  have hJnorm : ‖T Q * T W * T Y * T Winv * T Q‖ ≤ C := by
    have h : ‖T (Q * W * Y * Winv * Q)‖ ≤ C := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hBoundary.1
    simpa only [map_mul] using h
  have hLnorm : ‖T W * T Q * T Y * (1 - T Q)‖ ≤ C := by
    have h : ‖T (W * Q * Y * (1 - Q))‖ ≤ C := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hBoundary.2
    simpa only [map_mul, map_sub, map_one] using h
  have hVnorm : ‖V‖ ≤ C :=
    (ContinuousLinearMap.norm_le_of_subtypeL_comp_eq_domRestrict V
      (T Q * T W * T Y * T Winv * T Q) hV).trans hJnorm
  have hFnorm : ‖F‖ ≤ C :=
    (ContinuousLinearMap.norm_le_of_subtypeL_comp_eq_domRestrict F
      (T W * T Q * T Y * (1 - T Q)) hF).trans hLnorm
  have hFneg : ‖-F‖ ≤ C := by simpa only [norm_neg] using hFnorm
  have hEq' : XU ∘L Z - Z ∘L B = (-F) - V ∘L Z := by
    rw [hEq]
    abel
  have hnorm := ContinuousLinearMap.norm_le_div_of_sylvester_perturbation
    XU V B Z (-F) u e C C hLower hUpper hVnorm hFneg hgap hEq'
  exact ⟨Z, hZ, hnorm⟩
end TNLean.MPS.AreaLaw

section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual discrepancy of one regional clipping is small on the actual
low spectral span of the current Hamiltonian. The original positive unit
bonds supply every conjugation and forcing estimate. The structural
commutation and lower order are to be derived from the five-region
construction in the full physical theorem.

Auxiliary to AKL14, arXiv:1406.3898, Theorem lowspec, lines 1102–1168,
and ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem norm_nearestNeighbour_regional_truncation_low_le
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (r u e s t : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (hut : u ≤ t)
    (hXA : Commute X (∑ i ∈ I, h i))
    (horder : u • Matrix.spectralProjectionGE (∑ i ∈ I, h i) (r + u) ≤ X)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ
      (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ j, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + ∑ j ∈ J, h j) (b j) = (a j : ℂ) • b j)
    (hgap : 2 * (J.card : ℝ) < u - e) :
    let A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ I, h i
    let T := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    ‖(T (A - cfc (fun x : ℝ ↦ min x (r + t)) A)).domRestrict G‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) *
        ((2 * (J.card : ℝ)) / (u - e - 2 * (J.card : ℝ))) := by
  intro A T G
  obtain ⟨Z, hZ, hZnorm⟩ := exists_nearestNeighbour_weighted_low_restriction
    I J h hs h0 h1 X r u e s hs0 hs1 hXA horder b a hEigen hgap
  have hA : A.IsHermitian :=
    (isSelfAdjoint_sum I fun i hi ↦
      IsSelfAdjoint.of_nonneg (h0 i (Finset.mem_union_left J hi))).isHermitian
  have hcut : r + u ≤ r + t := add_le_add le_rfl hut
  have htail := hA.norm_excess_domRestrict_le_actual_weighted_map
    s (r + t) (r + u) hs0 hcut Z hZ
  have hcoef : 0 ≤ Real.exp (-s * ((r + t) - (r + u)) - 1) / s :=
    div_nonneg (Real.exp_nonneg _) hs0.le
  have hfinal := htail.trans (mul_le_mul_of_nonneg_left hZnorm hcoef)
  have hdiff : (r + t) - (r + u) = t - u := by ring
  simpa only [hdiff] using hfinal
end TNLean.MPS.AreaLaw
end
end

section

namespace TNLean.MPS.AreaLaw

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The single-region tail bound for a literal partially clipped consecutive
regional sum. Original bond supports imply commutation, and the original
regional lower bounds imply the required order. No current-commutation,
current-order or norm estimate is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
theorem norm_consecutive_regional_truncation_low_le
    {L q m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e : Fin m → ℝ) (T : Finset (Fin m)) (j : Fin m)
    (J : Finset (Fin (L - 1))) (u ε s t : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (hu : 0 ≤ u) (hut : u ≤ t)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ) :
    let A : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun i ↦
      ∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun r ↦ k i.castSucc ≤ r.val ∧ r.val + 1 < k i.succ), h r
    let X := ∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i)
      else A i) - (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a ε
    (∀ i, (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A i) →
    (∀ v, ι (X + ∑ r ∈ J, h r) (b v) = (a v : ℂ) • b v) →
    2 * (J.card : ℝ) < u - ε →
    ‖(ι (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) *
        ((2 * (J.card : ℝ)) / (u - ε - 2 * (J.card : ℝ))) := by
  intro A X ι G he hEigen hgap
  have hA (i : Fin m) : (A i).IsHermitian := by
    have hi : 0 ≤ A i := Finset.sum_nonneg fun r _ ↦ h0 r
    exact (IsSelfAdjoint.of_nonneg hi).isHermitian
  have hcomm : Pairwise fun i j : Fin m ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
  have hXA : Commute X (A j) :=
    Matrix.commute_centered_partially_clipped_sum A e t T hcomm j
  have horder : u • Matrix.spectralProjectionGE (A j) (e j + u) ≤ X :=
    Matrix.spectralProjectionGE_le_centered_partially_clipped_sum
      A e t u T hA he hu hut j
  exact norm_nearestNeighbour_regional_truncation_low_le
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun r ↦ k j.castSucc ≤ r.val ∧ r.val + 1 < k j.succ)) J h
    (fun r _ ↦ hs r) (fun r _ ↦ h0 r) (fun r _ ↦ h1 r)
    X (e j) u ε s t hs0 hs1 hut hXA horder b a hEigen hgap
end TNLean.MPS.AreaLaw
end
end
end
end
end
