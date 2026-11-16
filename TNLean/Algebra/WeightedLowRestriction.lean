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

/-!
# Regional truncation error from a conjugation bound

Let `A` be Hermitian, let `X` commute with `A` and dominate `u` times its
spectral projection above `r + u`, and let `Y` be any further operator. If
imaginary-time conjugation of `Y` by `exp(s (A - (r + u)))` has norm at most
`C < u - e`, the weighted projection restricted to the spectral span of
`X + Y` at energies at most `e` has norm at most `C / (u - e - C)`. The
discrepancy of clipping `A` at `r + t` is then exponentially small in `t - u`
on that span.

The locality of the interaction enters only through the conjugation bound. It is
proved separately for nearest-neighbour chains and for interactions of bounded
support and degree.

Source: Arad, Kuwahara and Landau, arXiv:1406.3898, Theorem `lowspec`,
`low70.tex`, lines 1102–1168, as used by ALVV, arXiv:1602.08828v2,
Proposition 4.4, `local_alg_arxiv_v2.tex`, lines 894–921.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- From a conjugation bound on `Y`, the actual exponential weight of `A` has a
small restriction from the low spectral span of `X + Y` to the high spectral
range of `A`. All commutations, range memberships and quadratic bounds are
derived. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168. -/
theorem exists_weighted_low_restriction_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (r u e s C : ℝ) (hs0 : 0 < s)
    (hXA : Commute X A)
    (horder : u • spectralProjectionGE A (r + u) ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - (r + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    let Q := spectralProjectionGE A (r + u)
    let W := NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ)))
    let T := toEuclideanCLM (n := n) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    let U := (T Q).range
    ∃ Z : G →L[ℂ] U,
      U.subtypeL ∘L Z = (T W * T Q).domRestrict G ∧
      ‖Z‖ ≤ C / (u - e - C) := by
  intro Q W T G U
  let Winv := NormedSpace.exp (-(s • (A - (r + u) •
    (1 : Matrix n n ℂ))))
  let R := G.starProjection
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
  let Pkg : Submodule ℂ (EuclideanSpace ℂ (n)) → Prop := fun S ↦
      ∃ (B : S →L[ℂ] S) (XU : U →L[ℂ] U) (Z : S →L[ℂ] U)
          (V : U →L[ℂ] U) (F : S →L[ℂ] U),
        S.subtypeL ∘L B = (T X + T Y).domRestrict S ∧
        U.subtypeL ∘L XU = (T X).domRestrict U ∧
        U.subtypeL ∘L Z = (T W * T Q).domRestrict S ∧
        U.subtypeL ∘L V = (T Q * T W * T Y * T Winv * T Q).domRestrict U ∧
        U.subtypeL ∘L F = (T W * T Q * T Y * (1 - T Q)).domRestrict S ∧
        XU ∘L Z - Z ∘L B = -(V ∘L Z) - F
  have hRrange :
      (R : EuclideanSpace ℂ (n) →ₗ[ℂ]
        EuclideanSpace ℂ (n)).range = G := by
    change G.starProjection.range = G
    exact Submodule.range_starProjection G
  have hrestr0 : Pkg ((R : EuclideanSpace ℂ (n) →ₗ[ℂ]
      EuclideanSpace ℂ (n)).range) :=
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
    have hpoint := congrArg (fun f : U →L[ℂ] EuclideanSpace ℂ (n) ↦ f y)
      (hXU0.trans hXU.symm)
    change (XU0 y : EuclideanSpace ℂ (n)) = (XU y : _) at hpoint
    have hl := hLower0 y
    change u * ‖(y : EuclideanSpace ℂ (n))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (n))
        (XU0 y : EuclideanSpace ℂ (n))).re at hl
    change u * ‖(y : EuclideanSpace ℂ (n))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (n))
        (XU y : EuclideanSpace ℂ (n))).re
    rw [hpoint] at hl
    exact hl
  have hUpper : ∀ x : G, (inner ℂ x (B x)).re ≤ e * ‖x‖ ^ 2 := by
    intro x
    have hpoint := congrArg (fun f : G →L[ℂ] EuclideanSpace ℂ (n) ↦ f x) hB
    change (B x : EuclideanSpace ℂ (n)) =
      (T X + T Y) (x : EuclideanSpace ℂ (n)) at hpoint
    change (inner ℂ (x : EuclideanSpace ℂ (n))
      (B x : EuclideanSpace ℂ (n))).re ≤
        e * ‖(x : EuclideanSpace ℂ (n))‖ ^ 2
    rw [hpoint]
    have hxG : (x : EuclideanSpace ℂ (n)) ∈
        Submodule.spectralSpanLE b a e := x.property
    exact Submodule.re_inner_apply_le_of_mem_spectralSpanLE
      (E := EuclideanSpace ℂ (n)) (n := n)
      b a (T X + T Y).toLinearMap hEigenT e
      (x := (x : EuclideanSpace ℂ (n))) hxG
  have hlow : ‖W * (1 - Q)‖ ≤ 1 :=
    hA.norm_exp_mul_sub_const_mul_lowProjection_le_one s (r + u) hs0.le
  have hBoundary : ‖Q * W * Y * Winv * Q‖ ≤ C ∧ ‖W * Q * Y * (1 - Q)‖ ≤ C := by
    refine ⟨(norm_projection_conjugated_mul_projection_le Q W Y Winv hQmat).trans hconj, ?_⟩
    calc
      ‖W * Q * Y * (1 - Q)‖ ≤ ‖W * Y * Winv‖ * ‖W * (1 - Q)‖ :=
        norm_weighted_projection_forcing_le Q W Y Winv hQmat hWQ hInv
      _ ≤ C * 1 := mul_le_mul hconj hlow (norm_nonneg _) ((norm_nonneg _).trans hconj)
      _ = C := mul_one _
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

/-- From a conjugation bound on `Y`, clipping `A` at `r + t` changes it by at
most `exp(-s (t - u) - 1) / s · C / (u - e - C)` on the low spectral span of
`X + Y`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168. -/
theorem norm_truncation_excess_low_le_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (r u e s t C : ℝ) (hs0 : 0 < s)
    (hut : u ≤ t) (hXA : Commute X A)
    (horder : u • spectralProjectionGE A (r + u) ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - (r + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A - cfc (fun x : ℝ ↦ min x (r + t)) A)).domRestrict
      (Submodule.spectralSpanLE b a e)‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) * (C / (u - e - C)) := by
  obtain ⟨Z, hZ, hZnorm⟩ := exists_weighted_low_restriction_of_conjugation_le
    A X Y hA r u e s C hs0 hXA horder b a hEigen hconj hgap
  have hcut : r + u ≤ r + t := add_le_add le_rfl hut
  have htail := hA.norm_excess_domRestrict_le_actual_weighted_map
    s (r + t) (r + u) hs0 hcut Z hZ
  have hcoef : 0 ≤ Real.exp (-s * ((r + t) - (r + u)) - 1) / s :=
    div_nonneg (Real.exp_nonneg _) hs0.le
  have hfinal := htail.trans (mul_le_mul_of_nonneg_left hZnorm hcoef)
  have hdiff : (r + t) - (r + u) = t - u := by ring
  simpa only [hdiff] using hfinal

/-- For pairwise commuting Hermitian regional operators with attained lower
bounds, clipping one of them changes the centered partially clipped sum plus `Y`
by an exponentially small amount on its own low spectral span, given a
conjugation bound on `Y`. Commutation and the high-energy lower order are
derived. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168; ALVV,
arXiv:1602.08828v2, Proposition 4.4, lines 894–921. -/
theorem norm_partially_clipped_truncation_low_le
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : m → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j ↦ Commute (A i) (A j))
    (e : m → ℝ) (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (T : Finset m) (j : m) (Y : Matrix n n ℂ) (u ε s t C : ℝ)
    (hs0 : 0 < s) (hu : 0 ≤ u) (hut : u ≤ t)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ v, toEuclideanCLM (n := n) (𝕜 := ℂ)
      ((∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i) else A i) -
        (e i : ℂ) • (1 : Matrix n n ℂ))) + Y) (b v) = (a v : ℂ) • b v)
    (hconj : ‖NormedSpace.exp (s • (A j - (e j + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A j - (e j + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - ε) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict
      (Submodule.spectralSpanLE b a ε)‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) * (C / (u - ε - C)) :=
  norm_truncation_excess_low_le_of_conjugation_le (A j) _ Y (hA j) (e j) u ε s t C hs0 hut
    (commute_centered_partially_clipped_sum A e t T hcomm j)
    (spectralProjectionGE_le_centered_partially_clipped_sum A e t u T hA he hu hut j)
    b a hEigen hconj hgap

end Matrix
