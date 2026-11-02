/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ChebyshevWordPower
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.ViableSubspaceBootstrap
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PolynomialFilterParameters

/-!
# Actual operator-word powers at independent physical scales

The actual clipped polynomial family is applied to the physical low cluster
with independent threshold and window scales. The numerical filter condition
is explicit; spectral bases, supported tensor factors and the original ground
space are constructed from the nearest-neighbour terms. This supports ALVV,
arXiv:1602.08828v2, Corollary 4.6 and Theorem 4.9, source line 1080.

**Local fix (closed spectral cutoffs):** The full original ground space is
retained as documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Actual ordered words in the fixed long-interval polynomial family improve every viable subspace
for the same target at every power, independently of the input space.
The threshold and window scales are independent. The scalar filter
bound is a numerical condition; no rank, overlap, tensor or spectral-basis
hypothesis is supplied. Auxiliary to ALVV, arXiv:1602.08828v2,
Corollary 4.6 and the proof of Theorem 4.9, source line 1080. -/
theorem exists_independent_long_middle_actual_dg_word_family :
    ∀ (m q ell : ℕ) (t g epsilon Delta : ℝ), 2 ≤ q → q ≤ m →
      1 ≤ ell → 21 ≤ t → 0 < g → g ≤ 1 → 0 < epsilon → epsilon ≤ 1 →
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
        epsilon * g / 1000000 →
      (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
      ∀ (L p r : ℕ), p ≤ r → r ≤ L → 4 * ell < r - p →
      let Jtarget := interval L p r
      let β := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv β Jtarget).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtargetᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtarget) ℂ)).repr
      let Tcoord := U.trans Phi.symm
      let Tm := Tcoord.trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtargetᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtarget)))
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      mu ∈ spectrum ℝ H →
      (∀ x ∈ spectrum ℝ H, x = mu ∨ mu + g ≤ x) →
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (N : ℕ)
        (F : Fin N → EuclideanSpace ℂ (Jtarget → Fin q) →L[ℂ]
          EuclideanSpace ℂ (Jtarget → Fin q)),
        N ≤ D ^ 2 ∧
        Submodule.IsCloseTo (epsilon / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (epsilon / 200 : ℝ) G T ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        ∀ (power : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q))) (δ : ℝ),
          Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
            (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)) δ S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) → δ < 1 →
          let grow := ⨆ w : Fin power → Fin N,
            S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
              (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q))
              (Delta ^ power / (1 - δ) ^ 2) grow
              (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                  EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) := by
  classical
  intro m q ell t g epsilon Delta hq hqm hell ht hg hg1 hepsilon hepsilon1 htail hfilter
    D L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm h hs h0 h1 mu H hH G hmu hgap
  let a := max p ell - ell
  let b := min r (L - ell) - ell - 1
  obtain ⟨_haEnd, _hbEnd, hab, hb, _hpp, _hpq, _hqq, _hlen,
    _hleft, _hright, _htotal, hsub, hcollar⟩ :=
    inward_effective_cuts L ell p r hell hpr hrL hlong
  obtain ⟨e, E0, _hground, _horigin, hE0, hE4, hnorm,
    v, lam, heigen, hclosed, _hband, hdim, hTG, hGT, _hnewgap⟩ :=
    exists_five_region_physical_scaled_low_cluster L q a b ell t
      (by omega) hell ht
      (hab.trans (Nat.le_succ b)) (hb.trans (Nat.sub_le L 1))
      h hs h0 h1 mu g (epsilon * g / 1000000) epsilon hg hg1 hepsilon hepsilon1
      htail le_rfl hmu hgap
  let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
  let Areg : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
    ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
  let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
    (fun i ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
  let Y := ∑ i ∈ Cross, h i
  let K : Finset (Fin 5) := {0, 2, 4}
  let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    (∑ j, ((if j ∈ K then
      cfc (fun x : ℝ ↦ min x (e j + t)) (Areg j) else Areg j) -
        (e j : ℂ) • 1)) + Y
  let eta0 := E0 + g / 10
  let eta1 := E0 + 9 * g / 10
  let upper := 3 * t + 4 * (ell : ℝ)
  let T := Submodule.spectralSpanLE v lam eta0
  have hellR : 1 ≤ (ell : ℝ) := by exact_mod_cast hell
  have hsep : eta0 < eta1 := by dsimp only [eta0, eta1]; linarith only [hg]
  have hendpoint : eta1 ≤ upper := by
    dsimp only [eta1, upper]
    linarith only [hE4, hg1, ht, hellR]
  have hR0 : 0 < upper - eta0 := by
    dsimp only [eta0, upper]
    linarith only [hE4, hg1, ht, hellR]
  have hRbudget : upper - eta0 ≤ 3 * t + 4 * (ell : ℝ) := by
    dsimp only [eta0, upper]
    linarith only [hE0, hg]
  have hwidth : eta1 - eta0 = 4 * g / 5 := by dsimp only [eta0, eta1]; ring
  have hcontract := hfilter (upper - eta0) hR0 hRbudget
  rw [← hwidth] at hcontract
  have hB : B.IsHermitian :=
    Matrix.isHermitian_sum_centered_partial_energyTruncation Areg
      (fun _ ↦ (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian)
      K e (fun j ↦ e j + t) _
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hdegree : 1 ≤ ell ^ 2 := by
    rw [pow_two]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hell hell
  let J0 := interval L (a + ell) (b + ell + 1)
  let D0 := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
  obtain ⟨N, W, hNraw, hdecomp⟩ :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hb h hs e t Jtarget
  change N ≤ D0 ^ 2 * q ^
    (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) at hNraw
  have hN : N ≤ D ^ 2 := by
    have hN' : N ≤ D0 ^ 2 * q ^ (2 * (Jtarget \ J0).card) := by
      simpa only [Finset.sdiff_eq_empty_iff_subset.mpr hsub,
        Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hNraw
    exact hN'.trans (collar_card_le_square_of_larger_count_base
      q m ell (Jtarget \ J0).card (D0 ^ 2) hq hqm hell hcollar le_rfl)
  have hcheb := Matrix.chebyshev_word_power_viability_of_actual_cluster_polynomial_family
    B hB v lam heigen W Tm (fun Q hQ ↦ (hdecomp Q hQ).imp fun _ hM ↦ hM.2)
    (D ^ 2) hN eta0 eta1 upper hsep hendpoint hclosed hnorm
  let CW := fun i : Fin N ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
    (n := Jtarget → Fin q) (W i)
  refine ⟨T, N, CW, hN, hTG, hGT, hdim, ?_⟩
  intro power S δ hS hδ grow
  obtain ⟨hdimension, hviable⟩ := hcheb power S δ hS hδ
  refine ⟨hdimension, ?_⟩
  have hcontract' :
      (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2 ≤ Delta := by
    simpa only [Nat.cast_pow] using hcontract
  exact Submodule.IsCloseTo.of_le hviable
    (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sq_nonneg _) hcontract' power) (sq_nonneg _))
end TNLean.MPS.AreaLaw
