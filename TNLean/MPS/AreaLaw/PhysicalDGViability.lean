/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.ViableSubspaceCoordinates
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.ShortRegionViableFamily

/-!
# A common viable-space enlargement for a gapped chain

For an actual nearest-neighbour Hamiltonian, a universal scalar choice gives a fixed operator
family on any prescribed interval. The target is mutually close to the full original ground
space, and the family improves every viable subspace with error below one. Long intervals use
a clipped spectral cluster; short intervals use configuration matrix units.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Long-middle existence of a common viable-space enlargement for an actual
nearest-neighbour Hamiltonian. One universal parameter precedes the local
dimension, normalized gap, chain and original bonds. The target interval may
meet either chain endpoint. Its inward effective cuts, central trace core,
regional energies, spectral cluster, polynomial decomposition and operator
count are derived internally. Auxiliary long-middle case of ALVV,
arXiv:1602.08828v2, Assumption (DG), lines 267–280, and Theorem `t:ais`,
lines 1010–1024. This auxiliary has `0 < g ≤ 1` and middle length `> 4 ell`;
it does not assert the arbitrary-gap or short-middle conclusion, an efficient
central bond, or a running-time estimate. -/
private theorem exists_long_middle_actual_dg_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (q : ℕ) (g : ℝ), 2 ≤ q → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      21 ≤ ell ∧ 2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
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
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ)
        (F : Fin (D ^ 2) → EuclideanSpace ℂ (Jtarget → Fin q) →L[ℂ]
          EuclideanSpace ℂ (Jtarget → Fin q)),
        Submodule.IsCloseTo (1 / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (1 / 200 : ℝ) G T ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q))) (δ : ℝ),
          Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
            (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)) δ S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) → δ < 1 →
          let grow := ⨆ i : Fin (D ^ 2), S.map (F i : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
              (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q))
              (Delta / (1 - δ) ^ 2) grow
              (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                  EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) := by
  classical
  obtain ⟨A, hA, hA21, hall⟩ := exists_five_region_dg_cluster_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro q g hq hg hg1 u ell D cA
  obtain ⟨hell, hD, hlogD, hphysical⟩ := hall q g hq hg hg1
  refine ⟨hell, hD, hlogD, ?_⟩
  intro L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm h hs h0 h1 mu H hH G hmu hgap
  have hell1 : 1 ≤ ell := Nat.le_trans (by decide : 1 ≤ 21) hell
  let a := max p ell - ell
  let b := min r (L - ell) - ell - 1
  obtain ⟨_haEnd, _hbEnd, hab, hb, _hpp, _hpq, _hqq, _hlen,
    _hleft, _hright, _htotal, hsub, hcollar⟩ :=
    inward_effective_cuts L ell p r hell1 hpr hrL hlong
  obtain ⟨e, E0, _hground, _horigin, _hE0, _hE4, hnorm, hsep, hendpoint,
    _hR0, _hR8, hDelta0, hsmall, v, lam, heigen, hclosed,
    _hband, _hdim, hTG, hGT, _hnewgap⟩ :=
    hphysical L a b (hab.trans (Nat.le_succ b)) (hb.trans (Nat.sub_le L 1))
      h hs h0 h1 mu hmu hgap
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
      cfc (fun x : ℝ ↦ min x (e j + (ell : ℝ))) (Areg j) else Areg j) -
        (e j : ℂ) • 1)) + Y
  let eta0 := E0 + g / 10
  let eta1 := E0 + 9 * g / 10
  let upper := 7 * (ell : ℝ)
  let Delta : ℝ := (2 * Real.exp
    (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
  let T := Submodule.spectralSpanLE v lam eta0
  have hB : B.IsHermitian := by
    have hterm (j : Fin 5) : IsSelfAdjoint
        ((if j ∈ K then
          cfc (fun x : ℝ ↦ min x (e j + (ell : ℝ))) (Areg j) else Areg j) -
            (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) := by
      apply IsSelfAdjoint.sub
      · split_ifs
        · exact IsSelfAdjoint.cfc
        · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)
      · exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (by simp [IsSelfAdjoint])
    exact ((isSelfAdjoint_sum Finset.univ fun j _ ↦ hterm j).add
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i))).isHermitian
  have hdegree : 1 ≤ ell ^ 2 := by
    rw [pow_two]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hell1 hell1
  let J0 := interval L (a + ell) (b + ell + 1)
  let D0 := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
  obtain ⟨N, W, hNraw, hdecomp⟩ :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell1 hq hdegree hab hb h hs e (ell : ℝ) Jtarget
  change N ≤ D0 ^ 2 * q ^
    (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) at hNraw
  have hdiff : J0 \ Jtarget = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hN : N ≤ D ^ 2 := by
    have hN' : N ≤ D0 ^ 2 * q ^ (2 * (Jtarget \ J0).card) := by
      simpa only [hdiff, Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hNraw
    exact hN'.trans (collar_card_le_square_at_square_degree
      q ell (Jtarget \ J0).card (D0 ^ 2) hq hell1 hcollar le_rfl)
  have hcheb := Matrix.chebyshev_viability_of_actual_cluster_polynomial_family
    B hB v lam heigen W Tm (by
      intro Q hQ
      obtain ⟨M, _hmatrix, hconj⟩ := hdecomp Q hQ
      exact ⟨M, hconj⟩)
    (D ^ 2) hN eta0 eta1 upper hsep hendpoint hclosed hnorm
  let CW := fun i : Fin N ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
    (n := Jtarget → Fin q) (W i)
  obtain ⟨_f, F, _hF, _hzero, hspan⟩ :=
    Submodule.exists_clm_family_extension_of_card_le
      (by simpa only [Fintype.card_fin] using hN) CW
  refine ⟨T, Delta, F, hTG, hGT, hDelta0, hsmall, ?_⟩
  intro S δ hS hδ grow
  obtain ⟨hdimension, hviable⟩ := hcheb S δ hS hδ
  constructor
  · change Module.finrank ℂ
        (↥((⨆ i : Fin (D ^ 2), S.map ((F i).toLinearMap)) :
          Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q)))) ≤
      D ^ 2 * Module.finrank ℂ S
    rw [hspan S]
    exact hdimension
  · change Submodule.IsViable (𝕜 := ℂ)
      (E := EuclideanSpace ℂ (Jtarget → Fin q))
      (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q))
      (Delta / (1 - δ) ^ 2)
      ((⨆ i : Fin (D ^ 2), S.map ((F i).toLinearMap)) :
        Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q)))
      (T.map Tm.toLinearEquiv.toLinearMap)
    rw [hspan S]
    simpa only [Nat.cast_pow] using hviable
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A fixed family on any prescribed middle interval improves viability
for a subspace mutually close to the full original ground space. The scalar
constant is chosen before every chain, Hamiltonian, gap and interval.
A ground spectral value and any strictly higher spectral value are supplied by ALVV,
arXiv:1602.08828v2, Assumption (DG), lines 273–280; the conclusion is the
operator-family assertion of Theorem `t:ais`, lines 1010–1024, with an
explicit logarithmic bound. The gap is normalized internally by its minimum
with one. No upper bound on the original gap, on-site dimension condition,
trace core, canonical spectral basis or boundary margin is assumed.

**Local fix (ground-space cutoff and viability boundary):** The original
comparison space is the full ground space, following the proof of `t:ais`,
line 1020. Its statement at line 1012 prints an extra ground-energy shift.
The improvement formula is used for viability error below one. Both readings
are documented in the companion note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
This assertion concerns existence and the viability estimate; the efficient
MPO construction is a separate result of the source. -/
theorem exists_physical_dg_viable_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ (W : Fin (D ^ 2) → EM →L[ℂ] EM)
        (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (1 / 200 : ℝ) G T ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ (S : Submodule ℂ EM) (delta : ℝ),
          Submodule.IsViable (F := EE) delta S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) → delta < 1 →
          Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ (2 : ℕ))
            (⨆ j, S.map (W j : EM →ₗ[ℂ] EM))
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hall⟩ := exists_long_middle_actual_dg_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hggamma : g ≤ gamma := min_le_left gamma 1
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    rcases hgap z hz with hzmu | hzlower
    · exact Or.inl hzmu
    · exact Or.inr (by linarith only [hggamma, hzlower])
  obtain ⟨hell, _hD, hlogD, hlong⟩ := hall q g hq hg hg1
  refine ⟨hlogD, ?_⟩
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell :=
      (card_interval_le (L := L) p r).trans hshort
    obtain ⟨W, Delta, hDelta, hbudget, himprove⟩ :=
      exists_short_actual_region_improving_family (F := EE) L q ell J hq
        (Nat.le_trans (by decide : 1 ≤ 21) hell) hJ
    have hGG : Submodule.IsCloseTo (1 / 200 : ℝ) G G := by
      apply Submodule.isCloseTo_iff.mpr
      intro x hx
      rw [G.starProjection_eq_self_iff.mpr hx]
      nlinarith [sq_nonneg ‖x‖]
    refine ⟨W, G, Delta, hGG, hGG, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact himprove (G.map (Tm.toLinearEquiv :
      EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] (EM ⊗[ℂ] EE))) S delta hS hdelta
  · obtain ⟨T, Delta, W, hTG, hGT, hDelta, hbudget, himprove⟩ :=
      hlong L p r hpr hrL (Nat.lt_of_not_ge hshort) h hs h0 h1 mu hmu hgapg
    refine ⟨W, T, Delta, hTG, hGT, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact (himprove S delta hS hdelta).2
end TNLean.MPS.AreaLaw
end
