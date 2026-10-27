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
import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ViableSubspaceDimension

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


section

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A gapped nearest-neighbour chain has a small viable subspace on every
interval, with the full ground-space dimension as a linear factor. The
improving family and sampling threshold are derived internally. This is
the interval form used at line 1080 in the area-law argument of ALVV,
arXiv:1602.08828v2, supporting Proposition `prop:albootstrap-dg`, lines 1062–1075.

**Scope restriction (contiguous regions):** The physical bootstrap statements
in this module concern intervals. The printed proposition permits arbitrary
subsets, whereas its proof invokes the contiguous-block family.
Disconnected regions do not satisfy the asserted uniform dimension bound,
as a product of adjacent Bell pairs shows. The interval statement suffices
for the area-law theorem. The scope and numerical corrections belong to
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
This theorem is not the unrestricted-subset proposition. -/
theorem exists_physical_interval_viable_subspace :
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
      ∃ W : Submodule ℂ EM,
        Module.finrank ℂ W < Module.finrank ℂ G * D ^ 24 ∧
        Submodule.IsViable (F := EE) 0.015 W
          (G.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
            (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hfamily⟩ := exists_physical_dg_viable_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  obtain ⟨hlogD, Fops, T, Delta, hTG, hGT, _hDelta0, hbudget, himprove⟩ :=
    hfamily L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hlogD, ?_⟩
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) hq)
  have hu1 : 1 ≤ u := by
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have hApos : 0 < A := by linarith only [hA]
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hellpos : 0 < ell := Nat.ceil_pos.mpr (by positivity)
  have hell1 : 1 ≤ ell := hellpos
  have hbase : 2 ≤ q * ell ^ 2 := by
    calc
      2 ≤ q := hq
      _ = q * 1 := (mul_one q).symm
      _ ≤ q * ell ^ 2 := Nat.mul_le_mul_left q (Left.one_le_pow_of_le hell1 2)
  have hD : 2 ≤ D := hbase.trans
    (le_self_pow (Nat.le_trans (by decide : 1 ≤ 2) hbase)
      (Nat.mul_ne_zero (by decide : (22 : ℕ) ≠ 0) hellpos.ne'))
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hdimT : Module.finrank ℂ T = Module.finrank ℂ G :=
    Nat.le_antisymm (hGT.finrank_le (by norm_num)) (hTG.finrank_le (by norm_num))
  have hdimMap : Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) = Module.finrank ℂ G :=
    (LinearEquiv.finrank_map_eq Tm.toLinearEquiv T).trans hdimT
  have hrMap : 1 ≤ Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) := by
    rw [hdimMap]
    exact hrG
  have hGTmap : Submodule.IsCloseTo 0.005
      (G.map Tm.toLinearEquiv.toLinearMap) (T.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hGT
  have hTGmap : Submodule.IsCloseTo 0.005
      (T.map Tm.toLinearEquiv.toLinearMap) (G.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hTG
  have hbudget' : (D : ℝ) ^ 12 * Delta ≤ 0.00001 := by
    simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
  obtain ⟨W, hWdim, hWviable⟩ :=
    Submodule.exists_isViable_finrank_lt_rank_mul_pow hGTmap hTGmap Fops
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta) hD hbudget' hrMap
  refine ⟨W, ?_, hWviable⟩
  simpa only [hdimMap] using hWdim
end TNLean.MPS.AreaLaw
end
end

section

open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A fixed actual interval has accuracy-dependent viable families with one
universal scalar choice. The auxiliary integer `m` enlarges only the
numerical count budget; every physical configuration remains valued in
`Fin q`, and the target coordinates use only the actual interval and `q`.
The low cluster and all operator data are derived from the original bonds.
Supporting the dyadic entropy route in ALVV, arXiv:1602.08828v2,
`thm:al-dg`, lines 1048–1099, through `t:ais`, lines 1010–1024.
No tail, core, spectral basis or residual bound is an input. This is the
long-interval case with normalized gap; no efficient core or runtime result
is asserted. -/
private theorem exists_accuracy_long_middle_actual_dg_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (m q : ℕ) (g : ℝ), 2 ≤ q → q ≤ m → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      21 ≤ ell ∧ m ≤ D ∧ 2 ≤ D ∧
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
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) T G ∧
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G T ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
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
  obtain ⟨A, hA, hA21, _hAM, _hAlog, hall⟩ :=
    Real.exists_dg_accuracy_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro m q g hq hqm hg hg1 u ell D cA
  obtain ⟨hell, hmD, hD, _hlower, _hupper, _hscale, _hcount,
    hlogD, htrade, htail⟩ := hall m g (hq.trans hqm) hg hg1
  refine ⟨hell, hmD, hD, hlogD, ?_⟩
  intro L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm h hs h0 h1 mu H hH G hmu hgap
  have hell1 : 1 ≤ ell := Nat.le_trans (by decide : 1 ≤ 21) hell
  let a := max p ell - ell
  let b := min r (L - ell) - ell - 1
  obtain ⟨_haEnd, _hbEnd, hab, hb, _hpp, _hpq, _hqq, _hlen,
    _hleft, _hright, _htotal, hsub, hcollar⟩ :=
    inward_effective_cuts L ell p r hell1 hpr hrL hlong
  let xi : ℝ := g / (1000000 * (m : ℝ))
  let scale : ℝ := 1 / (m : ℝ)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hq.trans hqm)
  have hmRpos : 0 < (m : ℝ) := by linarith
  have hscale0 : 0 < scale := one_div_pos.mpr hmRpos
  have hscale1 : scale ≤ 1 := (div_le_iff₀ hmRpos).2 (by linarith)
  have hxi : xi = scale * g / 1000000 := by
    dsimp only [xi, scale]
    rw [div_mul_eq_mul_div, one_mul, div_div, mul_comm (m : ℝ) 1000000]
  obtain ⟨e, E0, _hground, _horigin, hE0, hE4, hnorm,
    v, lam, heigen, hclosed, _hband, hdim, hTG, hGT, _hnewgap⟩ :=
    exists_five_region_physical_scaled_low_cluster L q a b ell (by omega) hell
      (hab.trans (Nat.le_succ b)) (hb.trans (Nat.sub_le L 1))
      h hs h0 h1 mu g xi scale hg hg1 hscale0 hscale1 htail hxi.le hmu hgap
  have herror : scale / 200 = 1 / (200 * (m : ℝ)) := by
    dsimp only [scale]
    rw [div_div, mul_comm (m : ℝ) 200]
  rw [herror] at hTG hGT
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
  obtain ⟨hsep, hendpoint, hR0, hR8, _hwidth, hsquare⟩ :=
    Real.physical_chebyshev_endpoints ell E0 g hell hE0 hE4 hg hg1
  have hDelta0 : 0 < Delta := by
    change 0 < (2 * Real.exp
      (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    exact sq_pos_of_pos (mul_pos (by norm_num) (Real.exp_pos _))
  have hDelta : Delta = 4 * Real.exp
      (-4 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / (upper - eta0))) := hsquare
  have hsmall : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 := by
    rw [hDelta]
    simpa only [neg_mul] using htrade (upper - eta0) hR0 hR8
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
    exact hN'.trans (collar_card_le_square_of_larger_count_base
      q m ell (Jtarget \ J0).card (D0 ^ 2) hq hqm hell1 hcollar le_rfl)
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
  refine ⟨T, Delta, F, hTG, hGT, hdim, hDelta0, hsmall, ?_⟩
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

/-- One universal choice of scale gives viable families of every numerical
accuracy on every actual interval of a gapped nearest-neighbour chain. The
integer `m` is at least the physical on-site dimension and controls only the
count and error bounds; configurations and the tensor identification remain
those of the original chain. The full ground space is used. Supporting the
accuracy refinement in ALVV, arXiv:1602.08828v2, `thm:al-dg`, lines 1048–1099,
through `t:ais`, lines 1010–1024. No tail or regional spectral estimate is an
input, and no efficient construction is asserted. -/
private theorem exists_accuracy_physical_dg_viable_family :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q m p r : ℕ), q ≤ m → p ≤ r → r ≤ L →
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
      let u : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
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
      21 ≤ ell ∧ m ≤ D ∧ 2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ (W : Fin (D ^ 2) → EM →L[ℂ] EM)
        (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) T G ∧
        Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G T ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
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
  obtain ⟨A, hA, hA21, hall⟩ := exists_accuracy_long_middle_actual_dg_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q m p r hqm hpr hrL h hs h0 h1 mu nu gamma hgamma H hH
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
  obtain ⟨hell, hmD, hD, hlogD, hlong⟩ := hall m q g hq hqm hg hg1
  refine ⟨hell, hmD, hD, hlogD, ?_⟩
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell :=
      (card_interval_le (L := L) p r).trans hshort
    obtain ⟨W, Delta, hDelta, hbudget, himprove⟩ :=
      exists_short_actual_region_improving_family_of_count_base (F := EE)
        L q m ell J hq hqm (Nat.le_trans (by decide : 1 ≤ 21) hell) hJ
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hGG : Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G G := by
      apply Submodule.isCloseTo_iff.mpr
      intro x hx
      rw [G.starProjection_eq_self_iff.mpr hx]
      have herr : 0 ≤ (1 / (200 * (m : ℝ)) : ℝ) := by positivity
      nlinarith [sq_nonneg ‖x‖]
    refine ⟨W, G, Delta, hGG, hGG, rfl, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact himprove (G.map (Tm.toLinearEquiv :
      EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] (EM ⊗[ℂ] EE))) S delta hS hdelta
  · obtain ⟨T, Delta, W, hTG, hGT, hdim, hDelta, hbudget, himprove⟩ :=
      hlong L p r hpr hrL (Nat.lt_of_not_ge hshort) h hs h0 h1 mu hmu hgapg
    refine ⟨W, T, Delta, hTG, hGT, hdim, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact (himprove S delta hS hdelta).2
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The accuracy-dependent physical families and a bootstrap subspace share
one universal scale. The bootstrap family is obtained by setting the numerical
count base equal to the original on-site dimension, before choosing the
families at other accuracies. Consequently its dimension is bounded using
that same scale, rather than an independently chosen constant. Supporting
ALVV, arXiv:1602.08828v2, `prop:albootstrap-dg`, lines 1062–1075, and the
entropy argument of `thm:al-dg`, lines 1080–1099. All tensor coordinates are
those of the actual interval. -/
theorem exists_accuracy_physical_interval_family_and_bootstrap :
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
      2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∃ W0 : Submodule ℂ EM,
        Module.finrank ℂ W0 < Module.finrank ℂ G * D ^ 24 ∧
        Submodule.IsViable (F := EE) 0.015 W0
          (G.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
            (EM ⊗[ℂ] EE))) ∧
        ∀ (m : ℕ), q ≤ m →
          let um : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
          let ellm : ℕ := ⌈A * um ^ 2 / g⌉₊
          let Dm : ℕ := (m * ellm ^ 2) ^ (22 * ellm)
          21 ≤ ellm ∧ m ≤ Dm ∧ 2 ≤ Dm ∧
          Real.log (Dm : ℝ) ≤ 22 * (A + 1) * cA / g * um ^ 3 ∧
          ∃ (W : Fin (Dm ^ 2) → EM →L[ℂ] EM)
            (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
            Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) T G ∧
            Submodule.IsCloseTo (1 / (200 * (m : ℝ)) : ℝ) G T ∧
            Module.finrank ℂ T = Module.finrank ℂ G ∧
            0 < Delta ∧ (Dm : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
            ∀ (S : Submodule ℂ EM) (delta : ℝ),
              Submodule.IsViable (F := EE) delta S
                (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                  (EM ⊗[ℂ] EE))) → delta < 1 →
              Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ (2 : ℕ))
                (⨆ j, S.map (W j : EM →ₗ[ℂ] EM))
                (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                  (EM ⊗[ℂ] EE))) := by
  classical
  obtain ⟨A, hA, hA21, hfamily⟩ := exists_accuracy_physical_dg_viable_family
  refine ⟨A, hA, hA21, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g u ell D cA J beta tau U Phi Tm EM EE
  obtain ⟨_hell, _hqD, hD, hlogD, Fops, T, Delta, hTG, hGT,
    hdimT, _hDelta0, hbudget, himprove⟩ :=
    hfamily L q q p r le_rfl hpr hrL h hs h0 h1 mu nu gamma
      hgamma hmu hnu hmunu hgap
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have herror : (1 / (200 * (q : ℝ)) : ℝ) ≤ 1 / 200 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hqR]
  have hGTsmall : Submodule.IsCloseTo (1 / 200 : ℝ) G T := hGT.of_le herror
  have hTGsmall : Submodule.IsCloseTo (1 / 200 : ℝ) T G := hTG.of_le herror
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hdimMap : Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) = Module.finrank ℂ G :=
    (LinearEquiv.finrank_map_eq Tm.toLinearEquiv T).trans hdimT
  have hrMap : 1 ≤ Module.finrank ℂ
      (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
        (EM ⊗[ℂ] EE))) := by
    rw [hdimMap]
    exact hrG
  have hGTmap : Submodule.IsCloseTo 0.005
      (G.map Tm.toLinearEquiv.toLinearMap) (T.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hGTsmall
  have hTGmap : Submodule.IsCloseTo 0.005
      (T.map Tm.toLinearEquiv.toLinearMap) (G.map Tm.toLinearEquiv.toLinearMap) := by
    rw [show (0.005 : ℝ) = 1 / 200 by norm_num]
    exact (Submodule.isCloseTo_map_iff Tm).mpr hTGsmall
  have hbudget' : (D : ℝ) ^ 12 * Delta ≤ 0.00001 := by
    simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
  obtain ⟨W0, hWdim, hWviable⟩ :=
    Submodule.exists_isViable_finrank_lt_rank_mul_pow hGTmap hTGmap Fops
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta) hD hbudget' hrMap
  refine ⟨hD, hlogD, W0, ?_, hWviable, ?_⟩
  · simpa only [hdimMap] using hWdim
  · intro m hqm um ellm Dm
    exact hfamily L q m p r hqm hpr hrL h hs h0 h1 mu nu gamma
      hgamma hmu hnu hmunu hgap
end TNLean.MPS.AreaLaw
end
