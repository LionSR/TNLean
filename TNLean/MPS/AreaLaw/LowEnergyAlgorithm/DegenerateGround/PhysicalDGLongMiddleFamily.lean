/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.Analysis.Subspace.ViableSubspace
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalPolynomialTensorFamily
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.PhysicalLowEnergyCloseness
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalIntervalTransport
import QICLean.Analysis.Parameter.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.ShortRegionViableFamily

/-!
# Long-middle families for a gapped chain

For an actual nearest-neighbour Hamiltonian with normalized gap, one universal parameter gives
a common viable-space enlargement on every interval whose middle is longer than four
bandwidths, both at constant accuracy and at every prescribed accuracy. These are the
long-middle cases of the families in `TNLean.MPS.AreaLaw.PhysicalDGViability`.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

open ManyBody (card_interval_le interval)


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
theorem exists_long_middle_actual_dg_family :
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
      let tau := (ManyBody.cutEquiv β Jtarget).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β Jtarget) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig β Jtarget) ℂ)).repr
      let Tcoord := U.trans Phi.symm
      let Tm := Tcoord.trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig β Jtarget))
        (EuclideanSpace ℂ (ManyBody.RegionConfig β Jtarget)))
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
            (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)) δ S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)))) → δ < 1 →
          let grow := ⨆ i : Fin (D ^ 2), S.map (F i : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
              (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q))
              (Delta / (1 - δ) ^ 2) grow
              (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                  EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)))) := by
  classical
  obtain ⟨A, hA, hA21, hall⟩ := exists_five_region_dg_cluster_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro q g hq hg hg1 u ell D cA
  obtain ⟨hell, hD, hlogD, hphysical⟩ := hall q g hq hg hg1
  refine ⟨hell, hD, hlogD, ?_⟩
  intro L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm Φ h0 h1 mu H hH G hmu hgap
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
      Φ h0 h1 mu hmu hgap
  let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
  let Areg : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
    ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
  let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
    (fun i ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
  let Y := ∑ i ∈ Cross, Φ.term i
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
      L q a b ell (ell ^ 2) hell1 hq hdegree hab hb Φ e (ell : ℝ) Jtarget
  change N ≤ D0 ^ 2 * q ^
    (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) at hNraw
  have hdiff : J0 \ Jtarget = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hN : N ≤ D ^ 2 := by
    have hN' : N ≤ D0 ^ 2 * q ^ (2 * (Jtarget \ J0).card) := by
      simpa only [hdiff, Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hNraw
    exact hN'.trans (Nat.collar_card_le_square_at_square_degree
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
      (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q))
      (Delta / (1 - δ) ^ 2)
      ((⨆ i : Fin (D ^ 2), S.map ((F i).toLinearMap)) :
        Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q)))
      (T.map Tm.toLinearEquiv.toLinearMap)
    rw [hspan S]
    simpa only [Nat.cast_pow] using hviable
end TNLean.MPS.AreaLaw
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
theorem exists_accuracy_long_middle_actual_dg_family :
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
      let tau := (ManyBody.cutEquiv β Jtarget).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β Jtarget) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig β Jtarget) ℂ)).repr
      let Tcoord := U.trans Phi.symm
      let Tm := Tcoord.trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig β Jtarget))
        (EuclideanSpace ℂ (ManyBody.RegionConfig β Jtarget)))
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
            (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)) δ S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)))) → δ < 1 →
          let grow := ⨆ i : Fin (D ^ 2), S.map (F i : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
              (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q))
              (Delta / (1 - δ) ^ 2) grow
              (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                  EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q)))) := by
  classical
  obtain ⟨A, hA, hA21, _hAM, _hAlog, hall⟩ :=
    Real.exists_dg_accuracy_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro m q g hq hqm hg hg1 u ell D cA
  obtain ⟨hell, hmD, hD, _hlower, _hupper, _hscale, _hcount,
    hlogD, htrade, htail⟩ := hall m g (hq.trans hqm) hg hg1
  refine ⟨hell, hmD, hD, hlogD, ?_⟩
  intro L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm Φ h0 h1 mu H hH G hmu hgap
  have hell1 : 1 ≤ ell := Nat.le_trans (by decide : 1 ≤ 21) hell
  let a := max p ell - ell
  let b := min r (L - ell) - ell - 1
  obtain ⟨_haEnd, _hbEnd, hab, hb, _hpp, _hpq, _hqq, _hlen,
    _hleft, _hright, _htotal, hsub, hcollar⟩ :=
    inward_effective_cuts L ell p r hell1 hpr hrL hlong
  let xi : ℝ := g / (1000000 * (m : ℝ))
  let scale : ℝ := 1 / (m : ℝ)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hq.trans hqm)
  have hmRpos : 0 < (m : ℝ) := by linarith only [hmR]
  have hscale0 : 0 < scale := one_div_pos.mpr hmRpos
  have hscale1 : scale ≤ 1 := (div_le_iff₀ hmRpos).2 (by linarith only [hmR])
  have hxi : xi = scale * g / 1000000 := by
    dsimp only [xi, scale]
    rw [div_mul_eq_mul_div, one_mul, div_div, mul_comm (m : ℝ) 1000000]
  obtain ⟨e, E0, _hground, _horigin, hE0, hE4, hnorm,
    v, lam, heigen, hclosed, _hband, hdim, hTG, hGT, _hnewgap⟩ :=
    exists_five_region_physical_scaled_low_cluster L q a b ell (by omega) hell
      (hab.trans (Nat.le_succ b)) (hb.trans (Nat.sub_le L 1))
      Φ h0 h1 mu g xi scale hg hg1 hscale0 hscale1 htail hxi.le hmu hgap
  have herror : scale / 200 = 1 / (200 * (m : ℝ)) := by
    dsimp only [scale]
    rw [div_div, mul_comm (m : ℝ) 200]
  rw [herror] at hTG hGT
  let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
  let Areg : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
    ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
  let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
    (fun i ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
  let Y := ∑ i ∈ Cross, Φ.term i
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
      L q a b ell (ell ^ 2) hell1 hq hdegree hab hb Φ e (ell : ℝ) Jtarget
  change N ≤ D0 ^ 2 * q ^
    (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) at hNraw
  have hdiff : J0 \ Jtarget = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hN : N ≤ D ^ 2 := by
    have hN' : N ≤ D0 ^ 2 * q ^ (2 * (Jtarget \ J0).card) := by
      simpa only [hdiff, Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hNraw
    exact hN'.trans (Nat.collar_card_le_square_of_larger_count_base
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
      (F := EuclideanSpace ℂ ({v // v ∉ Jtarget} → Fin q))
      (Delta / (1 - δ) ^ 2)
      ((⨆ i : Fin (D ^ 2), S.map ((F i).toLinearMap)) :
        Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q)))
      (T.map Tm.toLinearEquiv.toLinearMap)
    rw [hspan S]
    simpa only [Nat.cast_pow] using hviable
end TNLean.MPS.AreaLaw
end
