/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalLowDensityFamily
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import QICLean.Analysis.ShiftedLowEnergyCoordinates
import QICLean.Analysis.ViableSubspaceCoordinates

/-!
# Low-energy improving families on long prescribed intervals

Inward effective cuts remove at most two window lengths from a prescribed
interval. The exact polynomial family of the same global clipped matrix
is decomposed on the prescribed region, with the collar cost absorbed in
the same numerical count used for suppression. Scalar shifts are removed
using the original Hamiltonian's canonical minimum. Zero extension retains
the same image spans and gives exactly the required squared count.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041. The fixed bandwidth is explicit. This long-interval
lemma retains `4*ell < r-p`; short intervals are treated by actual
configuration matrix units in the subsequent interval theorem.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The actual regional tensor decompositions have dependent finite configuration types.
/-- A fixed-bandwidth low-energy family on every sufficiently long prescribed
interval, including intervals touching the chain boundary. The inward cuts
and collar cardinality are constructed, and the same actual global clipped
polynomial supplies all regional factors. The original targets use the raw
Hamiltonian's canonical energy normalization. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_long_interval_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      ∀ _hlong : 4 * ell < r - p,
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
      ∃ A : Fin (D ^ 2) → EM →L[ℂ] EM,
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
          Tlo ≤ Thi ∧
          Submodule.IsCloseTo (1 / 200)
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta)) Thi ∧
          Submodule.IsCloseTo (1 / 200) Tlo
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta - 3 * w)) ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
          ∀ (S : Submodule ℂ EM) (delta : ℝ),
            Submodule.IsViable (F := EE) delta S (Thi.map Tm.toLinearEquiv.toLinearMap) →
            delta < 1 →
            let grow := ⨆ i : Fin (D ^ 2), S.map (A i).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ 2)
                grow (Tlo.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hCeta, hregional⟩ :=
    exists_fixed_bandwidth_five_region_regional_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r w hq hqm hpr hrL hw g u ell D h hs h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, _⟩ := hregional L q m 0 0 w hq hqm hw
  refine ⟨hell, hlogD, ?_⟩
  intro hlong J beta tau U Phi Tm EM EE
  have hell1 : 1 ≤ ell := (by decide : 1 ≤ 21).trans hell
  let a := max p ell - ell
  let b := min r (L - ell) - ell - 1
  obtain ⟨_ha, _hb, hab, hbL, _hpp, _hpq, _hqq, _hlen,
    _hleft, _hright, _htotal, hsub, hcollar⟩ :=
    inward_effective_cuts L ell p r hell1 hpr hrL hlong
  have hcost :
      (interval L (a + ell) (b + ell + 1) \ J).card +
        (J \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell := by
    have hsub' : interval L (a + ell) (b + ell + 1) ⊆ J := hsub
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub', Finset.card_empty, zero_add]
    exact hcollar
  obtain ⟨_, _, hphysical⟩ := hregional L q m a b w hq hqm hw
  obtain ⟨e, E0, _x, z, hO, hClip, _hxunit, _hx, _hlo, hcenter, hzunit, hz, hE0low,
    _hE0, _hE04, _hnorm, hfamilies⟩ := hphysical hab hbL J hcost h hs h0 h1
  obtain ⟨_hminimum, hidentity⟩ :=
    hRaw.spectralSpanLE_centered_ground_of_eq hO (∑ j, e j) E0 z
      hcenter hzunit hz hE0low
  obtain ⟨N, W, hN, hfilters⟩ := hfamilies
  let A0 : Fin N → EM →L[ℂ] EM := fun i ↦
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W i)
  have hcard : Fintype.card (Fin N) ≤ D ^ 2 := by simpa only [Fintype.card_fin] using hN
  obtain ⟨_f, A, _hA, _hzero, hspan⟩ :=
    Submodule.exists_clm_family_extension_of_card_le hcard A0
  refine ⟨A, ?_⟩
  intro eta hbuffer hetaLD
  let lower := Submodule.spectralSpanLE hClip.eigenvectorBasis hClip.eigenvalues
    (E0 + eta - 2 * w)
  let higher := Submodule.spectralSpanLE hClip.eigenvectorBasis hClip.eigenvalues
    (E0 + eta - w)
  let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
    Real.sqrt (w / (7 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
  obtain ⟨hnest, hupper, hlower, htrade, _poly, _hdegree, _hp0, _M, _hM, himprove⟩ :=
    hfilters eta hbuffer hetaLD
  have hidentityLower :
      Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w) =
        Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
          (minEigenvalue hRaw + eta - 3 * w) := by
    simpa only [add_sub_assoc] using hidentity (eta - 3 * w)
  refine ⟨lower, higher, Delta, hnest, ?_, ?_, by dsimp only [Delta]; positivity, htrade, ?_⟩
  · simpa only [hidentity eta] using hupper
  · simpa only [hidentityLower] using hlower
  · intro S delta hS hdelta
    obtain ⟨_hdim, hviable⟩ := himprove S delta hS hdelta
    refine ⟨?_, ?_⟩
    · simpa only [Fintype.card_fin] using
        Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap)
    · rw [hspan S]
      exact hviable

end TNLean.MPS.AreaLaw
