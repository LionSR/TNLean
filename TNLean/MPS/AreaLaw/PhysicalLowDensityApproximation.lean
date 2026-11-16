/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SharpRegionalLowDensityFamily
import TNLean.MPS.AreaLaw.LowDensityLogDimension
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import QICLean.Analysis.ViableSubspaceSchmidtRank
import QICLean.Analysis.ViableSubspaceMinimum
import QICLean.Analysis.ViableSubspaceNestedEnlargement

/-!
# Normalized original-band approximations at independent scales

One actual constant-viable regional space is chosen before the requested
accuracy. The independently chosen sharp polynomial family refines that same
space. Two explicit spectral comparisons transfer only the input and output
viability formulas, retaining the actual clipped polynomial construction.
The short-interval alternative uses the original vector and its exact cut
rank. No gap or invariance of an original low-energy band is assumed.

This supports ALVV, arXiv:1602.08828v2, the fixed-cut approximation in
Theorem `thm:al-ld`, lines 1096–1105. The sharper logarithmic rank estimate
and global sequential MPS construction are separate consequences.

**Scope restriction (physical intervals and fixed bandwidth):** The theorem
retains `q ≥ 2` and one coefficient for each fixed bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- One viable outer-band space, selected before accuracy, gives normalized
fixed-cut approximations to every original inner-band unit vector. The rank
uses its actual dimension and the actual sharp polynomial count. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_normalized_low_energy_approximation_of_independent_scales
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Kb C : ℝ, 0 < Kb ∧ 21 ≤ C ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ h0 : ∀ i, 0 ≤ h i, (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + c)
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      ∃ W0 : Submodule ℂ EM,
        (Module.finrank ℂ W0 : ℝ) ≤ (Module.finrank ℂ (G etaLD) : ℝ) *
          Real.exp (Kb / (b / 2) *
            (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3) ∧
        Submodule.IsViable (F := EE) (3 / 200) W0
          ((G (etaLD - b / 2)).map Tm.toLinearEquiv.toLinearMap) ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        let u := 16 + Real.log (1 / g) + Real.log (1 / delta)
        ∃ ell : ℕ, 1 ≤ ell ∧
          (ell : ℝ) ≤ 8 / g +
            (7 * C) ^ (1 / 4 : ℝ) * (1 / g) ^ (1 / 4 : ℝ) * u ^ (3 / 4 : ℝ) ∧
        let D1 := (q * ell ^ 2) ^ (22 * ell)
        let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
          1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
          Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ Module.finrank ℂ W0 * D1 ^ 2 := by
  classical
  obtain ⟨Kb, hKb, hinitial⟩ :=
    exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound etaLD hLD
  obtain ⟨C, hC, hsharp⟩ := exists_fixed_bandwidth_sharp_regional_low_energy_family etaLD hLD
  refine ⟨Kb, C, hKb, hC, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw
    J beta tau U Phi Tm G EM EE b g
  let : Nonempty (Fin L → Fin q) := config
  have hb : 0 < b := lt_min hv (by positivity)
  have hbcap : b ≤ etaLD / 2 := min_le_right _ _
  have hbv : b ≤ v := min_le_left _ _
  have hw : 0 < b / 6 := by positivity
  obtain ⟨W0, hWdim, hW0⟩ :=
    hinitial L q p r (b / 2) hq hpr hrL (by positivity) h hs h0 h1
  refine ⟨W0, hWdim, hW0, ?_⟩
  intro delta hdelta hdelta1 u
  obtain ⟨ell, hell, hbound, hregional⟩ := hsharp (b / 6) delta hw hdelta hdelta1
  refine ⟨ell, hell, hbound, ?_⟩
  intro D1 eCoord ψ hψG hψ
  have hG {c d : ℝ} (hcd : c ≤ d) : G c ≤ G d :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hcd])
  have hψupper : ψ ∈ G (etaLD - b / 2) := hG (by linarith only [hbv, hb]) hψG
  have htargetne : (G (etaLD - b / 2)).map Tm.toLinearEquiv.toLinearMap ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨Tm ψ, ⟨ψ, hψupper, rfl⟩, ?_⟩
    intro hz
    have hn : ‖Tm ψ‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hψ
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hWone : 1 ≤ Module.finrank ℂ W0 := Submodule.one_le_finrank_iff.mpr
    (Submodule.isViable_ne_bot_of_target_ne_bot hW0 (by norm_num) htargetne)
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell := (card_interval_le (L := L) p r).trans hshort
    have hellsq : 1 ≤ ell ^ 2 := hell.trans (Nat.le_self_pow (by decide) ell)
    have hbase : q ≤ q * ell ^ 2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left q hellsq
    have hcount : Fintype.card (J → Fin q) ≤ D1 ^ 2 := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      calc
        q ^ J.card ≤ q ^ (4 * ell) := Nat.pow_le_pow_right (by omega) hJ
        _ ≤ (q * ell ^ 2) ^ (4 * ell) := Nat.pow_le_pow_left hbase _
        _ ≤ (q * ell ^ 2) ^ ((22 * ell) * 2) :=
          Nat.pow_le_pow_right ((by omega : 0 < q).trans_le hbase) (by omega)
        _ = D1 ^ 2 := pow_mul _ _ _
    have hbudget : D1 ^ 2 ≤ Module.finrank ℂ W0 * D1 ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (D1 ^ 2) hWone
    refine ⟨ψ, hψ, ?_, (Matrix.schmidtRank_le_left _).trans (hcount.trans hbudget)⟩
    have hinner : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
    rw [hinner]
    linarith only [hdelta]
  · let a := max p ell - ell
    let c := min r (L - ell) - ell - 1
    obtain ⟨_ha, _hc, hac, hcL, _hpp, _hpq, _hqq, _hlen,
      _hleft, _hright, _htotal, hsub, hcollar⟩ :=
      inward_effective_cuts L ell p r hell hpr hrL (Nat.lt_of_not_ge hshort)
    have hcost : (interval L (a + ell) (c + ell + 1) \ J).card +
        (J \ interval L (a + ell) (c + ell + 1)).card ≤ 2 * ell := by
      have hsub' : interval L (a + ell) (c + ell + 1) ⊆ J := hsub
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub', Finset.card_empty, zero_add]
      exact hcollar
    obtain ⟨energies, E0, _x, _z, hO, hC, _hxunit, _hx, _hlo, _hcenter,
      _hzunit, _hz, _hE0low, _hE0, _hE04, _hnorm, _hminimum, hidentity, hfamilies⟩ :=
      hregional L q q a c hq le_rfl hac hcL J hcost h hs h0 h1
    obtain ⟨N, W, hN, hfilters⟩ := hfamilies
    let eta1 := etaLD - b / 2
    have hbuffer : 6 * (b / 6) ≤ eta1 := by dsimp only [eta1]; linarith only [hbcap, hb]
    obtain ⟨_hnest, hupper, hlower, hDelta, _poly, _hdegree, _hp0,
      _M, _hM, himprove⟩ := hfilters eta1 hbuffer (by dsimp only [eta1]; linarith only [hb])
    let Tlo := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
      (E0 + eta1 - 2 * (b / 6))
    let Thi := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
      (E0 + eta1 - b / 6)
    have hupperRaw : Submodule.IsCloseTo (delta / 100) (G eta1) Thi :=
      Eq.mp (congrArg (fun T ↦ Submodule.IsCloseTo (delta / 100) T Thi)
        (hidentity eta1)) hupper
    have hleft : E0 + (etaLD - b) = E0 + eta1 - 3 * (b / 6) := by
      dsimp only [eta1]
      ring
    have hsource : Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues
        (E0 + eta1 - 3 * (b / 6)) = G (etaLD - b) :=
      (congrArg (fun c ↦ Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues c)
        hleft.symm).trans (hidentity (etaLD - b))
    have hlowerRaw : Submodule.IsCloseTo (delta / 100) Tlo (G (etaLD - b)) :=
      Eq.mp (congrArg (fun T ↦ Submodule.IsCloseTo (delta / 100) Tlo T) hsource) hlower
    let A : Fin N → EM →L[ℂ] EM := fun j ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)
    let V : Submodule ℂ EM := ⨆ j : Fin N, W0.map (A j).toLinearMap
    obtain ⟨hdim, hVinner⟩ := Submodule.viable_enlargement_of_close_nested_targets
      Tm (G eta1) (G (etaLD - b)) (G (etaLD - v)) Tlo Thi W0 A delta _
      hdelta hdelta1 (hG (by linarith only [hbv])) hW0 hupperRaw hlowerRaw hDelta himprove
    have hcomp : eCoord.trans (Submodule.euclideanTensorEquiv
        (J → Fin q) (↥(Jᶜ) → Fin q)) = Tm := by
      dsimp only [eCoord]
      rw [← LinearIsometryEquiv.trans_assoc, LinearIsometryEquiv.symm_trans_self,
        LinearIsometryEquiv.trans_refl]
    have hVcoord : Submodule.IsViable (F := EE) (delta / 2) V
        ((G (etaLD - v)).map (eCoord.trans (Submodule.euclideanTensorEquiv
          (J → Fin q) (↥(Jᶜ) → Fin q))).toLinearEquiv.toLinearMap) := by
      rw [hcomp]
      exact hVinner
    obtain ⟨φ, hφ, _hφV, hoverlap, hrank⟩ :=
      hVcoord.exists_unit_schmidtRank_le_of_equiv eCoord
        (by linarith only [hdelta1]) hψG hψ
    refine ⟨φ, hφ, ?_, hrank.trans ?_⟩
    · nlinarith [norm_nonneg ⟪φ, ψ⟫_ℂ]
    · calc
        Module.finrank ℂ V ≤ N * Module.finrank ℂ W0 := hdim
        _ ≤ D1 ^ 2 * Module.finrank ℂ W0 := Nat.mul_le_mul_right _ hN
        _ = Module.finrank ℂ W0 * D1 ^ 2 := Nat.mul_comm _ _

end TNLean.MPS.AreaLaw
