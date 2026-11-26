/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.SharpApproximationParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.SharpRegionalLowDensityFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LowDensityMinimumDimension
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalIntervalTransport
import QICLean.Channel.Schmidt.ViableSubspaceSchmidtRank
import QICLean.Probability.Sampling.ViableSubspaceMinimum
import TNLean.MPS.Tensor.OpenMPS.NormalizedSequentialApproximation
import QICLean.Analysis.Real.LogRankRounding
import QICLean.ManyBody.Entropy.ViableSubspaceEntropy
import QICLean.Channel.Schmidt.MaximalOverlap

/-!
# Sharp logarithmic rank for an original low-energy band

The same initial viable space is refined by the actual polynomial family at
independent truncation and window scales. Its actual dimension contributes
exactly one logarithm of the original full-band dimension. The remaining
accuracy dependence has power three quarters of the logarithmic accuracy,
as in ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105.

**Scope restriction (physical intervals and fixed bandwidth):** The theorem
retains `q ≥ 2` and a coefficient for each fixed positive bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`. The capped width is
explicit; comparison with the source variable uses its stated range
`0 < v ≤ etaLD`. No original-band gap or invariance is assumed.

It also contains the following results.

* `exists_fixed_bandwidth_normalized_low_energy_approximation_of_independent_scales`
  (in `TNLean.MPS.AreaLaw`):
  normalized original-band approximations at independent scales.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_low_energy_normalized_isOpenMPS_approximation`: one
  sharp matrix product approximation to an original low-energy vector.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_low_energy_strict_isOpenMPS_approximation`: strict
  global low-energy MPS approximation in positive local dimension.
-/

section PhysicalLowDensityApproximation

/-!
## Normalized original-band approximations at independent scales

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

open ManyBody (card_interval_le interval)

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
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ h0 : ∀ i, 0 ≤ Φ.term i, (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + c)
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({x // x ∉ J} → Fin q)
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
        let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) ({x // x ∉ J} → Fin q)).symm
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
          1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
          Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ Module.finrank ℂ W0 * D1 ^ 2 := by
  classical
  obtain ⟨Kb, hKb, hinitial⟩ :=
    exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound etaLD hLD
  obtain ⟨C, hC, hsharp⟩ := exists_fixed_bandwidth_sharp_regional_low_energy_family etaLD hLD
  refine ⟨Kb, C, hKb, hC, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw
    J beta tau U Phi Tm G EM EE b g
  let : Nonempty (Fin L → Fin q) := config
  have hb : 0 < b := lt_min hv (by positivity)
  have hbcap : b ≤ etaLD / 2 := min_le_right _ _
  have hbv : b ≤ v := min_le_left _ _
  have hw : 0 < b / 6 := by positivity
  obtain ⟨W0, hWdim, hW0⟩ :=
    hinitial L q p r (b / 2) hq hpr hrL (by positivity) Φ h0 h1
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
      hregional L q q a c hq le_rfl hac hcL J hcost Φ h0 h1
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
        (J → Fin q) ({x // x ∉ J} → Fin q)) = Tm := by
      dsimp only [eCoord]
      rw [← LinearIsometryEquiv.trans_assoc, LinearIsometryEquiv.symm_trans_self,
        LinearIsometryEquiv.trans_refl]
    have hVcoord : Submodule.IsViable (F := EE) (delta / 2) V
        ((G (etaLD - v)).map (eCoord.trans (Submodule.euclideanTensorEquiv
          (J → Fin q) ({x // x ∉ J} → Fin q))).toLinearEquiv.toLinearMap) := by
      rw [hcomp]
      exact hVinner
    obtain ⟨φ, hφ, _hφV, hoverlap, hrank⟩ :=
      hVcoord.exists_unit_schmidtRank_le_of_equiv eCoord
        (by linarith only [hdelta1]) hψG hψ
    refine ⟨φ, hφ, ?_, hrank.trans ?_⟩
    · have hx0 : 0 ≤ ‖⟪φ, ψ⟫_ℂ‖ := norm_nonneg _
      rcases le_total 1 ‖⟪φ, ψ⟫_ℂ‖ with h1 | h1
      · linarith only [h1, hdelta]
      · have hsq : ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ≤ ‖⟪φ, ψ⟫_ℂ‖ := by
          rw [sq]
          exact mul_le_of_le_one_left hx0 h1
        linarith only [hsq, hoverlap, hdelta]
    · calc
        Module.finrank ℂ V ≤ N * Module.finrank ℂ W0 := hdim
        _ ≤ D1 ^ 2 * Module.finrank ℂ W0 := Nat.mul_le_mul_right _ hN
        _ = Module.finrank ℂ W0 * D1 ^ 2 := Nat.mul_comm _ _

end TNLean.MPS.AreaLaw

end PhysicalLowDensityApproximation

section PhysicalLowDensitySharpApproximation

open ManyBody (interval)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- A normalized fixed-cut approximation has the sharp logarithmic rank bound,
with coefficient one on the logarithm of the original low-energy dimension.
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_normalized_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ h0 : ∀ i, 0 ≤ Φ.term i, (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + c)
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) ({x // x ∉ J} → Fin q)).symm
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨Kb, C, hKb, hC, hactual⟩ :=
    exists_fixed_bandwidth_normalized_low_energy_approximation_of_independent_scales etaLD hLD
  let beta : ℝ := (7 * C) ^ (1 / 4 : ℝ)
  let kappa : ℝ := 44 * (1 + Real.log (11 + beta))
  let K : ℝ := 8 * Kb + 2 * kappa * (11 + beta)
  have hbeta : 0 ≤ beta := Real.rpow_nonneg (by linarith only [hC]) _
  have hlogbeta : 0 ≤ Real.log (11 + beta) := Real.log_nonneg (by linarith only [hbeta])
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw
    J betaCoord tau U Phi Tm G e b g u
  let : Nonempty (Fin L → Fin q) := config
  have hb : 0 < b := lt_min hv (by positivity)
  have hg : 0 < g := lt_min (by dsimp only [b]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgb : g ≤ b / 2 := (min_le_left _ _).trans (by linarith only [hb])
  have hinv : 1 ≤ 1 / g := (one_le_div hg).2 hg1
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg hinv
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hcost : Kb / (b / 2) *
      (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 ≤
      8 * Kb / g * u ^ 3 := by
    have hinvb : 1 / (b / 2) ≤ 1 / g := one_div_le_one_div_of_le hg hgb
    have hlogb : Real.log (1 + 1 / (b / 2)) ≤ 1 + Real.log (1 / g) := by
      calc
        _ ≤ Real.log (2 * (1 / g)) :=
          Real.log_le_log (by positivity) (by linarith only [hinv, hinvb])
        _ = Real.log 2 + Real.log (1 / g) :=
          Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + Real.log (1 / g) := by
          linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hbase : 1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2)) ≤ 2 * u := by
      dsimp only [u]
      linarith only [hlogb, hlogq, hlogg]
    have hbase0 : 0 ≤ 1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2)) := by
      have hn := Real.log_nonneg (show 1 ≤ 1 + 1 / (b / 2) by
        linarith only [one_div_pos.mpr (show 0 < b / 2 by positivity)])
      linarith only [hlogq, hn]
    calc
      _ ≤ Kb / g * (2 * u) ^ 3 := mul_le_mul
        (div_le_div_of_nonneg_left hKb.le hg hgb)
        (pow_le_pow_left₀ hbase0 hbase 3) (by positivity) (by positivity)
      _ = _ := by ring
  obtain ⟨W0, hWdim, _hW0, happ⟩ := hactual L q p r v hq hpr hrL hv Φ h0 h1
  intro delta hdelta hdelta1 a ψ hψG hψ
  obtain ⟨ell, hell, hwindow, hvec⟩ := happ delta hdelta hdelta1
  let D1 : ℕ := (q * ell ^ 2) ^ (22 * ell)
  obtain ⟨φ, hφ, hoverlap, hrank⟩ := hvec ψ hψG hψ
  have ha : 1 ≤ a := by
    have hl := Real.log_nonneg ((one_le_div hdelta).2 hdelta1)
    dsimp only [a]
    linarith only [hlogg, hl]
  let X := u ^ 3 / g
  let Y := (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u
  let P := 1 + Real.log a
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [Real.log_nonneg ha]
  have hXgrow : X ≤ (X + Y) * P := by
    nlinarith only [hY, mul_nonneg (add_nonneg hX hY) (sub_nonneg.mpr hP)]
  have hwindow' : (ell : ℝ) ≤
      10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    change (ell : ℝ) ≤ 8 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) at hwindow
    have hdiv : 8 / g ≤ 10 / g :=
      div_le_div_of_nonneg_right (by norm_num) hg.le
    linarith only [hwindow, hdiv]
  have hcount : Real.log (D1 : ℝ) ≤ kappa *
      (10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u * P :=
    Real.sharp_polynomial_family_log_count q ell g a beta
      (by omega) hell hg hg1 ha hbeta hwindow'
  have hucube : u ≤ u ^ 3 := by
    have hsq : 1 ≤ u ^ 2 := one_le_pow₀ hu
    nlinarith only [mul_le_mul_of_nonneg_left hsq hu0]
  have hpoly : (10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u ≤
      (11 + beta) * (X + Y) := by
    have hux : u / g ≤ X := div_le_div_of_nonneg_right hucube hg.le
    calc
      _ = 10 * (u / g) + beta * Y := by dsimp only [Y]; ring
      _ ≤ 10 * X + beta * Y := by linarith only [hux]
      _ ≤ (11 + beta) * (X + Y) := by
        nlinarith only [hX, hY, mul_nonneg hbeta hX]
  have hcountgrow : 2 * Real.log (D1 : ℝ) ≤
      2 * kappa * (11 + beta) * (X + Y) * P := by
    have hscale := mul_le_mul_of_nonneg_left hpoly hkappa.le
    have hscaleP := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hP)
    nlinarith only [hcount, hscaleP]
  refine ⟨φ, hφ, hoverlap, ?_⟩
  change Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
    Real.log (Module.finrank ℂ (G etaLD) : ℝ) + K * (X + Y) * P
  by_cases hzero : Matrix.schmidtRank (WithLp.ofLp (e φ)) = 0
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact add_nonneg (Real.log_natCast_nonneg _) (by positivity)
  · have hWpos : (0 : ℝ) < (Module.finrank ℂ W0 : ℝ) := by
      have hm : 0 < Module.finrank ℂ W0 * D1 ^ 2 :=
        (Nat.pos_of_ne_zero hzero).trans_le hrank
      exact_mod_cast Nat.pos_of_mul_pos_right hm
    have hrpos : (0 : ℝ) < (Module.finrank ℂ (G etaLD) : ℝ) :=
      pos_of_mul_pos_left (hWpos.trans_le hWdim) (Real.exp_pos _).le
    have hlogW : Real.log (Module.finrank ℂ W0 : ℝ) ≤
        Real.log (Module.finrank ℂ (G etaLD) : ℝ) + 8 * Kb * X := by
      have hl := Real.log_le_log hWpos hWdim
      rw [Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
      have hc : Kb / (b / 2) *
          (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 ≤ 8 * Kb * X := by
        calc
          _ ≤ 8 * Kb / g * u ^ 3 := hcost
          _ = _ := by dsimp only [X]; ring
      linarith only [hl, hc]
    have hbudget : Real.log ((Module.finrank ℂ W0 * D1 ^ 2 : ℕ) : ℝ) ≤
        Real.log (Module.finrank ℂ (G etaLD) : ℝ) + K * (X + Y) * P := by
      have hDpos : (0 : ℝ) < (D1 : ℝ) := by dsimp only [D1]; positivity
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hWpos.ne' (pow_pos hDpos 2).ne', Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      have hbasegrow := mul_le_mul_of_nonneg_left hXgrow (by positivity : 0 ≤ 8 * Kb)
      dsimp only [K]
      nlinarith only [hlogW, hcountgrow, hbasegrow]
    exact (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero)
      (by exact_mod_cast hrank)).trans hbudget

end TNLean.MPS.AreaLaw

end PhysicalLowDensitySharpApproximation

section PhysicalLowDensityGlobalApproximation

/-!
## One sharp matrix product approximation to an original low-energy vector

The fixed-cut approximants control the discarded mass of the actual original
marginals. One sequential product of their leading spectral projections is
then normalized. The resulting vector has simultaneous bond control at all
cuts, with the same three-quarter power of the logarithmic accuracy as the
fixed-cut estimate. The coefficient of the logarithm of the full low-energy
dimension is one.

This supports ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105.
No spectral gap or invariance of an original band is assumed.

**Scope restriction (physical intervals and fixed bandwidth):** The theorem
retains `q ≥ 2` and a coefficient for each fixed positive bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`. The effective width is
capped explicitly; the source comparison uses `0 < v ≤ etaLD`.
-/

open ManyBody (interval)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original buffered low-energy unit vector has one normalized
sequential MPS approximation, with the sharp logarithmic accuracy exponent
and one full-band multiplicity factor. ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_low_energy_normalized_isOpenMPS_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ) (v : ℝ) (hq : 2 ≤ q), 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1),
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
      let bcap := min v (etaLD / 2)
      let g := min (bcap / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ :=
    exists_fixed_bandwidth_interval_low_energy_normalized_approximation etaLD hLD
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q v hq hv Φ h0 h1 config H hH G bcap g u
  let : Nonempty (Fin L → Fin q) := config
  have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
    rw [← hi]
    exact hH.eigenvalues_mem_spectrum_real i
  have hGne : G etaLD ≠ ⊥ :=
    hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD])
  have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  intro delta hdelta hdelta1 b
  let deltaCut := delta / (16 * ((L : ℝ) + 1))
  have hden : 0 < 16 * ((L : ℝ) + 1) := by positivity
  have hcut : 0 < deltaCut := div_pos hdelta hden
  have hcut1 : deltaCut ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith only [hdelta1, hL]
  have hrecip : 1 / deltaCut = 16 * ((L : ℝ) + 1) / delta := by
    dsimp only [deltaCut]
    field_simp
  have hb : 16 ≤ b := by
    have hlogcut := Real.log_nonneg ((one_le_div hcut).2 hcut1)
    rw [hrecip] at hlogcut
    dsimp only [b]
    linarith only [hlogg, hlogcut]
  let F := u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u
  have hbase : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hroot : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by positivity
  have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by
    linarith only [hbase, hroot]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hF : 1 ≤ F := hsum
  have hPone : 1 ≤ 1 + Real.log b := by linarith only [hlogb]
  have hFP : 1 ≤ F * (1 + Real.log b) := by
    simpa only [one_mul] using
      (mul_le_mul hF hPone (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hF))
  let E := K * F * (1 + Real.log b)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hK.le (zero_le_one.trans hF))
    (zero_le_one.trans hPone)
  let B : ℕ := ⌈Real.exp E⌉₊
  obtain ⟨hB, hlogB⟩ := Real.log_ceil_exp_le_add_one E hE
  refine ⟨B, hB, ?_, ?_⟩
  · change Real.log (B : ℝ) ≤ (K + 1) * F * (1 + Real.log b)
    change Real.log (B : ℝ) ≤ E + 1 at hlogB
    dsimp only [E] at hlogB
    nlinarith only [hlogB, hFP]
  · intro ψ hψG hψ
    have htail : ∀ k ∈ Finset.Ico 1 L,
        1 - (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q)
          (leftBlock L k) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * B) ≤
            delta / (8 * ((L : ℝ) + 1)) := by
      intro k hk
      have hkL : k ≤ L := (Finset.mem_Ico.mp hk).2.le
      obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
        hfixed L q 0 k v hq (Nat.zero_le k) hkL hv Φ h0 h1
          deltaCut hcut hcut1 ψ hψG hψ
      rw [hrecip] at hlogrank
      have hregional := one_sub_regional_kyFanNorm_le_twice_error
        (interval L 0 k) ψ φ hφ deltaCut hcut1 (Module.finrank ℂ (G etaLD) * B)
        (Nat.le_mul_ceil_exp_of_log_le hrG E hlogrank) hoverlap
      rw [leftBlock_eq_interval]
      convert hregional using 1
      dsimp only [deltaCut]
      field_simp; ring
    exact exists_unit_mps_of_uniform_prefix_mass ψ hψ (Module.finrank ℂ (G etaLD) * B)
      delta hdelta hdelta1 htail

end TNLean.MPS.AreaLaw

end PhysicalLowDensityGlobalApproximation

section PositiveDimensionLowDensityGlobalApproximation

/-!
## Strict global low-energy MPS approximation in positive local dimension

For the scalar local space, the original unit vector already has a bond-one
representation. For local dimension at least two, retain the same actual
sequential projection construction at half the requested accuracy. The one
bond factor is still chosen before the vector. The strict overlap changes
only the fixed numerical factor inside the logarithm of the global accuracy.

This is the global approximation consequence of ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. Positive local
dimension is the qudit convention. The bandwidth is fixed before physical
data; the capped-width comparison is recorded in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)
open ManyBody (cutMatrix)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original buffered low-energy unit vector admits a strict-overlap
MPS approximation in every positive local dimension. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. The global accuracy
logarithm contains the explicit fixed factor 32. -/
theorem exists_fixed_bandwidth_low_energy_strict_isOpenMPS_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ) (v : ℝ) (hq : 0 < q), 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1),
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
      let bcap := min v (etaLD / 2)
      let g := min (bcap / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (32 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * B) (fun x ↦ Φ x) ∧
        1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 4 := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_low_energy_normalized_isOpenMPS_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q v hq hv Φ h0 h1 config H hH G bcap g u delta hdelta hdelta1 b
  by_cases hq2 : 2 ≤ q
  · obtain ⟨B, hB, hlogB, hvec⟩ :=
      hactual L q v hq2 hv Φ h0 h1
        (delta / 2) (by positivity) (by linarith only [hdelta1])
    have hscale : 16 * ((L : ℝ) + 1) / (delta / 2) =
        32 * ((L : ℝ) + 1) / delta := by field_simp; ring
    rw [hscale] at hlogB
    refine ⟨B, hB, hlogB, ?_⟩
    intro ψ hψG hψ
    obtain ⟨Φ, hΦ, hmps, hoverlap, hdist⟩ := hvec ψ hψG hψ
    refine ⟨Φ, hΦ, hmps, by linarith only [hoverlap, hdelta], ?_⟩
    linarith only [hdist]
  · have hq1 : q = 1 := by omega
    subst q
    let : Nonempty (Fin L → Fin 1) := config
    have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
    have hg1 : g ≤ 1 := min_le_right _ _
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hu : 0 ≤ u := by
      simp only [u, Nat.cast_one, Real.log_one, add_zero]
      linarith only [hlogg]
    have hden : delta ≤ 32 * ((L : ℝ) + 1) := by
      have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith only [hdelta1, hL]
    have hlogdelta : 0 ≤ Real.log (32 * ((L : ℝ) + 1) / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 hden)
    have hb : 1 ≤ b := by dsimp only [b]; linarith only [hlogg, hlogdelta]
    have hP : 0 ≤ 1 + Real.log b := by linarith only [Real.log_nonneg hb]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) := by positivity
    refine ⟨1, le_rfl, ?_, ?_⟩
    · simpa only [Nat.cast_one, Real.log_one] using hcost
    · intro ψ _hψG hψ
      have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
        obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
        rw [← hi]
        exact hH.eigenvalues_mem_spectrum_real i
      have hGne : G etaLD ≠ ⊥ :=
        hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD])
      have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
      have hmps : IsOpenMPS L 1 (Module.finrank ℂ (G etaLD) * 1) (fun x ↦ ψ x) := by
        apply isOpenMPS_of_cutMatrix_rank_le ψ
        intro k
        have hrank := Matrix.rank_le_card_height (cutMatrix (leftBlock L k) ψ)
        have hcard : Fintype.card
            (ManyBody.RegionConfig (fun _ ↦ Fin 1)
            (leftBlock L k)) = 1 := by simp [ManyBody.RegionConfig]
        rw [hcard] at hrank
        simpa only [mul_one] using hrank.trans hrG
      refine ⟨ψ, hψ, hmps, ?_, ?_⟩
      · have hi : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
        rw [hi]
        linarith only [hdelta]
      · simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        positivity

end TNLean.MPS.AreaLaw

end PositiveDimensionLowDensityGlobalApproximation
