/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.ShortRegionViableFamily
import QICLean.Analysis.Subspace.ViableSubspace
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.DyadicRegionalLowDensityWordFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalIntervalTransport
import QICLean.Spectral.LowEnergy.ShiftedLowEnergyCoordinates
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.Probability.Sampling.ViableSubspaceBootstrap

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
result retains `4*ell < r-p`; short intervals are treated by actual
configuration matrix units in the subsequent interval theorem.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_interval_dyadic_low_energy_family`: dyadic low-energy
  improving families on every prescribed interval.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family`,
  `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_long_interval_dyadic_low_energy_family`: dyadic
  low-energy improving families on long prescribed intervals.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_interval_low_energy_family`: low-energy improving
  families on every prescribed interval.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_interval_low_energy_dyadic_refinement`: actual
  refinement between original low-energy targets.
-/

section DyadicLongIntervalLowDensityFamily

/-!
## Dyadic low-energy improving families on long prescribed intervals

Inward effective cuts remove at most two window lengths from a prescribed
interval. The exact polynomial family of the same global clipped matrix
is decomposed on the prescribed region, with the collar cost absorbed in
the same numerical count used for suppression. Scalar shifts are removed
using the original Hamiltonian's canonical minimum. Zero extension retains
the same image spans and gives exactly the required squared count.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041. The fixed bandwidth is explicit. This long-interval
result retains `4*ell < r-p` at each dyadic index. Its original/clipped
comparison loss is `1 / (200 * 2^(4*i))`. Short intervals are treated by actual
configuration matrix units in the subsequent interval theorem.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The actual regional tensor decompositions have dependent finite configuration types.
/-- A fixed-bandwidth low-energy family on every sufficiently long prescribed
interval, including intervals touching the chain boundary. The inward cuts
and collar cardinality are constructed, and the same actual global clipped
polynomial supplies all regional factors. The original targets use the raw
Hamiltonian's canonical energy normalization. The family is recorded with
its own count `N ≤ D ^ 2`, and every word of length `a` improves the upper
target to the lower one with suppression `Delta ^ a`, as for the repeated
filter of Theorem `t:alg1`, lines 1777–1817, used by Theorem `t:alg2`,
lines 1869–1878. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r i : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let nu := (1 / 200 : ℝ) / 2 ^ (4 * i)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      ∀ _hlong : 4 * ell < r - p,
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      ∃ (N : ℕ) (F : Fin N → EM →L[ℂ] EM), N ≤ D ^ 2 ∧
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
          Tlo ≤ Thi ∧
          Submodule.IsCloseTo nu
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta)) Thi ∧
          Submodule.IsCloseTo nu Tlo
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta - 3 * w)) ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
          ∀ (a : ℕ) (S : Submodule ℂ EM) (delta : ℝ),
            Submodule.IsViable (F := EE) delta S (Thi.map Tm.toLinearEquiv.toLinearMap) →
            delta < 1 →
            let grow := ⨆ v : Fin a → Fin N,
              S.map ((List.ofFn (fun j ↦ F (v j))).prod : EM →ₗ[ℂ] EM)
            Module.finrank ℂ grow ≤ N ^ a * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EE) (Delta ^ a / (1 - delta) ^ 2)
                grow (Tlo.map Tm.toLinearEquiv.toLinearMap):= by
  classical
  obtain ⟨C, hC, hCeta, hregional⟩ :=
    exists_fixed_bandwidth_regional_dyadic_low_energy_word_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r i w hq hqm hpr hrL hw mi g u ell D nu Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, _⟩ := hregional L q m 0 0 i w hq hqm hw
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
  obtain ⟨_, _, hphysical⟩ := hregional L q m a b i w hq hqm hw
  obtain ⟨e, E0, _x, z, hO, hClip, _hxunit, _hx, _hlo, hcenter, hzunit, hz, hE0low,
    _hE0, _hE04, _hnorm, hfamilies⟩ := hphysical hab hbL J hcost Φ h0 h1
  obtain ⟨_hminimum, hidentity⟩ :=
    hRaw.spectralSpanLE_centered_ground_of_eq hO (∑ j, e j) E0 z
      hcenter hzunit hz hE0low
  obtain ⟨N, W, hN, hfilters⟩ := hfamilies
  let F : Fin N → EM →L[ℂ] EM := fun i ↦
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W i)
  refine ⟨N, F, hN, ?_⟩
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
  · intro a S delta hS hdelta
    exact himprove a S delta hS hdelta

/-- A fixed-bandwidth low-energy family on every sufficiently long prescribed
interval, including intervals touching the chain boundary. The inward cuts
and collar cardinality are constructed, and the same actual global clipped
polynomial supplies all regional factors. The original targets use the raw
Hamiltonian's canonical energy normalization. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_long_interval_dyadic_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r i : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let nu := (1 / 200 : ℝ) / 2 ^ (4 * i)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      ∀ _hlong : 4 * ell < r - p,
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      ∃ A : Fin (D ^ 2) → EM →L[ℂ] EM,
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
          Tlo ≤ Thi ∧
          Submodule.IsCloseTo nu
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta)) Thi ∧
          Submodule.IsCloseTo nu Tlo
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
  obtain ⟨C, hC, hCeta, hword⟩ :=
    exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r i w hq hqm hpr hrL hw mi g u ell D nu Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, hrest⟩ := hword L q m p r i w hq hqm hpr hrL hw Φ h0 h1
  refine ⟨hell, hlogD, ?_⟩
  intro hlong J beta tau U Phi Tm EM EE
  obtain ⟨N, F, hN, hfamily⟩ := hrest hlong
  have hcard : Fintype.card (Fin N) ≤ D ^ 2 := by simpa only [Fintype.card_fin] using hN
  obtain ⟨_f, A, _hA, _hzero, hspan⟩ :=
    Submodule.exists_clm_family_extension_of_card_le hcard F
  refine ⟨A, fun eta hbuffer hetaLD ↦ ?_⟩
  obtain ⟨Tlo, Thi, Delta, hnest, hupper, hlower, hDelta, htrade, hwords⟩ :=
    hfamily eta hbuffer hetaLD
  refine ⟨Tlo, Thi, Delta, hnest, hupper, hlower, hDelta, htrade, fun S delta hS hdelta ↦ ?_⟩
  obtain ⟨_hdim, hviable⟩ := hwords 1 S delta hS hdelta
  rw [Submodule.iSup_map_ofFn_prod_fin_one F S, pow_one] at hviable
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap)
  · rw [hspan S]
    exact hviable

end TNLean.MPS.AreaLaw

end DyadicLongIntervalLowDensityFamily

section LongIntervalLowDensityFamily

open ManyBody (interval)

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
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      ∀ _hlong : 4 * ell < r - p,
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
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
  obtain ⟨C, hC, hCeta, hlong⟩ :=
    exists_fixed_bandwidth_long_interval_dyadic_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r w hq hqm hpr hrL hw
  have h := hlong L q m p r 0 w hq hqm hpr hrL hw
  rw [show m * 2 ^ (0 : ℕ) = m by simp] at h
  rw [show (1 / 200 : ℝ) / 2 ^ (4 * (0 : ℕ)) = 1 / 200 by norm_num] at h
  exact h

end TNLean.MPS.AreaLaw

end LongIntervalLowDensityFamily

section DyadicIntervalLowDensityFamily

/-!
## Dyadic low-energy improving families on every prescribed interval

A single fixed-bandwidth scale treats every physical interval, including
short intervals and intervals meeting the chain endpoints. Long intervals
use the same global clipped polynomial and its exact regional factors;
short intervals use actual configuration matrix units. Both cases retain
the same count envelope and suppression budget. The comparison loss decreases
as `1 / (200 * 2^(4*i))` at the enlarged numerical bases. All original targets use
the raw Hamiltonian's canonical energy normalization.

This is the physical improving-family construction supporting ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, with the fixed
bandwidth of Assumption (LD), lines 281–284. No spectral gap or supplied
operator, residual, rank or probability premise is imposed. The subsequent
strict low-density dimension argument is separate.

**Scope restriction (nontrivial local dimension):** The statement retains
`q ≥ 2`. The scalar local space is a separate elementary case;
see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (card_interval_le interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The long and short cases share dependent physical configuration coordinates.
/-- An actual improving family on every prescribed interval, for all buffered
cutoffs within a fixed bandwidth. The constant precedes every physical datum;
the same family is chosen before every cutoff and viable subspace. Inward
cuts and short-region matrix units discharge all geometric alternatives.
Both cases use the same count and suppression envelope and the same original
canonical Hamiltonian targets. ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_interval_dyadic_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r i : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let nu := (1 / 200 : ℝ) / 2 ^ (4 * i)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      ∃ A : Fin (D ^ 2) → EM →L[ℂ] EM,
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
          Tlo ≤ Thi ∧
          Submodule.IsCloseTo nu
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta)) Thi ∧
          Submodule.IsCloseTo nu Tlo
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
  obtain ⟨C, hC, hCeta, hlong⟩ :=
    exists_fixed_bandwidth_long_interval_dyadic_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r i w hq hqm hpr hrL hw mi g u ell D nu
  have hmmi : m ≤ mi := Nat.le_mul_of_pos_right m (pow_pos (by decide) i)
  have hqmi : q ≤ mi := hqm.trans hmmi
  have hnu : 0 ≤ nu := by dsimp only [nu]; positivity
  intro Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, hfamily⟩ := hlong L q m p r i w hq hqm hpr hrL hw Φ h0 h1
  refine ⟨hell, hlogD, ?_⟩
  intro J beta tau U Phi Tm EM EE
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell := (card_interval_le (L := L) p r).trans hshort
    obtain ⟨A, Delta, hDelta, htrade, himprove⟩ :=
      exists_short_actual_region_improving_family_of_count_base (F := EE)
        L q mi ell J hq hqmi ((by decide : 1 ≤ 21).trans hell) hJ
    refine ⟨A, ?_⟩
    intro eta _hbuffer _hetaLD
    let Gup := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
      (minEigenvalue hRaw + eta)
    let Glow := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
      (minEigenvalue hRaw + eta - 3 * w)
    have hle : Glow ≤ Gup := Submodule.span_mono
      (Set.image_mono (fun _ hi ↦ hi.trans
        (show minEigenvalue hRaw + eta - 3 * w ≤ minEigenvalue hRaw + eta by
          linarith only [hw])))
    have hGG : Submodule.IsCloseTo nu Gup Gup :=
      Submodule.isCloseTo_of_le hnu le_rfl
    have hGL : Submodule.IsCloseTo nu Gup Glow :=
      Submodule.isCloseTo_of_le hnu hle
    refine ⟨Gup, Gup, Delta, le_rfl, hGG, hGL, hDelta, htrade, ?_⟩
    intro S delta hS hdelta
    refine ⟨?_, himprove (Gup.map Tm.toLinearEquiv.toLinearMap) S delta hS hdelta⟩
    simpa only [Fintype.card_fin] using
      Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap)
  · exact hfamily (Nat.lt_of_not_ge hshort)

end TNLean.MPS.AreaLaw

end DyadicIntervalLowDensityFamily

section IntervalLowDensityFamily

/-!
## Low-energy improving families on every prescribed interval

A single fixed-bandwidth scale treats every physical interval, including
short intervals and intervals meeting the chain endpoints. Long intervals
use the same global clipped polynomial and its exact regional factors;
short intervals use actual configuration matrix units. Both cases retain
the same count envelope and suppression budget. All original targets use
the raw Hamiltonian's canonical energy normalization.

This is the physical improving-family construction supporting ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, with the fixed
bandwidth of Assumption (LD), lines 281–284. No spectral gap or supplied
operator, residual, rank or probability premise is imposed. The subsequent
strict low-density dimension argument is separate.

**Scope restriction (nontrivial local dimension):** The statement retains
`q ≥ 2`. The scalar local space is a separate elementary case;
see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The long and short cases share dependent physical configuration coordinates.
/-- An actual improving family on every prescribed interval, for all buffered
cutoffs within a fixed bandwidth. The constant precedes every physical datum;
the same family is chosen before every cutoff and viable subspace. Inward
cuts and short-region matrix units discharge all geometric alternatives.
Both cases use the same count and suppression envelope and the same original
canonical Hamiltonian targets. ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_interval_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
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
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_interval_dyadic_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r w hq hqm hpr hrL hw
  have h := hfamily L q m p r 0 w hq hqm hpr hrL hw
  rw [show m * 2 ^ (0 : ℕ) = m by simp] at h
  rw [show (1 / 200 : ℝ) / 2 ^ (4 * (0 : ℕ)) = 1 / 200 by norm_num] at h
  exact h

end TNLean.MPS.AreaLaw

end IntervalLowDensityFamily

section LowDensityAccurateViability

/-!
## Actual refinement between original low-energy targets

The accurate interval families send one constant-viable regional space for
an original upper target to actual image spaces with geometrically decreasing
error for the original lower target. Both transfers use the proved physical
original-to-clipped comparisons. No invariance of an original spectral band
under a clipped polynomial is asserted.

This is an auxiliary to ALVV, arXiv:1602.08828v2, the entropy argument for
Theorem `thm:al-ld`, lines 1096–1105, using the improving-family construction
at lines 1027–1041. The bandwidth is fixed as in Assumption (LD), lines 281–284.

**Scope restriction (nontrivial local dimension):** The theorem retains
`q ≥ 2`; see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

-- The actual interval's tensor coordinates depend on its finite configuration types.
/-- A single constructed regional operator family refines every constant-viable
source for the original upper band to an actual image viable for the original
lower band. The error is dyadic in the numerical accuracy index. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_dyadic_refinement
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r i : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∃ A : Fin (D ^ 2) → EM →L[ℂ] EM,
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∀ S : Submodule ℂ EM,
          Submodule.IsViable (F := EE) (3 / 200) S
            ((G eta).map Tm.toLinearEquiv.toLinearMap) →
          let grow := ⨆ j : Fin (D ^ 2), S.map (A j).toLinearMap
          Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EE) (1 / (2 : ℝ) ^ (i + 1))
              grow ((G (eta - 3 * w)).map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_interval_dyadic_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r i w hq hqm hpr hrL hw mi g u ell D
  let nu := (1 / 200 : ℝ) / 2 ^ (4 * i)
  intro Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, A, hA⟩ := hfamily L q m p r i w hq hqm hpr hrL hw Φ h0 h1
  refine ⟨hell, hlogD, ?_⟩
  intro J beta tau U Phi Tm EM EE G
  have hell1 : 1 ≤ ell := (by decide : 1 ≤ 21).trans hell
  have hmiD : mi ≤ D := by
    have hfirst : mi ≤ mi * ell ^ 2 :=
      Nat.le_mul_of_pos_right mi (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hell1) 2)
    exact hfirst.trans (Nat.le_self_pow (by omega : 22 * ell ≠ 0) _)
  have htwoD : 2 ^ i ≤ D := by
    have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) (hq.trans hqm)
    have hfirst : 2 ^ i ≤ mi := by
      simpa only [mi, mul_comm] using Nat.le_mul_of_pos_right (2 ^ i) hmpos
    exact hfirst.trans hmiD
  have hx : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) i
  have hpow : (2 : ℝ) ^ i ≤ 2 ^ (4 * i) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnu : nu ≤ 1 / (200 * (2 : ℝ) ^ i) := by
    dsimp only [nu]
    calc
      (1 / 200 : ℝ) / 2 ^ (4 * i) ≤ (1 / 200 : ℝ) / 2 ^ i :=
        div_le_div_of_nonneg_left (by norm_num) hx hpow
      _ = 1 / (200 * (2 : ℝ) ^ i) := by ring
  have hnuSmall : nu ≤ (1 / 200 : ℝ) := by
    have hpow1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    exact hnu.trans ((div_le_iff₀ (by positivity)).mpr (by linarith only [hpow1]))
  refine ⟨A, ?_⟩
  intro eta hbuffer heta S hS
  obtain ⟨Tlo, Thi, Delta, _hsub, hupper, hlower, _hDelta, hbudget, himprove⟩ :=
    hA eta hbuffer heta
  have hupperMap := (Submodule.isCloseTo_map_iff Tm).mpr hupper
  have hlowerCanonical : Submodule.IsCloseTo nu Tlo (G (eta - 3 * w)) := by
    simpa only [G, add_sub_assoc] using hlower
  have hlowerMap := (Submodule.isCloseTo_map_iff Tm).mpr hlowerCanonical
  have hstart : Submodule.IsViable (F := EE) (1 / 25) S
      (Thi.map Tm.toLinearEquiv.toLinearMap) :=
    (Submodule.IsCloseTo.trans hS hupperMap (by norm_num)).of_le
      (by linarith only [hnuSmall])
  obtain ⟨hdim, hraw⟩ := himprove S (1 / 25) hstart (by norm_num)
  have hshrink : Delta / (1 - (1 / 25 : ℝ)) ^ 2 ≤
      1 / (8 * (2 : ℝ) ^ i) := by
    have hb : (D : ℝ) ^ 12 * Delta ≤ 0.00001 := by
      simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
    simpa only [Nat.cast_pow, Nat.cast_ofNat,
      show (0.04 : ℝ) = 1 / 25 by norm_num] using
      Submodule.improving_error_le_inverse_scale (2 ^ i) D Delta
        (Nat.one_le_pow i 2 (by decide)) htwoD hb
  have himproved := hraw.of_le hshrink
  have hfinal : 2 * (1 / (8 * (2 : ℝ) ^ i) + nu) ≤
      1 / (2 : ℝ) ^ (i + 1) := by
    calc
      2 * (1 / (8 * (2 : ℝ) ^ i) + nu) ≤
          2 * (1 / (8 * (2 : ℝ) ^ i) + 1 / (200 * (2 : ℝ) ^ i)) := by
            linarith only [hnu]
      _ = (13 / 50 : ℝ) * ((2 : ℝ) ^ i)⁻¹ := by
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
      _ ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ i)⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hx.le)
      _ = 1 / (2 : ℝ) ^ (i + 1) := by
        rw [pow_succ]
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
  exact ⟨hdim, (Submodule.IsCloseTo.trans himproved hlowerMap (by positivity)).of_le hfinal⟩

end TNLean.MPS.AreaLaw

end LowDensityAccurateViability
