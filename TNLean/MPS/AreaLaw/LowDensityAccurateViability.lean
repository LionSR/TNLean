/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DyadicIntervalLowDensityFamily
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# Actual refinement between original low-energy targets

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
  intro h hs h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, A, hA⟩ := hfamily L q m p r i w hq hqm hpr hrL hw h hs h0 h1
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
