/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.PhysicalLowDensitySharpApproximation
import TNLean.MPS.Tensor.OpenMPS.NormalizedSequentialApproximation
import QICLean.Analysis.Real.LogRankRounding
import TNLean.MPS.Tensor.OpenMPS.OpenMPSCutRank
import QICLean.Analysis.Subspace.ViableSubspace

/-!
# Strict fixed-cut approximation in positive local dimension

The scalar local space is handled by its exact rank-one representation.
In local dimension at least two, use the same actual physical construction
at half the requested accuracy. This makes the overlap strict and changes
only the fixed numerical factor inside the accuracy logarithm.

The statement is the fixed-cut consequence of ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105, with the usual positive local-dimension
convention and fixed bandwidth. Its capped-width comparison is recorded in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_low_energy_designated_isOpenMPS_approximation`: one
  low-energy approximant with a sharp designated cut and global MPS bounds.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_low_energy_orthonormal_mps_basis`: a matrix product
  basis for an approximation to an original low-energy band.
-/

open ManyBody (interval)

section PositiveDimensionLowDensityApproximation

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Positive local dimension suffices for the sharp fixed-cut rank bound
with strict overlap. ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`,
lines 1096–1105. The accuracy logarithm contains the explicit factor two. -/
theorem exists_fixed_bandwidth_interval_low_energy_strict_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 0 < q), p ≤ r → r ≤ L → 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ h0 : ∀ i, 0 ≤ Φ.term i, (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
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
      let a := 16 + Real.log (1 / g) + Real.log (2 / delta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta < ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_interval_low_energy_normalized_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw
    J beta tau U Phi Tm G e b g u delta hdelta hdelta1 a ψ hψG hψ
  by_cases hq2 : 2 ≤ q
  · obtain ⟨φ, hφ, hoverlap, hrank⟩ :=
      hactual L q p r v hq2 hpr hrL hv Φ h0 h1
        (delta / 2) (by positivity) (by linarith only [hdelta1]) ψ hψG hψ
    have hrecip : 1 / (delta / 2) = 2 / delta := by field_simp
    rw [hrecip] at hrank
    exact ⟨φ, hφ, by linarith only [hoverlap, hdelta], hrank⟩
  · have hq1 : q = 1 := by omega
    subst q
    have hg : 0 < g := lt_min (by dsimp only [b]; positivity) (by norm_num)
    have hg1 : g ≤ 1 := min_le_right _ _
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hu : 0 ≤ u := by
      simp only [u, Nat.cast_one, Real.log_one, add_zero]
      linarith only [hlogg]
    have hlogdelta : 0 ≤ Real.log (2 / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 (by linarith only [hdelta1]))
    have ha : 1 ≤ a := by dsimp only [a]; linarith only [hlogg, hlogdelta]
    have hP : 0 ≤ 1 + Real.log a := by linarith only [Real.log_nonneg ha]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) := by positivity
    have hrank : Matrix.schmidtRank (WithLp.ofLp (e ψ)) ≤ 1 := by
      have h := Matrix.schmidtRank_le_left (WithLp.ofLp (e ψ))
      simpa only [Fintype.card_fun, Fintype.card_fin, one_pow] using h
    refine ⟨ψ, hψ, ?_, ?_⟩
    · have hi : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
      rw [hi]
      linarith only [hdelta]
    · exact (Real.log_nonpos (Nat.cast_nonneg _) (by exact_mod_cast hrank)).trans
        (add_nonneg (Real.log_natCast_nonneg _) hcost)

end TNLean.MPS.AreaLaw

end PositiveDimensionLowDensityApproximation

section LowDensityDesignatedApproximation

/-!
## One low-energy approximant with a sharp designated cut and global MPS bounds

The designated cut uses a constant fraction of the error budget; all other
cuts share a length-dependent budget. Their actual leading marginal
projections form one sequential product. Normalizing that product retains
both the sharper designated-cut rank and the global matrix product bound.

This proves the simultaneous-witness approximation conclusion of ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105, in positive
local dimension. The bandwidth is fixed as in Assumption (LD), lines
281–284. All original-band comparisons and polynomial-family bounds are
derived physically by the imported fixed-cut theorem; no raw-band gap or
invariance is assumed. The capped-width comparison is documented in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (cutMatrix)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- One actual normalized sequential MPS satisfies the sharp rank bound at
any designated cut and the global bond bound simultaneously. Both integer
factors are chosen before the designated cut and vector. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_low_energy_designated_isOpenMPS_approximation
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
      let a := 16 + Real.log (1 / g) + Real.log (128 / delta)
      let b := 16 + Real.log (1 / g) + Real.log (128 * ((L : ℝ) + 1) / delta)
      ∃ Bs Bg : ℕ, 1 ≤ Bs ∧ Bs ≤ Bg ∧
        Real.log (Bs : ℝ) ≤
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) ∧
        Real.log (Bg : ℝ) ≤
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log b) ∧
      ∀ (k0 : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q)),
        ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * Bg) (fun x ↦ Φ x) ∧
        (cutMatrix (interval L 0 k0) Φ).rank ≤ Module.finrank ℂ (G etaLD) * Bs ∧
        1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ :=
    exists_fixed_bandwidth_interval_low_energy_strict_approximation etaLD hLD
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q v hq hv Φ h0 h1 config H hH G bcap g u
  let : Nonempty (Fin L → Fin q) := config
  have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogg, hlogq]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hX : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
    rw [← hi]
    exact hH.eigenvalues_mem_spectrum_real i
  have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD]))
  intro delta hdelta hdelta1 a b
  let F : ℝ → ℝ := fun x ↦ K *
    (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) * (1 + Real.log x)
  have hF0 {x : ℝ} (hx : 1 ≤ x) : 0 ≤ F x := by
    have hP : 0 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    dsimp only [F]
    positivity
  have hFmono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : F x ≤ F y := by
    have hy : 1 ≤ y := hx.trans hxy
    have hpow := Real.rpow_le_rpow (zero_le_one.trans hx) hxy (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hlog := Real.log_le_log (zero_lt_one.trans_le hx) hxy
    have hleft : u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u ≤
        u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) * u := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (1 / g) ^ (1 / 4 : ℝ))) hu0
      linarith only [hm]
    have hPx : 0 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    have hY : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) * u) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hleft hK.le)
      (by linarith only [hlog]) hPx hY
  have ha : 16 ≤ a := by
    have hl : 0 ≤ Real.log (128 / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 (by linarith only [hdelta1]))
    dsimp only [a]
    linarith only [hlogg, hl]
  have hab : a ≤ b := by
    have harg : 128 / delta ≤ 128 * ((L : ℝ) + 1) / delta :=
      div_le_div_of_nonneg_right
        (by nlinarith only [show 0 ≤ (L : ℝ) from Nat.cast_nonneg L]) hdelta.le
    have hl := Real.log_le_log (by positivity : 0 < 128 / delta) harg
    dsimp only [a, b]
    linarith only [hl]
  have hb : 16 ≤ b := ha.trans hab
  have hround {x : ℝ} (hx : 1 ≤ x) :
      1 ≤ ⌈Real.exp (F x)⌉₊ ∧ Real.log (⌈Real.exp (F x)⌉₊ : ℕ) ≤
        (K + 1) * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log x) := by
    obtain ⟨hB, hlog⟩ := Real.log_ceil_exp_le_add_one (F x) (hF0 hx)
    have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u := by
      have hy : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u := by positivity
      linarith only [hX, hy]
    have hP : 1 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    have hprod : 1 ≤ (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log x) := by
      simpa only [one_mul] using
        mul_le_mul hsum hP (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hsum)
    refine ⟨hB, ?_⟩
    dsimp only [F] at hlog
    nlinarith only [hlog, hprod]
  let Bs : ℕ := ⌈Real.exp (F a)⌉₊
  let Bg : ℕ := ⌈Real.exp (F b)⌉₊
  obtain ⟨hBs, hlogs⟩ := hround (show 1 ≤ a by linarith only [ha])
  obtain ⟨_hBg, hloggBound⟩ := hround (show 1 ≤ b by linarith only [hb])
  have hBsg : Bs ≤ Bg := Nat.ceil_mono
    (Real.exp_le_exp.mpr (hFmono (by linarith only [ha]) hab))
  refine ⟨Bs, Bg, hBs, hBsg, hlogs, hloggBound, ?_⟩
  intro k0 ψ hψG hψ
  have hmassAt (k : ℕ) (hkL : k ≤ L) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
      1 - (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q)
        (interval L 0 k) ψ).kyFanNorm
          (Module.finrank ℂ (G etaLD) *
            ⌈Real.exp (F (16 + Real.log (1 / g) + Real.log (2 / eps)))⌉₊) ≤ 2 * eps := by
    obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
      hfixed L q 0 k v hq (Nat.zero_le k) hkL hv Φ h0 h1 eps heps heps1 ψ hψG hψ
    have hregional := one_sub_regional_kyFanNorm_le_twice_error
      (interval L 0 k) ψ φ hφ eps heps1
      (Module.finrank ℂ (G etaLD) *
        ⌈Real.exp (F (16 + Real.log (1 / g) + Real.log (2 / eps)))⌉₊)
      (Nat.le_mul_ceil_exp_of_log_le hrG _ hlogrank) hoverlap.le
    exact hregional
  have hDs : 1 ≤ Module.finrank ℂ (G etaLD) * Bs := by
    simpa only [one_mul] using Nat.mul_le_mul hrG hBs
  apply exists_unit_mps_of_designated_prefix_mass ψ hψ k0
    (Module.finrank ℂ (G etaLD) * Bs) (Module.finrank ℂ (G etaLD) * Bg)
    hDs (Nat.mul_le_mul_left _ hBsg) delta hdelta hdelta1
  · intro hk0
    have hm := hmassAt k0 (Finset.mem_Ico.mp hk0).2.le (delta / 64)
      (by positivity) (by linarith only [hdelta1])
    have heq : 2 / (delta / 64) = 128 / delta := by field_simp; ring
    rw [heq] at hm
    change 1 - (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q)
      (interval L 0 k0) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * Bs) ≤ _ at hm
    convert hm using 1; ring
  · intro k hk _hne
    have hden : 0 < 64 * ((L : ℝ) + 1) := by positivity
    have heps1 : delta / (64 * ((L : ℝ) + 1)) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith only [hdelta1, hL]
    have hm := hmassAt k (Finset.mem_Ico.mp hk).2.le
      (delta / (64 * ((L : ℝ) + 1))) (by positivity) heps1
    have heq : 2 / (delta / (64 * ((L : ℝ) + 1))) =
        128 * ((L : ℝ) + 1) / delta := by field_simp; ring
    rw [heq] at hm
    change 1 - (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q)
      (interval L 0 k) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * Bg) ≤ _ at hm
    convert hm using 1; field_simp; ring

end TNLean.MPS.AreaLaw

end LowDensityDesignatedApproximation

section LowEnergyMPSBasis

/-!
## A matrix product basis for an approximation to an original low-energy band

A common rank factor is chosen before an orthonormal basis of the actual
inner band. Approximate its basis vectors with the proved physical MPS
construction, then take the actual linear image of that basis. Summed
squared errors prove injectivity, the exact dimension, and closeness in
both directions. Every vector of the resulting space is a linear
combination of the same MPS family. Its actual standard orthonormal basis
therefore has the additional honest generator-count bond factor.

This is a mathematical basis-existence consequence of ALVV,
arXiv:1602.08828v2, introductory statement at line 288 and Theorem
`thm:al-ld`, lines 1096–1105. It is not the probabilistic efficient
algorithm in Theorem `t:alg2`, lines 1869–1874, and makes no running-time
or energy-eigenstate assertion. The zero inner band, scalar local space
and empty chain are included.
-/

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- The actual basis-defined linear image of the original inner band has
its exact dimension, approximates it in both directions, and has a native
orthonormal MPS basis. The factor is chosen before the basis and vectors.
Mathematical basis consequence of ALVV, arXiv:1602.08828v2, line 288 and
Theorem `thm:al-ld`, lines 1096–1105; no algorithmic conclusion is claimed. -/
theorem exists_fixed_bandwidth_low_energy_orthonormal_mps_basis
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
      let rInner := Module.finrank ℂ (G (etaLD - v))
      let rOuter := Module.finrank ℂ (G etaLD)
      let g := min (min v (etaLD / 2) / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let eps := delta / (8 * ((rInner : ℝ) + 1))
      let a := 16 + Real.log (1 / g) +
        Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) ∧
      let targetBasis := stdOrthonormalBasis ℂ (G (etaLD - v))
      ∃ phi : Fin rInner → EuclideanSpace ℂ (Fin L → Fin q),
        (∀ i, ‖phi i‖ = 1 ∧ IsOpenMPS L q (rOuter * B) (fun x ↦ phi i x) ∧
          ‖phi i - (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ eps / 2) ∧
      let F := targetBasis.toBasis.constr ℂ phi
      let V := LinearMap.range F
      Function.Injective F ∧ Module.finrank ℂ V = rInner ∧ Module.finrank ℂ V ≤ rOuter ∧
        V = Submodule.span ℂ (Set.range phi) ∧
        Submodule.IsCloseTo delta V (G (etaLD - v)) ∧
        Submodule.IsCloseTo delta (G (etaLD - v)) V ∧
        Submodule.IsCloseTo delta (G etaLD) V ∧
        (∀ x ∈ V, IsOpenMPS L q (rInner * rOuter * B) (fun w ↦ x w)) ∧
      let basis := stdOrthonormalBasis ℂ V
      ∀ i, IsOpenMPS L q (rInner * rOuter * B)
        (fun w ↦ (basis i : EuclideanSpace ℂ (Fin L → Fin q)) w) := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_low_energy_designated_isOpenMPS_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q v hq hv Φ h0 h1 config H hH G rInner rOuter g u
    delta hdelta hdelta1 eps a
  let : Nonempty (Fin L → Fin q) := config
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heps1 : eps ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((rInner : ℝ) + 1))).2
    have hn : 0 ≤ (rInner : ℝ) := Nat.cast_nonneg rInner
    linarith only [hdelta1, hn]
  obtain ⟨Bs, B, hBs, hBsg, _hlogs, hlogB, hvec⟩ :=
    hactual L q v hq hv Φ h0 h1 eps heps heps1
  have hscale : 128 * ((L : ℝ) + 1) / eps =
      1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / delta := by
    dsimp only [eps]
    field_simp
    ring
  rw [hscale] at hlogB
  refine ⟨B, hBs.trans hBsg, hlogB, ?_⟩
  intro targetBasis
  have happrox (i : Fin rInner) :
      ∃ x : EuclideanSpace ℂ (Fin L → Fin q), ‖x‖ = 1 ∧
        IsOpenMPS L q (rOuter * B) (fun w ↦ x w) ∧
        ‖x - (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ eps / 2 := by
    have hn : ‖(targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ = 1 :=
      targetBasis.norm_eq_one i
    obtain ⟨x, hx, hmps, _hrank, _hoverlap, hdist⟩ :=
      hvec 0 (targetBasis i) (targetBasis i).property hn
    exact ⟨x, hx, hmps, hdist⟩
  choose phi hnorm hmps herr using happrox
  refine ⟨phi, fun i ↦ ⟨hnorm i, hmps i, herr i⟩, ?_⟩
  intro F V
  have hsum : (∑ i, ‖phi i -
      (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2) ≤ delta / 16 := by
    calc
      _ ≤ ∑ _i : Fin rInner, eps / 2 := Finset.sum_le_sum fun i _ ↦ herr i
      _ = (rInner : ℝ) * (eps / 2) := by simp
      _ = ((rInner : ℝ) * delta) / (16 * ((rInner : ℝ) + 1)) := by
        dsimp only [eps]
        field_simp
        ring
      _ ≤ delta / 16 := by
        apply (div_le_iff₀ (by positivity : 0 < 16 * ((rInner : ℝ) + 1))).2
        nlinarith only [hdelta]
  obtain ⟨hinj, hdim, hspan, hVT, hTV⟩ :=
    OrthonormalBasis.range_constr_isCloseTo_of_sum_norm_sq_le (G (etaLD - v))
      targetBasis phi (delta / 16) (by linarith only [hdelta1]) hsum
  have hmono : G (etaLD - v) ≤ G etaLD :=
    Submodule.spectralSpanLE_mono_cutoff hH.eigenvectorBasis hH.eigenvalues
      (by linarith only [hv])
  have hforward : Submodule.IsCloseTo delta V (G (etaLD - v)) :=
    hVT.of_le (by linarith only [hdelta])
  have hback : Submodule.IsCloseTo delta (G (etaLD - v)) V :=
    hTV.of_le (by linarith only [hdelta])
  have hall : ∀ x ∈ V, IsOpenMPS L q (rInner * rOuter * B) (fun w ↦ x w) := by
    intro x hx
    let R : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] ((Fin L → Fin q) → ℂ) :=
      (WithLp.linearEquiv 2 ℂ ((Fin L → Fin q) → ℂ)).toLinearMap
    have hxspan : x ∈ Submodule.span ℂ (Set.range phi) := by
      rw [← hspan]
      exact hx
    have hxread : R x ∈ Submodule.span ℂ (Set.range (fun i ↦ R (phi i))) := by
      simpa only [← Set.range_comp, Function.comp_def] using
        Submodule.apply_mem_span_image_of_mem_span R hxspan
    simpa [R, Nat.mul_assoc] using
      isOpenMPS_of_mem_span_range (fun i ↦ R (phi i)) hmps hxread
  refine ⟨hinj, hdim, ?_, hspan, hforward, hback, hback.mono hmono, hall, ?_⟩
  · rw [hdim]
    exact Submodule.finrank_mono hmono
  · intro basis i
    exact hall (basis i) (basis i).property

end TNLean.MPS.AreaLaw

end LowEnergyMPSBasis
