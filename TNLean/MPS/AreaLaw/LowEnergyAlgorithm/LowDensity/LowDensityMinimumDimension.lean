/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LongIntervalLowDensityFamily
import QICLean.Probability.Sampling.ViableSubspaceNestedSampling
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Analysis.Parameter.LowDensityCountParameters

/-!
# A physical low-energy viable subspace from least dimensions

At one fixed physical interval, the canonical raw-Hamiltonian targets
increase along a dyadic sequence of energy deficits. Their least viable
dimensions are attained. The actual all-interval improving families and
their same-degree count and suppression estimates supply the calibrated
sample at a first bad-to-good count comparison. Its image contradicts the
preceding least dimension. A finite index is derived from the actual
natural ceiling counts, not imposed as a termination hypothesis.

This is the dimension argument supporting ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1112–1128. The bandwidth is fixed
as in Assumption (LD), lines 281–284. The multiplicity factor is the actual
dimension of the raw low-energy space at that bandwidth. No spectral gap,
supplied improving family, sampling condition or count comparison is assumed.

**Scope restriction (nontrivial local dimension):** The statement retains
`q ≥ 2` and a freely chosen numerical count base `m ≥ q` with
`log m ≥ 100`. For example, `m = max q (ceil (exp 100))` meets these
conditions. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
The subsequent source-scale simplification and entropy estimate are separate.

**Local fix (strict dimension decrease):** The sample dimension is the
previous minimum divided naturally by `2*D^2`, rather than the next
minimum divided by `D^2`. The literal calibrated sample gives a strictly
smaller viable space. See the companion note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_low_density_sampling.pdf.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound`: a
  logarithmic dimension estimate for the physical low-energy space.
-/

open ManyBody (interval)
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

section LowDensityMinimumDimension

open Matrix

set_option maxHeartbeats 800000 in
-- The proof retains the fixed interval's dependent finite configuration coordinates.
/-- Every physical interval has a viable subspace for an original low-energy
target, with the actual dyadic initial count and the dimension of the full
bandwidth target as multiplicity. All family, count, sampling and finite-index
premises are derived. The same raw spectral normalization and fixed tensor
coordinates are used at every scale. ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_fixed_bandwidth_interval_low_energy_viable_subspace
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r : ℕ) (v : ℝ) (hq : 2 ≤ q), q ≤ m →
      100 ≤ Real.log (m : ℝ) → p ≤ r → r ≤ L → 0 < v →
      let vbar := min v (etaLD / 2)
      let w := fun j : ℕ ↦ vbar / (6 * (2 : ℝ) ^ j)
      let g := fun j ↦ min (w j) 1
      let u := fun j ↦ 1 + Real.log (m : ℝ) + Real.log (1 / g j)
      let ell := fun j ↦ ⌈C * u j ^ 2 / g j⌉₊
      let D := fun j ↦ (m * ell j ^ 2) ^ (22 * ell j)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
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
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({x // x ∉ J} → Fin q)
      ∃ W : Submodule ℂ EM,
        Module.finrank ℂ W ≤ Module.finrank ℂ (G etaLD) * D 0 ^ 3 ∧
        Submodule.IsViable (F := EE) (3 / 200) W
          ((G (etaLD - v)).map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_interval_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r v hq hqm hlogm hpr hrL hv vbar w g u ell D Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  intro J beta tau U Phi Tm G EM EE
  have hvbar : 0 < vbar := lt_min hv (by positivity)
  have hw (j : ℕ) : 0 < w j := by dsimp only [w]; positivity
  have hhalf (j : ℕ) : w (j + 1) = w j / 2 := by
    dsimp only [w]
    rw [pow_succ]
    ring
  have hwcap (j : ℕ) : 6 * w j ≤ etaLD / 2 := by
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hvj : vbar / (2 : ℝ) ^ j ≤ vbar := div_le_self hvbar.le hpow
    have heq : 6 * w j = vbar / (2 : ℝ) ^ j := by dsimp only [w]; ring
    rw [heq]
    exact hvj.trans (min_le_right _ _)
  have hG {a b : ℝ} (hab : a ≤ b) : G a ≤ G b :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hab])
  have hnonzero : G etaLD ≠ ⊥ := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hRaw
    apply hRaw.spectralSpanLE_ne_bot_of_mem_spectrum
    · simpa only [hi] using hRaw.eigenvalues_mem_spectrum_real i
    · linarith only [hLD]
  let rho := Module.finrank ℂ (G etaLD)
  have hrho : 1 ≤ rho := by
    let : Nontrivial (G etaLD) := Submodule.nontrivial_iff_ne_bot.mpr hnonzero
    exact Module.finrank_pos
  let T : ℕ → Submodule ℂ (EM ⊗[ℂ] EE) := fun j ↦
    (G (etaLD - 6 * w j)).map Tm.toLinearEquiv.toLinearMap
  have hT (j : ℕ) : T j ≤ T (j + 1) := by
    apply Submodule.map_mono
    apply hG
    rw [hhalf]
    linarith only [hw j]
  have htarget (j : ℕ) : Module.finrank ℂ (T j) ≤ rho :=
    (Submodule.finrank_map_le _ _).trans
      (Submodule.finrank_mono (hG (by linarith only [hw j])))
  have hrun : ∃ W : Submodule ℂ EM,
      Module.finrank ℂ W ≤ rho * D 0 ^ 3 ∧
        Submodule.IsViable (F := EE) (3 / 200) W (T 0) := by
    apply Submodule.exists_isViable_finrank_le_of_dyadic_filter_families
      C vbar m rho hC hvbar (hq.trans hqm) hlogm T hT hrho htarget
    intro j
    obtain ⟨_hell, _hlogD, A, hA⟩ :=
      hfamily L q m p r (w j) hq hqm hpr hrL (hw j) Φ h0 h1
    have hbuffer : 6 * w j ≤ etaLD - 3 * w j := by
      linarith only [hwcap j, hLD]
    have heta : etaLD - 3 * w j ≤ etaLD := by linarith only [hw j]
    obtain ⟨Tlo, Thi, Delta, _hle, hupper, hlower, hDelta, htrade, himprove⟩ :=
      hA (etaLD - 3 * w j) hbuffer heta
    have hupcut : etaLD - 3 * w j = etaLD - 6 * w (j + 1) := by
      rw [hhalf]
      ring
    have hlocut : minEigenvalue hRaw + (etaLD - 3 * w j) - 3 * w j =
        minEigenvalue hRaw + (etaLD - 6 * w j) := by ring
    have hupper' : Submodule.IsCloseTo (1 / 200) (T (j + 1))
        (Thi.map Tm.toLinearEquiv.toLinearMap) := by
      apply (Submodule.isCloseTo_map_iff Tm).mpr
      change Submodule.IsCloseTo (1 / 200) (G (etaLD - 6 * w (j + 1))) Thi
      rw [← hupcut]
      exact hupper
    have hlower' : Submodule.IsCloseTo (1 / 200)
        (Tlo.map Tm.toLinearEquiv.toLinearMap) (T j) := by
      apply (Submodule.isCloseTo_map_iff Tm).mpr
      simpa only [G, hlocut] using hlower
    refine ⟨A, Tlo.map Tm.toLinearEquiv.toLinearMap,
      Thi.map Tm.toLinearEquiv.toLinearMap, Delta,
      hupper', hlower', hDelta.le, htrade, ?_⟩
    intro delta hdelta S hS
    exact (himprove S delta hS hdelta).2
  obtain ⟨W, hdim, hW⟩ := hrun
  refine ⟨W, hdim, hW.of_target_le (Submodule.map_mono (hG ?_))⟩
  have hinit : 6 * w 0 = vbar := by dsimp only [w]; ring
  rw [hinit]
  linarith only [min_le_left v (etaLD / 2)]

end LowDensityMinimumDimension

section LowDensityLogDimension

/-!
## A logarithmic dimension estimate for the physical low-energy space

The actual natural budget from the least-dimension argument is bounded
by a regularized logarithmic expression. One fixed numerical multiplier
of the local dimension supplies the count regularity. The bandwidth cap
changes the inverse width by a constant depending only on that bandwidth.
The underlying physical interactions and target subspace are unchanged.

This gives the dimension estimate in ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1107–1128, for physical intervals.
Under the substitution `v = mu / log L`, its exponent is an explicit
version of the printed soft-O bound. No spectral gap or sampling premise
is imposed. The multiplicity is the actual original low-energy dimension.

**Scope restriction (physical intervals and fixed bandwidth):** The
statement retains `q ≥ 2` and the quantifiers `∀ eta > 0, ∃ K_eta` before
the physical data. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
Entropy, sharper accuracy-dependent tails and MPS conclusions are separate.

The strict-decrease correction used in the minimum argument is documented
at https://sirui-lu.com/QICLean/paper-gaps/alvv16_low_density_sampling.pdf.
-/

open Matrix

set_option maxHeartbeats 800000 in
-- The argument retains the original interval's dependent configuration coordinates.
/-- A physical original-window viable space with the regularized logarithmic
dimension bound. The coefficient is uniform before length, local dimension,
interactions, interval and positive deficit. Deficits exceeding the bandwidth
give the zero target and are included. ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1107–1128. -/
theorem exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
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
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ ({x // x ∉ J} → Fin q)
      ∃ W : Submodule ℂ EM,
        (Module.finrank ℂ W : ℝ) ≤ (Module.finrank ℂ (G etaLD) : ℝ) *
          Real.exp (K / v * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / v)) ^ 3) ∧
        Submodule.IsViable (F := EE) (3 / 200) W
          ((G (etaLD - v)).map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, _hCeta, hactual⟩ :=
    exists_fixed_bandwidth_interval_low_energy_viable_subspace etaLD hLD
  have hC1 : 1 ≤ C := (by norm_num : (1 : ℝ) ≤ 100).trans hC
  let B := max 12 etaLD
  let F := 102 + Real.log B
  let K := 66 * (C + 1) * (6 + 2 * Real.log (C + 1)) * B * F ^ 3
  have hK : 0 < K :=
    (Real.log_initial_low_density_count_le C etaLD etaLD 2 hC1 hLD hLD le_rfl
      (by decide)).1
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  intro J beta tau U Phi Tm G EM EE
  by_cases hveta : v ≤ etaLD
  · let m := q * ⌈Real.exp 100⌉₊
    let vbar := min v (etaLD / 2)
    let g := min (vbar / 6) 1
    let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
    let D := (m * ell ^ 2) ^ (22 * ell)
    obtain ⟨_hK, hqm, hlogm, hDpos, hbudget⟩ :=
      Real.log_initial_low_density_count_le C etaLD v q hC1 hLD hv hveta hq
    obtain ⟨W, hdim, hW⟩ := hactual L q m p r v hq hqm hlogm hpr hrL hv Φ h0 h1
    have hdimNat : Module.finrank ℂ W ≤ Module.finrank ℂ (G etaLD) * D ^ 3 := by
      simpa only [pow_zero, mul_one] using hdim
    have hdimR : (Module.finrank ℂ W : ℝ) ≤
        (Module.finrank ℂ (G etaLD) : ℝ) * (D : ℝ) ^ 3 := by exact_mod_cast hdimNat
    have hDexp : (D : ℝ) ^ 3 ≤
        Real.exp (K / v * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / v)) ^ 3) := by
      calc
        (D : ℝ) ^ 3 = Real.exp (Real.log ((D : ℝ) ^ 3)) :=
          (Real.exp_log (pow_pos hDpos 3)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hbudget
    exact ⟨W, hdimR.trans (mul_le_mul_of_nonneg_left hDexp (Nat.cast_nonneg _)), hW⟩
  · have hzero : G (etaLD - v) = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      change hRaw.eigenvalues i ≤ minEigenvalue hRaw + (etaLD - v) at hi
      exfalso
      have hmin := minEigenvalue_le hRaw i
      have hvgt : etaLD < v := lt_of_not_ge hveta
      linarith only [hi, hmin, hvgt]
    refine ⟨⊥, ?_, ?_⟩
    · simpa only [finrank_bot, Nat.cast_zero] using
        mul_nonneg (Nat.cast_nonneg (Module.finrank ℂ (G etaLD)))
          (Real.exp_pos (K / v * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / v)) ^ 3)).le
    · rw [hzero, Submodule.map_bot]
      exact Submodule.isCloseTo_of_le (by norm_num) bot_le

end LowDensityLogDimension

end TNLean.MPS.AreaLaw
