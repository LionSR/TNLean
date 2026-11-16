/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityMinimumDimension
import QICLean.Analysis.LowDensityCountParameters

/-!
# A logarithmic dimension estimate for the physical low-energy space

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

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

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
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
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
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
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
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw
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
    obtain ⟨W, hdim, hW⟩ := hactual L q m p r v hq hqm hlogm hpr hrL hv h hs h0 h1
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

end TNLean.MPS.AreaLaw
