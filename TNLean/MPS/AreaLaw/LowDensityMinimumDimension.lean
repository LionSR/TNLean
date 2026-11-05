/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalLowDensityFamily
import QICLean.Analysis.ViableSubspaceDyadicBootstrap
import QICLean.Analysis.LowEnergyOrder

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
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

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
        Module.finrank ℂ W ≤ Module.finrank ℂ (G etaLD) * D 0 ^ 3 ∧
        Submodule.IsViable (F := EE) (3 / 200) W
          ((G (etaLD - v)).map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_interval_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r v hq hqm hlogm hpr hrL hv vbar w g u ell D h hs h0 h1 config H hRaw
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
      hfamily L q m p r (w j) hq hqm hpr hrL (hw j) h hs h0 h1
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

end TNLean.MPS.AreaLaw
