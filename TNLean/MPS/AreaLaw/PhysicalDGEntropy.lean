/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.SupportedMarginalTails
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.DGEntropyParameters
import TNLean.MPS.AreaLaw.PhysicalDGViability

/-!
# Regional entropy in the full ground space

For an original positive nearest-neighbour chain with a spectral gap,
every unit vector in its full ground space has bounded regional entropy
on each interval. The bound has coefficient one on the logarithm of the
ground-space dimension and one universal cubic logarithmic remainder.

The accuracy-dependent families and the constant-error bootstrap use the
same universal scalar choice. The actual vector and actual regional state
are retained, including at empty intervals. This establishes the entropy
conclusion only; no efficient construction or matrix product approximation
is asserted here. Supporting ALVV, arXiv:1602.08828v2, `thm:al-dg`,
lines 1048–1099.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every unit vector in the full original ground space has a uniform entropy
bound at every actual interval. One universal constant is chosen before the
chain, Hamiltonian, gap, interval and vector. The entropy is that of the
original physical regional state; the proof uses its Schmidt coefficient
matrix in the fixed actual tensor coordinates.
Supporting the entropy conclusion of ALVV, arXiv:1602.08828v2,
`thm:al-dg`, lines 1048–1099. The accuracy-dependent families and the bootstrap
base use the same universal scale. No algorithmic or efficient matrix product
representation is asserted.

**Local fix (ground-space cutoff):** The original full ground space follows
the proof of `t:ais`; the cutoff and viability boundary are documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf. -/
theorem exists_physical_dg_interval_entropy_bound :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let J := interval L p r
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      Entropy.regionEntropy J ψ ≤ Real.log (Module.finrank ℂ G : ℝ) +
        Cbound / g * (1 + Real.log (q : ℝ) + Real.log (1 / g)) ^ 3 := by
  classical
  obtain ⟨A, hA, _hA21, hphysical⟩ :=
    exists_accuracy_physical_interval_family_and_bootstrap
  let cA : ℝ := 6 + 2 * Real.log (A + 1)
  let Cbound : ℝ := 14872 * (A + 1) * cA + 54
  have hA1 : 1 ≤ A + 1 := by linarith only [hA]
  have hcA : 0 < cA := by
    have hlog := Real.log_nonneg hA1
    dsimp only [cA]
    linarith only [hlog]
  have hAp : 0 < A + 1 := lt_of_lt_of_le zero_lt_one hA1
  have hC : 0 < Cbound := by
    dsimp only [Cbound]
    positivity
  refine ⟨Cbound, hC, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g J ψ hψG hψ
  let beta := fun _ : Fin L ↦ Fin q
  let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
    (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
  let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
    (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
  let w := (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm (Tm ψ)
  let Cψ := Matrix.schmidtCoeffMatrix (WithLp.ofLp w)
  let hρ := Matrix.posSemidef_self_mul_conjTranspose Cψ
  let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let ellq : ℕ := ⌈A * u ^ 2 / g⌉₊
  let Dq : ℕ := (q * ellq ^ 2) ^ (22 * ellq)
  obtain ⟨_hDq, _hlogDq, W0, hWdim, hW0, haccuracy⟩ :=
    hphysical L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hq1 : 1 ≤ q := Nat.le_trans (by decide : 1 ≤ 2) hq
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hu : 1 ≤ u := by
    have hlogq := Real.log_nonneg hqR
    have hlogg := Real.log_nonneg ((one_le_div hg).2 hg1)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  let D : ℕ → ℕ := fun i ↦
    let m := q * 2 ^ i
    let ui : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let elli : ℕ := ⌈A * ui ^ 2 / g⌉₊
    (m * elli ^ 2) ^ (22 * elli)
  have hDzero : D 0 = Dq := by
    simp only [D, pow_zero, mul_one, Dq, ellq, u]
  have hqm (i : ℕ) : q ≤ q * 2 ^ i :=
    Nat.le_mul_of_pos_right q (pow_pos (by decide : 0 < (2 : ℕ)) i)
  have hD (i : ℕ) : 1 ≤ D i := by
    obtain ⟨_hell, _hmD, hDi, _hlog, _hfamily⟩ := haccuracy (q * 2 ^ i) (hqm i)
    exact Nat.le_trans (by decide : 1 ≤ 2) hDi
  let K : ℝ := 22 * (A + 1) * cA / g
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hlogD (i : ℕ) : Real.log (D i : ℝ) ≤
      K * (1 + Real.log ((q * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3 := by
    obtain ⟨_hell, _hmD, _hDi, hlog, _hfamily⟩ := haccuracy (q * 2 ^ i) (hqm i)
    exact hlog
  obtain ⟨hp, hsum, hentropy, htail_of_viable⟩ :=
    Submodule.unit_cut_spectral_probability
      (σ := J → Fin q) (β := ↥(Jᶜ) → Fin q) Tm G ψ hψG hψ
  let probability := hρ.isHermitian.eigenvalues₀
  have htail (i : ℕ) (_hi : i < Fintype.card (J → Fin q)) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin (Fintype.card (J → Fin q)) ↦
        Module.finrank ℂ G * D 0 ^ 24 * D i ^ 2 ≤ a.val), probability a) ≤
          1 / (2 : ℝ) ^ (i + 1) := by
    let m := q * 2 ^ i
    obtain ⟨_hell, hmD, _hDi, _hlog, Fops, T, Delta, hTG, hGT,
      _hdimT, _hDelta, hbudget, himprove⟩ := haccuracy m (hqm i)
    have hbase : Module.finrank ℂ W0 ≤ Module.finrank ℂ G * D 0 ^ 24 := by
      rw [hDzero]
      exact hWdim.le
    have hbudget' : (D i : ℝ) ^ 12 * Delta ≤ 0.00001 := by
      simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
    have hspan := Submodule.viable_enlargement_of_close_improving_target
      Tm G T W0 (Module.finrank ℂ G * D 0 ^ 24) m (D i) Delta
      (hq1.trans (hqm i)) hmD hW0 hbase hGT hTG Fops hbudget'
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta)
    obtain ⟨hspanDim, hspanViable⟩ := hspan
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hq1.trans (hqm i))
    have hdelta : (1 / (2 * (m : ℝ)) : ℝ) < 1 := by
      apply (div_lt_one (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
      linarith only [hmR]
    have hmass := htail_of_viable (1 / (2 * (m : ℝ)))
      (⨆ j : Fin (D i ^ 2), W0.map (Fops j).toLinearMap)
      (Module.finrank ℂ G * D 0 ^ 24 * D i ^ 2) hdelta hspanDim hspanViable
    have hdenomNat : 2 ^ (i + 1) ≤ 2 * (q * 2 ^ i) := by
      rw [pow_succ]
      have hmul := Nat.mul_le_mul_right (2 ^ i) hq1
      nlinarith only [hmul]
    have hdenom : (2 : ℝ) ^ (i + 1) ≤ 2 * (m : ℝ) := by
      exact_mod_cast hdenomNat
    exact hmass.trans (div_le_div_of_nonneg_left (by norm_num)
      (pow_pos (by norm_num) (i + 1)) hdenom)
  have hraw := Entropy.probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    q (Module.finrank ℂ G) g K D hq hrG hg hg1 hK hD hlogD probability hp hsum htail
  have hrawEntropy : vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian ≤
      Real.log (Module.finrank ℂ G : ℝ) + 676 * K * u ^ 3 + 54 * Real.log 2 := by
    rw [hentropy]
    exact hraw
  have hcanonical := Real.dg_entropy_coefficient_bound A g u
    (vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian) (Module.finrank ℂ G)
    hg hg1 hu hrawEntropy
  have hactual : vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian =
      Entropy.regionEntropy J ψ :=
    (Submodule.actualRegionSplit_marginal_and_entropy (n := fun _ : Fin L ↦ q) J ψ).2
  rw [← hactual]
  exact hcanonical

end TNLean.MPS.AreaLaw
