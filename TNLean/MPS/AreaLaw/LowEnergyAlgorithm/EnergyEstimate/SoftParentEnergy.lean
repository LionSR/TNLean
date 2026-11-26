/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.HardTruncationResidual
import QICLean.ManyBody.Sites.Twirl
import QICLean.Analysis.Order.QuadraticScalarShift
import QICLean.ManyBody.Entropy.Cut.PositiveLocalLift
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.AdjacentIntervalMerge
import QICLean.Analysis.Parameter.SoftRegionalEnergyParameters
import QICLean.Analysis.Projection.RegionalEnergyCalibration
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Spectral.Eigenvalue.CompressionEnergyBounds
import QICLean.ManyBody.Entropy.Cut.RegionalViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.SoftTruncation.SoftFamilyResiduals
import QICLean.Spectral.Filter.ShiftedSoftHardTruncation
import QICLean.Spectral.Perturbation.GroundEnergyResidual

/-!
# Regional coordinates and energy of the central soft replacement

The actual central replacement and its unmodified collars give a
positive centered native operator with an explicit norm bound. Its
actual attained minimum is compared with the original parent minimum
by the proved reverse residual. The resulting energy estimate concerns
the entire original ground space. The generated soft spectral target
and its separate untrimmed energy candidate remain subsequent steps.
These are corrected auxiliaries to ALVV, arXiv:1602.08828v2,
Figure `fig:generate`, lines 1348–1392, and Figure `fig:algo1`, line 1631.

**Scope restriction (regional energy auxiliary):** The center is one-sided,
the norm bound is for the centered operator, and the energy bound concerns
the original ground space. Transfer to the generated soft spectral target
and the recursive energy estimate remain separate. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.exists_native_soft_word_compressed_energy_estimate`: raw regional energy
  on the same untrimmed word candidate.
* `TNLean.MPS.AreaLaw.ALVV.exists_soft_parent_structure`: the actual central soft replacement inside
  a parent interval.
-/

section SoftParentStructure

/-!
## The actual central soft replacement inside a parent interval

The original parent bonds determine the central soft term, unchanged
collars, actual ground energies and a uniform reverse residual. Estimated
centers retain their ten-unit correction and the logarithmic harmonic cap.
This is an auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`,
lines 1348–1392. The source energy-estimation target remains separate.

**Scope restriction (estimated center and centered norm):** The estimate
lies below the actual middle minimum by at most ten. The proved norm bound
is after subtracting the attained soft minimum. These conditions are not
identified with the broader absolute-error input or uncentered norm in the
printed efficient-generation theorem. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`. The harmonic cap is
corrected as documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_soft_truncation_log_bound.pdf.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

private theorem middle_soft_parent_cap {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Fin 5 → Matrix σ σ ℂ) (e : Fin 5 → ℝ)
    (Y : Matrix σ σ ℂ) (p t a b : ℝ) (m : ℕ)
    (he : ∀ j, 0 ≤ e j) (hpu : p ≤ e 2)
    (hX : (A 2 - (p : ℂ) • 1).PosSemidef) (ht : 0 < t) (hm : 1 ≤ m)
    (hA0 : A 0 = 0) (hA4 : A 4 = 0)
    (hA1 : A 1 ≤ a • 1) (hA3 : A 3 ≤ b • 1) (hY : Y ≤ (4 : ℝ) • 1) :
    (∑ j, ((if j = 2 then (p : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) - (e j : ℂ) • 1)) + Y ≤
      (a + t * (1 + Real.log (m : ℝ)) + b + 4) • 1 := by
  classical
  let cap := t * (1 + Real.log (m : ℝ))
  let c : Fin 5 → ℝ := ![0, a, cap, b, 0]
  let F := fun j : Fin 5 ↦ (if j = 2 then (p : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) - (e j : ℂ) • 1
  have hraw (j : Fin 5) (d : ℝ) (hd : A j ≤ d • 1) : A j - (e j : ℂ) • 1 ≤ d • 1 := by
    apply (sub_le_self (A j) ?_).trans hd
    rw [Complex.coe_smul]
    exact smul_nonneg (he j) zero_le_one
  have hsoft : (p : ℂ) • (1 : Matrix σ σ ℂ) +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (e 2 : ℂ) • 1 ≤ cap • 1 := by
    calc
      _ ≤ (e 2 : ℂ) • 1 + cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) -
          (e 2 : ℂ) • 1 := by
        apply sub_le_sub_right
        apply _root_.add_le_add _ (le_refl _)
        simpa only [Complex.coe_smul] using
          smul_le_smul_of_nonneg_right hpu (zero_le_one : (0 : Matrix σ σ ℂ) ≤ 1)
      _ = cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) := by abel
      _ ≤ cap • 1 := hX.cfc_softTruncation_le_scalar t m ht hm
  have hFc (j : Fin 5) : F j ≤ c j • 1 := by
    fin_cases j
    · simpa [F, c, hA0] using hraw 0 0 (by simp [hA0])
    · simpa [F, c] using hraw 1 a hA1
    · simpa [F, c] using hsoft
    · simpa [F, c] using hraw 3 b hA3
    · simpa [F, c, hA4] using hraw 4 0 (by simp [hA4])
  have hsum : (∑ j, F j) + Y ≤ (∑ j, c j • (1 : Matrix σ σ ℂ)) + (4 : ℝ) • 1 :=
    add_le_add (Finset.sum_le_sum (fun j _ ↦ hFc j)) hY
  change (∑ j, F j) + Y ≤ (a + cap + b + 4) • 1
  calc
    _ ≤ (∑ j, c j • (1 : Matrix σ σ ℂ)) + (4 : ℝ) • 1 := hsum
    _ = (a + cap + b + 4) • 1 := by
      simp only [← Finset.sum_smul, Fin.sum_univ_five]
      norm_num [c]
      module

/-- Actual original parent bonds construct the central estimated-center
soft replacement and its true ground energy. The unchanged collars give
an explicit norm bound, and the actual reverse residual bounds the
minimum shift. All ground data precede the auxiliary tail cutoff.
This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:generate`, lines 1348–1392; no efficient-generation claim is made. -/
theorem exists_soft_parent_structure {L q l u v r ell : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let Ψ := Φ.restrict fun i ↦ l ≤ i.val ∧ i.val + 1 < r
    let k : Fin 6 → ℕ := ![0, l, u, v, r, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ Ψ.partialHamiltonian (I j)
    let P := Φ.partialHamiltonian (Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r))
    ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ (∀ j, 0 ≤ e j) ∧
      let s := ∑ j, e j
      let C := P - (s : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ C *ᵥ z = (E : ℂ) • z ∧
      (C - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 4 ∧
      ∀ (p t : ℝ) (m : ℕ), e 2 - 10 ≤ p → p ≤ e 2 → 0 < t → 2 ≤ m →
        let B := P - A 2 + (p : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (s : ℂ) • 1
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), B.IsHermitian ∧
          (B + (10 : ℂ) • 1).PosSemidef ∧ B ≤ C ∧
          star w ⬝ᵥ w = 1 ∧ B *ᵥ w = (mu : ℂ) • w ∧
          (B - (mu : ℂ) • 1).PosSemidef ∧ -10 ≤ mu ∧ mu ≤ E ∧
          ‖B - (mu : ℂ) • 1‖ ≤ t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14 ∧
          ∀ T : ℝ, 48 ≤ t → 48 ≤ T →
            0 ≤ E - mu ∧ E - mu ≤
              32 * Real.exp (-(T - 48) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
  classical
  intro Ψ k I A P
  let Cross := Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, u, v, r} : Finset ℕ))
  let Y := Ψ.partialHamiltonian Cross
  have hp0 (i) : 0 ≤ Ψ.term i := ManyBody.Interaction.restrict_term_nonneg (h0 i)
  have hp1 (i) : Ψ.term i ≤ 1 := ManyBody.Interaction.restrict_term_le_one (h1 i)
  obtain ⟨hCross, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
      _hH, _bH, _aH, _hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq hlu huv hvr hrL Ψ hp0 hp1
  obtain ⟨_hk, _hR, _hsA, hA, hYpos, hYcap, _hCross', hsum0⟩ :=
    ManyBody.BondInteraction.five_region_original_bond_data L q l u v r hlu huv hvr hrL Ψ hp0 hp1
  have he0 (j : Fin 5) : 0 ≤ e j :=
    (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx
  have hP : Ψ.hamiltonian = P := ManyBody.Interaction.hamiltonian_restrict Φ _
  have hsum : P = (∑ j, A j) + Y := hP.symm.trans hsum0
  let s := ∑ j, e j
  let C := P - (s : ℂ) • 1
  have hHz' : C *ᵥ z = (E : ℂ) • z := by simpa only [hP] using hHz
  have hE' : (C - (E : ℂ) • 1).PosSemidef := by simpa only [hP] using hE
  have hE4 : E ≤ 4 := hEC.trans (by exact_mod_cast hCross)
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz', hE', hE0, hE4, ?_⟩
  intro p t m hpl hpu ht hm B
  let S : Finset (Fin 5) := {2}
  let pvec := Function.update e (2 : Fin 5) p
  have hpL : ∀ j ∈ S, e j - 10 ≤ pvec j := by
    intro j hj
    have hj' : j = 2 := Finset.mem_singleton.mp hj
    subst j
    simpa only [pvec, Function.update_self] using hpl
  have hpU : ∀ j ∈ S, pvec j ≤ e j := by
    intro j hj
    have hj' : j = 2 := Finset.mem_singleton.mp hj
    subst j
    simpa only [pvec, Function.update_self] using hpu
  let F := fun j : Fin 5 ↦ (pvec j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A j - (pvec j : ℂ) • 1)
  let B0 := (∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y
  obtain ⟨mu, w, hB0, hBpos0, hBC0, hw, hBw0, hBlow0, hmuD, hmuE, _hmuC,
      bG, aG, hEigG, _hforward, hreverse⟩ := hfamily S pvec t m hpL hpU ht hm
  have hF2 : F 2 = (p : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) := by
    simp only [F, pvec, Function.update_self]
  have hcenter : (∑ j, (A j - (e j : ℂ) • 1)) + Y = C := by
    dsimp only [C, s]
    rw [hsum, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_smul]
    abel
  have hB0eq : B0 = B := by
    have hdiff := sum_centered_sub_partially_replaced_eq A F
      (fun j ↦ (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) S
    simp only [S, Finset.sum_singleton] at hdiff
    calc
      B0 = (∑ j, (A j - (e j : ℂ) • 1)) + Y - (A 2 - F 2) := by
        rw [← hdiff]
        dsimp only [B0]
        abel
      _ = B := by rw [hcenter, hF2]; dsimp only [B, C]; abel
  have hB : B.IsHermitian := hB0eq ▸ hB0
  have hBpos : (B + (10 : ℂ) • 1).PosSemidef := by
    change ((∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) +
      (((10 * (S.card : ℝ)) : ℝ) : ℂ) • 1).PosSemidef at hBpos0
    have hfull := hBpos0.add hYpos
    have heq : ((∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) +
        (((10 * (S.card : ℝ)) : ℝ) : ℂ) • 1) + Y = B + (10 : ℂ) • 1 := by
      have hD : (((10 * (S.card : ℝ)) : ℝ) : ℂ) = 10 := by norm_num [S]
      rw [hD, ← hB0eq]
      dsimp only [B0]
      abel
    exact heq ▸ hfull
  have hBC : B ≤ C := by
    change B0 ≤ Ψ.hamiltonian - (s : ℂ) • 1 at hBC0
    rw [hB0eq, hP] at hBC0
    exact hBC0
  have hBw : B *ᵥ w = (mu : ℂ) • w := hB0eq ▸ hBw0
  have hBlow : (B - (mu : ℂ) • 1).PosSemidef := hB0eq ▸ hBlow0
  have hmu10 : -10 ≤ mu := by
    simpa only [S, Finset.card_singleton, Nat.cast_one, mul_one] using hmuD
  refine ⟨mu, w, hB, hBpos, hBC, hw, hBw, hBlow, hmu10, hmuE, ?_, ?_⟩
  · have hA0 : A 0 = 0 := ManyBody.Interaction.partialHamiltonian_restrict_eq_zero
      (s := Finset.univ.filter fun i : Fin (L - 1) ↦ 0 ≤ i.val ∧ i.val + 1 < l)
      fun i hi ↦ by have := (Finset.mem_filter.mp hi).2; omega
    have hA4 : A 4 = 0 := ManyBody.Interaction.partialHamiltonian_restrict_eq_zero
      (s := Finset.univ.filter fun i : Fin (L - 1) ↦ r ≤ i.val ∧ i.val + 1 < L)
      fun i hi ↦ by have := (Finset.mem_filter.mp hi).2; omega
    have hcard1 : (I 1).card ≤ 2 * ell :=
      (ManyBody.card_internal_bonds_le L l u).trans (by omega)
    have hcard3 : (I 3).card ≤ 2 * ell :=
      (ManyBody.card_internal_bonds_le L v r).trans (by omega)
    have hcap1 : A 1 ≤ (2 * (ell : ℝ)) • 1 :=
      (hA 1).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hcard1) zero_le_one)
    have hcap3 : A 3 ≤ (2 * (ell : ℝ)) • 1 :=
      (hA 3).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hcard3) zero_le_one)
    have hcapY : Y ≤ (4 : ℝ) • 1 := hYcap.trans
      (smul_le_smul_of_nonneg_right (by exact_mod_cast hCross) zero_le_one)
    have hpe : (p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
        (e 2 : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using
        smul_le_smul_of_nonneg_right hpu
          (zero_le_one : (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ 1)
    have hX : (A 2 - (p : ℂ) • 1).PosSemidef :=
      le_iff.mp (hpe.trans (le_iff.mpr (he 2)))
    have hform : B0 = (∑ j : Fin 5, ((if j = 2 then
        (p : ℂ) • 1 + cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) -
          (e j : ℂ) • 1)) + Y := by
      dsimp only [B0]
      congr 1
    have hcap0 := middle_soft_parent_cap A e Y p t (2 * (ell : ℝ))
      (2 * (ell : ℝ)) m he0 hpu hX ht (by omega) hA0 hA4 hcap1 hcap3 hcapY
    let cap := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 4
    have hBcap : B ≤ cap • 1 := by
      rw [← hB0eq, hform]
      convert hcap0 using 1
      dsimp only [cap]
      congr 1
      ring
    have hCcap : B - (mu : ℂ) • 1 ≤ (cap + 10) • 1 := by
      rw [Complex.coe_smul]
      calc
        _ ≤ cap • 1 - mu • 1 := sub_le_sub_right hBcap _
        _ = (cap - mu) • 1 := (sub_smul cap mu 1).symm
        _ ≤ (cap + 10) • 1 := smul_le_smul_of_nonneg_right (by linarith only [hmu10]) zero_le_one
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap (B - (mu : ℂ) • 1)
      (by dsimp only [cap]; positivity : 0 ≤ cap + 10) hBlow.nonneg).mpr
        (by simpa only [Algebra.algebraMap_eq_smul_one] using hCcap)
    dsimp only [cap] at hnorm
    linarith only [hnorm]
  · intro T ht48 hT48
    let U0 := 2 * (10 + 3 * (Cross.card : ℝ) + 2)
    have hcardC : (Cross.card : ℝ) ≤ 4 := by exact_mod_cast hCross
    have hU0 : U0 ≤ 48 := by dsimp only [U0]; linarith only [hcardC]
    have hscale : 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2) ≤ t := by
      simpa only [U0, S, Finset.card_singleton, Nat.cast_one, _root_.mul_one,
        _root_.zero_add] using hU0.trans ht48
    have hcut : 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2) ≤ T := by
      simpa only [U0, S, Finset.card_singleton, Nat.cast_one, _root_.mul_one,
        _root_.zero_add] using hU0.trans hT48
    have hrev0 := hreverse 0 T le_rfl hscale hcut
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (Ψ.hamiltonian - (s : ℂ) • 1 - B0)).domRestrict
        (Submodule.spectralSpanLE bG aG (mu + 0))‖ ≤
      (S.card : ℝ) * (8 * (Cross.card : ℝ) * Real.exp
        (-(T - 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2)) / 8) +
          (t / (m : ℝ)) * (T / t) ^ m) at hrev0
    have hScard : (S.card : ℝ) = 1 := by simp [S]
    rw [hP, hScard] at hrev0
    have hres : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (C - B0)).domRestrict
        (Submodule.spectralSpanLE bG aG (mu + 0))‖ ≤
          8 * (Cross.card : ℝ) * Real.exp (-(T - U0) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
      simpa only [_root_.mul_one, _root_.one_mul, _root_.zero_add] using hrev0
    let wE : EuclideanSpace ℂ (Fin L → Fin q) :=
      (EuclideanSpace.equiv (Fin L → Fin q) ℂ).symm w
    have hwnorm : ‖wE‖ = 1 := by
      have hsquare := re_star_dotProduct_self_eq_norm_sq w
      rw [hw] at hsquare
      change (1 : ℝ) = ‖wE‖ ^ 2 at hsquare
      nlinarith only [hsquare, norm_nonneg wE]
    have hwEigen : toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B0 wE =
        (mu : ℂ) • wE := by
      change (EuclideanSpace.equiv (Fin L → Fin q) ℂ).symm (B0 *ᵥ w) = _
      have hBw' : B0 *ᵥ w = (mu : ℂ) • w := hBw0
      rw [hBw', map_smul]
    have hEig : ∀ j, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B0 (bG j) =
        (aG j : ℂ) • bG j := hEigG
    have hshift := energy_sub_eigenvalue_le_norm_spectral_residual C B0 E mu (mu + 0)
      hE' bG aG hEig wE hwnorm hwEigen (by simp only [_root_.add_zero]; exact le_rfl)
    refine ⟨sub_nonneg.mpr hmuE, (hshift.trans hres).trans ?_⟩
    apply _root_.add_le_add _ (le_refl _)
    apply mul_le_mul
    · linarith only [hcardC]
    · exact Real.exp_le_exp.mpr (by linarith only [hU0])
    · exact Real.exp_nonneg _
    · norm_num

end TNLean.MPS.AreaLaw.ALVV

end SoftParentStructure

section SoftParentEnergy

open ManyBody (interval mem_interval)

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- Original bonds construct a native positive centered soft
operator, its true attained energy and a norm bound independent of the
parent volume apart from the explicit collar lengths. The native matrix
is chosen before every auxiliary tail cutoff. The energy comparison is
on the original full ground space; no soft-target energy or generation
algorithm is assumed or concluded. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392,
and Figure `fig:algo1`, line 1631. -/
theorem exists_native_soft_parent_energy_bound {L q l u v r ell : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let P := Φ.partialHamiltonian (Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r))
    let M := Φ.partialHamiltonian (Finset.univ.filter
      (fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v))
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      ∀ (p t : ℝ) (m : ℕ), eM - 10 ≤ p → p ≤ eM → 0 < t → 2 ≤ m →
        let R := P - M + (p : ℂ) • 1 + cfc (Real.softTruncation t m) (M - (p : ℂ) • 1)
        let budget := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14
        ∃ (eSoft : ℝ) (K : Matrix (J → Fin q) (J → Fin q) ℂ)
          (w : (Fin L → Fin q) → ℂ),
          K.PosSemidef ∧ ‖K‖ ≤ budget ∧
          R = ManyBody.place (X := fun _ ↦ Fin q) J K + (eSoft : ℂ) • 1 ∧
          star w ⬝ᵥ w = 1 ∧ R *ᵥ w = (eSoft : ℂ) • w ∧
          (R - (eSoft : ℂ) • 1).PosSemidef ∧ ‖R - (eSoft : ℂ) • 1‖ ≤ budget ∧
          ∀ T : ℝ, 48 ≤ t → 48 ≤ T →
            let rho := 32 * Real.exp (-(T - 48) / 8) + (t / (m : ℝ)) * (T / t) ^ m
            eSoft ≤ eP ∧ eP - eSoft ≤ rho ∧
              ∀ g ∈ G,
                (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
                  (ManyBody.place (X := fun _ ↦ Fin q) J K) g) g).re ≤
                    (2 + rho) * ‖g‖ ^ 2 := by
  classical
  intro config H hH G J P M
  let : Nonempty (Fin L → Fin q) := config
  let Ψ := Φ.restrict fun i ↦ l ≤ i.val ∧ i.val + 1 < r
  let k : Fin 6 → ℕ := ![0, l, u, v, r, L]
  let I := fun j : Fin 5 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  let A := fun j : Fin 5 ↦ Ψ.partialHamiltonian (I j)
  obtain ⟨e, x, z, E, hx, hxe, he, _he0, hz, hHz, hE, _hE0, _hE4, hfamily⟩ :=
    exists_soft_parent_structure hq hlu huv hvr hrL hleft hright Φ h0 h1
  have hAM : A 2 = M := ManyBody.Interaction.partialHamiltonian_restrict_of_forall
    (s := Finset.univ.filter fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v)
    fun i hi ↦ by have := (Finset.mem_filter.mp hi).2; omega
  let s := ∑ j, e j
  let eP := E + s
  have hPz : P *ᵥ z = (eP : ℂ) • z := by
    have hh := hHz
    change (P - (s : ℂ) • 1) *ᵥ z = (E : ℂ) • z at hh
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hh
    dsimp only [eP]
    rw [Complex.ofReal_add, add_smul]
    exact sub_eq_iff_eq_add.mp hh
  have hPmin : (P - (eP : ℂ) • 1).PosSemidef := by
    convert hE using 1
    dsimp only [eP]
    rw [Complex.ofReal_add, add_smul]
    abel
  obtain ⟨e0, x0, hx0, hPx0, hP0, _hPnorm, hGenergy, _hprojection⟩ :=
    exists_regional_ground_energy_bound hq (hlu.trans (huv.trans hvr)) hrL Φ h0 h1
  have heP : e0 = eP := groundEnergy_eq_of_normalized_eigenvectors P e0 eP x0 z
    hPx0 hx0 hPz hz hP0 hPmin
  have hMxe : M *ᵥ x = (e 2 : ℂ) • x := by rw [← hAM]; exact hxe 2
  have hMmin : (M - (e 2 : ℂ) • 1).PosSemidef := by rw [← hAM]; exact he 2
  refine ⟨eP, e 2, z, x, hz, hPz, hPmin, hx, hMxe, hMmin, ?_⟩
  intro p t m hpl hpu ht hm R budget
  obtain ⟨mu, w, _hB, _hBplus, hBC, hw, hBw, hBlow, _hmu10, hmuE, hnorm, hshift⟩ :=
    hfamily p t m hpl hpu ht hm
  let B := P - M + (p : ℂ) • 1 + cfc (Real.softTruncation t m) (M - (p : ℂ) • 1) -
    (s : ℂ) • 1
  let Bmid := P - A 2 + (p : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (s : ℂ) • 1
  have hBform : Bmid = B := by dsimp only [Bmid, B]; rw [hAM]
  change (Bmid - (mu : ℂ) • 1).PosSemidef at hBlow
  rw [hBform] at hBlow
  change ‖Bmid - (mu : ℂ) • 1‖ ≤ budget at hnorm
  rw [hBform] at hnorm
  change Bmid *ᵥ w = (mu : ℂ) • w at hBw
  rw [hBform] at hBw
  change Bmid ≤ P - (s : ℂ) • 1 at hBC
  rw [hBform] at hBC
  let eSoft := mu + s
  let Csoft := B - (mu : ℂ) • 1
  have hCraw : Csoft = R - (eSoft : ℂ) • 1 := by
    dsimp only [Csoft, B, R, eSoft]
    rw [Complex.ofReal_add, add_smul]
    abel
  have hPs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) P J :=
    ManyBody.BondInteraction.isSupportedOn_sum_internal_bonds L q l r Φ
  have hMs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) M J := by
    apply (ManyBody.BondInteraction.isSupportedOn_sum_internal_bonds L q u v Φ).mono
    intro i hi
    simp only [J, mem_interval] at hi ⊢
    omega
  let V := ManyBody.supportedOperators (fun _ ↦ Fin q) J
  have hPV : P ∈ V := hPs
  have hMV : M ∈ V := hMs
  have hIV : (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∈ V :=
    (one_mem (ManyBody.supportedOperators _ J))
  have hXV : M - (p : ℂ) • 1 ∈ V := sub_mem hMV (SMulMemClass.smul_mem _ hIV)
  have hFV : cfc (Real.softTruncation t m) (M - (p : ℂ) • 1) ∈ V :=
    ManyBody.cfc_mem_supportedOperators _ hXV
  have hCV : Csoft ∈ V :=
    sub_mem (sub_mem (add_mem (add_mem (sub_mem hPV hMV)
      (SMulMemClass.smul_mem _ hIV)) hFV) (SMulMemClass.smul_mem _ hIV))
          (SMulMemClass.smul_mem _ hIV)
  obtain ⟨K, hK, hKnorm, hLift⟩ :=
    ManyBody.IsSupportedOn.exists_posSemidef_localLift_norm_le hCV hBlow budget hnorm
  have hRnative : R = ManyBody.place (X := fun _ ↦ Fin q) J K + (eSoft : ℂ) • 1 := by
    rw [← hLift, hCraw]
    abel
  have hRw : R *ᵥ w = (eSoft : ℂ) • w := by
    change (R - (s : ℂ) • 1) *ᵥ w = (mu : ℂ) • w at hBw
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hBw
    dsimp only [eSoft]
    rw [Complex.ofReal_add, add_smul]
    exact sub_eq_iff_eq_add.mp hBw
  refine ⟨eSoft, K, w, hK, hKnorm, hRnative, hw, hRw, ?_, ?_, ?_⟩
  · exact hCraw ▸ hBlow
  · exact hCraw ▸ hnorm
  · intro T ht48 hT48 rho
    obtain ⟨_hmuLower, hmuUpper⟩ := hshift T ht48 hT48
    have hrho : E - mu ≤ rho := hmuUpper
    have hSoftle : eSoft ≤ eP := by
      dsimp only [eSoft, eP]
      exact _root_.add_le_add hmuE (le_refl s)
    have hDiff : eP - eSoft = E - mu := by dsimp only [eP, eSoft]; ring
    refine ⟨hSoftle, ?_, ?_⟩
    · rw [hDiff]
      exact hrho
    · intro g hg
      have horder : Csoft ≤ (P - (eP : ℂ) • 1) + ((E - mu : ℝ) : ℂ) • 1 := by
        calc
          Csoft ≤ (P - (s : ℂ) • 1) - (mu : ℂ) • 1 := sub_le_sub_right hBC _
          _ = _ := by
            dsimp only [eP]
            rw [Complex.ofReal_add, Complex.ofReal_sub, add_smul, sub_smul]
            abel
      have hform := (le_iff.mp horder).isPositive_toEuclideanCLM.re_inner_nonneg_left g
      simp only [map_sub, map_add, map_smul, map_one, _root_.sub_apply, _root_.add_apply,
        _root_.smul_apply, one_apply_eq_self, inner_sub_left, inner_add_left,
        inner_smul_left, RCLike.re_to_complex, Complex.conj_ofReal,
        Complex.re_ofReal_mul] at hform
      have hself : (inner ℂ g g).re = ‖g‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
      rw [hself] at hform
      have horiginal : (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (P - (eP : ℂ) • 1) g) g).re ≤ 2 * ‖g‖ ^ 2 := by
        rw [← heP]
        exact hGenergy g hg
      rw [Matrix.re_inner_toEuclideanCLM_sub_ofReal_smul_one P eP g] at horiginal
      rw [← hLift]
      nlinarith only [hform, horiginal,
        mul_le_mul_of_nonneg_right hrho (sq_nonneg ‖g‖)]

end TNLean.MPS.AreaLaw.ALVV

end SoftParentEnergy

section SoftWordEnergyEstimate

/-!
## Raw regional energy on the same untrimmed word candidate

A specified target and its own certified word family determine the energy
candidate. The raw native matrix is a fixed-complement principal slice of
the literal soft replacement, before its true minimum is chosen. Its actual
compressed minimum gives a one-sided original-parent estimate. No target-energy
bound, projected vector or compressed eigenvalue is supplied.

This is a corrected conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and its energy proof at line 1807. The
certificate comes from the calibrated hard-clipped construction; that family
is not identified with literal soft Generate.

**Scope restriction (given family certificate):** The target, its own word
family and the calibrated count conditions are inputs supplied by the proved
physical factory. No regional energy or spectral minimum is assumed. The
substitution into the actual tree and its recursive energy assignment remain
separate. See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The actual raw compressed minimum on the specified family's one-word
child image yields a one-sided parent estimate. The soft operator and its
minimum are constructed from the original bonds. The target/family certificate,
count bounds and one-sided estimated middle center are explicit inputs. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_native_soft_word_compressed_energy_estimate
    {L q l u v r ell D s N : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (hell : 21 ≤ ell) (hD : 2 ≤ D) (hcount : 50 * ell ^ 2 ≤ D) (hsample : 1 ≤ s)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let coords := Entropy.regionTensorCoordinates q J
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    let loss := Delta / (1 - (1 / 4 : ℝ)) ^ 2
    let rho := 32 * Real.exp (-(((384 : ℝ) - 48) / 8)) +
      (768 / (12 : ℝ)) * (384 / (768 : ℝ)) ^ 12
    Module.finrank ℂ T = Module.finrank ℂ G → Submodule.IsCloseTo tau G T →
    (∀ S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)),
      Submodule.IsViable (1 / 4 : ℝ) S (T.map coords.toLinearEquiv.toLinearMap) →
      let grow : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ w : Fin 1 → Fin N,
        S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable loss grow (T.map coords.toLinearEquiv.toLinearMap)) →
    let P := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), Φ.term i
    let M := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v), Φ.term i
    let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
    let y0 := ((ManyBody.cutEquiv (fun _ ↦ Fin q) J) sigma0).2
    let native := fun x : J → Fin q ↦
      (ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm (x, y0)
    0 ≤ rho ∧ rho < 1 / 16 ∧
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      ∀ p : ℝ, eM - 10 ≤ p → p ≤ eM →
        let R := P - M + (p : ℂ) • 1 +
          cfc (Real.softTruncation 768 12) (M - (p : ℂ) • 1)
        let Kraw := R.submatrix native native
        Kraw.IsHermitian ∧ ∃ (eSoft : ℝ) (w : (Fin L → Fin q) → ℂ),
          R = ManyBody.place (X := fun _ ↦ Fin q) J Kraw ∧
          star w ⬝ᵥ w = 1 ∧ R *ᵥ w = (eSoft : ℂ) • w ∧
          (Kraw - (eSoft : ℂ) • 1).PosSemidef ∧
          eSoft ≤ eP ∧ eP - eSoft ≤ rho ∧
          ∀ (k : ℕ) (hlk : l ≤ k) (hkr : k ≤ r)
            (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
            (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              (G.map (Entropy.regionTensorCoordinates q
                (interval L l k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              (G.map (Entropy.regionTensorCoordinates q
                (interval L k r)).toLinearEquiv.toLinearMap) →
            let W : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) :=
              adjacentIntervalMerge L q l k r hlk hkr S1 S2
            let V : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ word : Fin 1 → Fin N,
              W.map ((List.ofFn (fun j ↦ F (word j))).prod : _ →ₗ[ℂ] _)
            Module.finrank ℂ V ≤ D ^ 2 * Module.finrank ℂ W ∧
              ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ V)
                (energy : Fin (n + 1) → ℝ),
                Module.finrank ℂ V = n + 1 ∧
                (∀ j, V.orthogonalCompression
                  (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw).toLinearMap
                    (b j) = (energy j : ℂ) • b j) ∧
                Antitone energy ∧ eSoft ≤ energy (Fin.last n) ∧
                energy (Fin.last n) ≤ eSoft + 3 ∧
                eP - 3 - rho ≤ energy (Fin.last n) - 3 ∧
                energy (Fin.last n) - 3 ≤ eP := by
  classical
  intro config H hH G J coords a tau Delta loss rho hdimT hGT hword
    P M sigma0 y0 native
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨htau0, htau, hloss0, hloss⟩ :=
    Real.soft_regional_filter_precision_bounds D s hD hsample
  have hnorm := Real.soft_regional_fixed_norm_bound ell D hell hcount
  obtain ⟨hrho0, hrho⟩ := Real.soft_regional_fixed_residual_lt
  have htauSmall : tau ≤ 1 / 100 := by
    apply htau.trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100)
    have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith only [hDR]
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, hsoft⟩ :=
    exists_native_soft_parent_energy_bound hq hlu huv hvr hrL hleft hright Φ h0 h1
  refine ⟨hrho0, hrho, eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, ?_⟩
  intro p hpl hpu R Kraw
  have hPpos : P.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hMpos : M.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hscalar : IsSelfAdjoint ((p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (by simp [IsSelfAdjoint])
  have hRself : IsSelfAdjoint R :=
    (((hPpos.isHermitian.isSelfAdjoint.sub hMpos.isHermitian.isSelfAdjoint).add hscalar).add
      IsSelfAdjoint.cfc)
  have hKraw : Kraw.IsHermitian := hRself.isHermitian.submatrix native
  obtain ⟨eSoft, K, w, hK, _hKnorm, hR, hw, hRw, hC, hCnorm, hresidual⟩ :=
    hsoft p 768 12 hpl hpu (by norm_num) (by norm_num)
  obtain ⟨hSoftLE, hShift, hGenergy⟩ := hresidual 384 (by norm_num) (by norm_num)
  norm_num only at hShift hGenergy hCnorm
  have hrhoEq : 32 * Real.exp (-42) + (1 : ℝ) / 64 = rho := by norm_num [rho]
  rw [hrhoEq] at hShift hGenergy
  have hNormD : ‖R - (eSoft : ℂ) • 1‖ ≤ (D : ℝ) := by
    have hbudget : 768 * (1 + Real.log (12 : ℝ)) + 4 * (ell : ℝ) + 14 ≤ D := by
      linarith only [hnorm.2]
    exact hCnorm.trans hbudget
  have hCeq : R - (eSoft : ℂ) • 1 =
      ManyBody.place (X := fun _ ↦ Fin q) J K := sub_eq_iff_eq_add.mpr hR
  have hGenergyC : ∀ g ∈ G,
      RCLike.re (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (R - (eSoft : ℂ) • 1) g) g) ≤ (2 + rho) * ‖g‖ ^ 2 := by
    intro g hg
    rw [hCeq]
    exact hGenergy g hg
  have hRnative : R = ManyBody.place (X := fun _ ↦ Fin q) J
      (K + (eSoft : ℂ) • 1) := by
    rw [ManyBody.place_add, ManyBody.place_smul, ManyBody.place_one]
    exact hR
  have hNative : Kraw = K + (eSoft : ℂ) • 1 := by
    ext x y
    change ManyBody.cutOperator J R (x, y0) (y, y0) = _
    rw [hRnative, ManyBody.cutOperator_place]
    simp
  have hRawLift : R = ManyBody.place (X := fun _ ↦ Fin q) J Kraw := by
    rw [hNative]
    exact hRnative
  have hRawLower : (Kraw - (eSoft : ℂ) • 1).PosSemidef := by
    rw [hNative, add_sub_cancel_right]
    exact hK
  refine ⟨hKraw, eSoft, w, hRawLift, hw, hRw, hRawLower, hSoftLE, hShift, ?_⟩
  intro k hlk hkr S1 S2 hS1 hS2 W V
  have hmerged := isViable_adjacentIntervalMerge hlk hkr G S1 S2 hS1 hS2
  have hGTmap : Submodule.IsCloseTo tau
      (G.map coords.toLinearEquiv.toLinearMap) (T.map coords.toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff coords).mpr hGT
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map coords.toLinearEquiv.toLinearMap) := by
    apply Submodule.IsCloseTo.of_le (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num))
    linarith only [htauSmall]
  obtain ⟨hdimV, hV⟩ := hword W hWT
  refine ⟨hdimV, ?_⟩
  let U := (V.tensorProd
    (⊤ : Submodule ℂ (EuclideanSpace ℂ ({v // v ∉ J} → Fin q)))).comap
      coords.toLinearEquiv.toLinearMap
  have hmapU : U.map coords.toLinearEquiv.toLinearMap = V.tensorProd
      (⊤ : Submodule ℂ (EuclideanSpace ℂ ({v // v ∉ J} → Fin q))) :=
    Submodule.map_comap_eq_of_surjective coords.surjective _
  have hUT : Submodule.IsCloseTo loss U T := by
    apply (Submodule.isCloseTo_map_iff coords).mp
    rw [hmapU]
    exact hV
  have hproject := hGT.map_starProjection_energy_le_three_of_close_target hUT
    (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (R - (eSoft : ℂ) • 1))
    hC.isPositive_toEuclideanCLM hGenergyC hNormD hrho0 hrho.le
    htau0.le htau hloss0.le hloss
  have hGne : G ≠ ⊥ := by
    obtain ⟨j, hj⟩ := minEigenvalue_achieved hH
    apply hH.spectralSpanLE_ne_bot_of_mem_spectrum _ le_rfl
    rw [← hj]
    exact hH.eigenvalues_mem_spectrum_real j
  have hTne : T ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    rw [hdimT]
    exact Submodule.one_le_finrank_iff.mpr hGne
  obtain ⟨t, htT, htne⟩ := T.ne_bot_iff.mp hTne
  have hloss1 : loss < 1 :=
    (Real.projected_nine_quarters_energy_le_three
      (by positivity : (0 : ℝ) ≤ D) hloss0.le hloss).1
  let z := U.starProjection t
  have hzne : z ≠ 0 := hUT.starProjection_ne_zero hloss1 htT htne
  have hzU : z ∈ U := U.starProjection_apply_mem t
  have hzenergy := hproject z (Submodule.mem_map_of_mem htT)
  have hRawEnergy : (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R z) z).re ≤
      (eSoft + 3) * ‖z‖ ^ 2 := by
    change (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (R - (eSoft : ℂ) • 1) z) z).re ≤ 3 * ‖z‖ ^ 2 at hzenergy
    rw [Matrix.re_inner_toEuclideanCLM_sub_ofReal_smul_one R eSoft z] at hzenergy
    nlinarith only [hzenergy]
  have hConj := Entropy.regionTensorCoordinates_conjugation_localLift q J Kraw
  have hTA : coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R z) =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw)
        (1 : EuclideanSpace ℂ ({v // v ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) (coords z) := by
    have hh := congrArg (fun f ↦ f (coords z)) hConj
    change coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (ManyBody.place (X := fun _ ↦ Fin q) J Kraw) (coords.symm (coords z))) = _ at hh
    rw [coords.symm_apply_apply, ← hRawLift] at hh
    exact hh
  have hTensorEnergy : (inner ℂ
      (TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw)
        (1 : EuclideanSpace ℂ ({v // v ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) (coords z)) (coords z)).re ≤
      (eSoft + 3) * ‖coords z‖ ^ 2 := by
    rw [← hTA, coords.inner_map_map, coords.norm_map]
    exact hRawEnergy
  have hTensorNe : coords z ≠ 0 := by
    intro hz
    exact hzne (coords.injective (hz.trans coords.map_zero.symm))
  obtain ⟨n, hn, hlower, hupper⟩ := hKraw.exists_compression_min_between_of_tensor_energy
    V eSoft (eSoft + 3) hRawLower hzU hTensorNe hTensorEnergy
  let hSym := V.orthogonalCompression_isSymmetric
    (isSymmetric_toEuclideanLin_iff.mpr hKraw)
  change hSym.eigenvalues hn (Fin.last n) ≤ eSoft + 3 at hupper
  change eSoft ≤ hSym.eigenvalues hn (Fin.last n) at hlower
  refine ⟨n, hSym.eigenvectorBasis hn, hSym.eigenvalues hn, hn,
    hSym.apply_eigenvectorBasis hn, hSym.eigenvalues_antitone hn,
    hlower, hupper, ?_, ?_⟩
  · linarith only [hlower, hShift]
  · linarith only [hupper, hSoftLE]

end TNLean.MPS.AreaLaw.ALVV

end SoftWordEnergyEstimate
