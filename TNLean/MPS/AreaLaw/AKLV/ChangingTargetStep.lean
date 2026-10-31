/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.SequenceParameters
import TNLean.MPS.AreaLaw.AKLV.VariableWindowRefinement
import QICLean.Analysis.GroundEnergyBounds

/-!
# A dyadic step for the actual changing-target AKLV sequence

The three regional minima are fixed. Their uniqueness identifies the minima
returned by each physical refinement, so that the changing thresholds clip
one and the same normalized physical Hamiltonian. The result retains the
actual polynomial and normalized filtered image.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1025--1052.
The available-window and actual-first-excited-energy restrictions of
`VariableWindowRefinement` remain explicit. The supplied minima below are
auxiliary data; the final recursive construction obtains them physically.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

private theorem aklv_regional_minima_eq {L q a s : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (e e' : Fin 3 → ℝ)
    (he : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef)
    (he' : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e' j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s h j - (e' j : ℂ) • 1).PosSemidef) : e = e' := by
  obtain ⟨z, hz, hze, hlow⟩ := he
  obtain ⟨z', hz', hze', hlow'⟩ := he'
  funext j
  exact groundEnergy_eq_of_normalized_eigenvectors _ _ _ z z'
    (hze j) hz (hze' j) hz' (hlow j) (hlow' j)

/-- One edge of the changing-target sequence consists of an actual clipped
Hamiltonian, its unit ground vector, a normalized Chebyshev polynomial and the
phase-aligned normalized image of the preceding vector. AKLV, arXiv:1301.1162v1,
Lemma `l:5`, lines 1025--1052. This predicate is proved from physical data,
rather than supplied as a hypothesis of the recursive construction. -/
def IsAKLVSequenceStep {L q : ℕ} (a s : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (e : Fin 3 → ℝ) (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (i : ℕ)
    (x y : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let t := aklvSequenceThreshold g (i + 1)
  let ell := aklvSequenceDegree g s (i + 1)
  let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
  ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ) (c : ℂ),
    0 ≤ E ∧ ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
    (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
    ‖φ - Ω‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 100 ∧
    p.natDegree = ell ∧ p.eval E = 1 ∧
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    toEuclideanLin K φ = φ ∧ toEuclideanLin K x ≠ 0 ∧ ‖c‖ = 1 ∧
    y = c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x

/-- The actual physical refinement closes the dyadic unit-vector invariant
while retaining its exact sharp rank multiplier and normalized polynomial image.
This is the step used in the recursion for AKLV Lemma `l:5`. -/
theorem exists_aklv_dyadic_filtered_output {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h j) (interval L j.val (j.val + 2)))
    (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ (∑ j, h j))
    (e : Fin 3 → ℝ)
    (he : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef)
    (i : ℕ) (x : EuclideanSpace ℂ (Fin L → Fin q)) (hx : ‖x‖ = 1)
    (hxΩ : ‖x - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16) :
    ∃ y : EuclideanSpace ℂ (Fin L → Fin q),
      ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 16 ∧
      schmidtRank (WithLp.ofLp (Entropy.cutVector (leftBlock L (a + s / 2)) y)) ≤
        aklvSequenceFilterRank q g s (i + 1) *
          schmidtRank (WithLp.ofLp (Entropy.cutVector (leftBlock L (a + s / 2)) x)) ∧
      IsAKLVSequenceStep a s h e g Ω i x y := by
  classical
  let t := aklvSequenceThreshold g (i + 1)
  let ell := aklvSequenceDegree g s (i + 1)
  let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
  have hxsmall : ‖x - Ω‖ ^ 2 ≤ 1 / 16 := by
    have hw := (aklvSequenceWeight_pos_le_one i).2
    linarith
  obtain ⟨_hq, hg1, e', _E0, he', _hEeq, _hE0, _hE6, hfilter⟩ :=
    exists_aklv_variable_window_filtered_output hs ha h hsupp h0 h1
      mu g Ω hΩ hground hgap hg hexcited x hx hxsmall
  have heq : e' = e := aklv_regional_minima_eq h e' e he' he
  subst e'
  obtain ⟨_hBpos, _hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose,
      _hxφ, _hoverlap, hpoly⟩ :=
    hfilter t (aklvLogarithmicThreshold_le_sequenceThreshold g (i + 1))
  obtain ⟨p, hdegree, hpE, hfix, _hrankK, hKx, c, hc, hyunit, hyrank, hcontract, _hraw⟩ :=
    hpoly ell
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
  let y := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
  have htarget : ‖φ - Ω‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 100 :=
    hclose.trans (div_le_div_of_nonneg_right
      (exp_neg_sequenceThreshold_div_le hg hg1 (i + 1)) (by norm_num))
  have hdyadic := (aklvSequenceWeight_zero_succ i).2
  have hxφ : ‖x - φ‖ ^ 2 ≤ 27 * aklvSequenceWeight (i + 1) / 100 := by
    have htri := norm_sub_sq_le_two_mul_add x Ω φ
    rw [norm_sub_rev Ω φ] at htri
    linarith
  have hdelta := aklvSequenceDegree_shrink_le hg hg1 s (i + 1)
  have hyφ : ‖y - φ‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 64 := by
    have hprod := mul_le_mul hdelta hxφ (sq_nonneg ‖x - φ‖) (by norm_num : (0 : ℝ) ≤ 1 / 256)
    nlinarith
  have hyΩ : ‖y - Ω‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 16 := by
    have htri := norm_sub_sq_le_two_mul_add y φ Ω
    nlinarith [(aklvSequenceWeight_pos_le_one (i + 1)).1]
  exact ⟨y, hyunit, hyΩ, hyrank, E, φ, p, c, hE, hφ, heigen,
    hprojector, htarget, hdegree, hpE, hfix, hKx, hc, rfl⟩

end TNLean.MPS.AreaLaw
