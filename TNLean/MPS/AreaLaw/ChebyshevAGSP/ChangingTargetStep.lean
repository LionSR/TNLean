/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SequenceParameters
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Algebra.Combinatorics.DependentSequence
import TNLean.MPS.AreaLaw.ChebyshevAGSP.ClippedFilter

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

## One coherent changing-target AKLV sequence

An actual favorable clipped filter initializes a product vector. Each next
state is the phase-aligned normalized image of the actual preceding state
under a polynomial in the next clipped Hamiltonian. One dependent recursion
chooses the whole sequence, and the rank budget is the product of the sharp
operator-Schmidt rank bounds.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1003--1052.

**Scope restriction (available window and actual gap):** The fixed physical
window must fit in the chain and have at least six interactions; the actual
first excited energy is part of the physical data. The favorable initial
width is at least 21. These restrictions are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. The exact product rank
budget is established; the source's summed logarithmic
rank estimate, optimized accuracy-dependent enlarged window, and final
entropy and MPS estimates are separate results.

It also contains the following results.

* `TNLean.MPS.AreaLaw.normalized_cut_schmidtRank_le`,
  `TNLean.MPS.AreaLaw.exists_aklv_variable_window_filtered_output`: refinement by an actual clipped
  filter with a variable window.
-/

section VariableWindowRefinement

/-!
## Refinement by an actual clipped filter with a variable window

A unit input close to the original ground vector has uniformly nonzero overlap
with the actual clipped ground vector. For every fitting window, threshold and
polynomial degree, the physical clipped Chebyshev construction therefore gives
an actual normalized filtered image. Its error contracts relative to that
clipped target, and its rank retains the sharp window-dependent exponent.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1025--1052, and the separate
accuracy-dependent window choice in lines 1503--1517.

**Scope restriction (available window):** The window has at least six
interactions and fits in the chain. The actual first excited energy is part of
the original physical data. See `docs/paper-gaps/aklv13_two_block_robustness.tex`.
No approximation sequence, scalar degree optimization or final MPS estimate is
asserted here.
-/

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A nonzero rescaling of a filtered image `Kx` has Schmidt rank at the cut `k` at most
the operator Schmidt rank of `K` at that cut times the Schmidt rank of `x`. AKLV,
arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`), lines 296–314. -/
theorem normalized_cut_schmidtRank_le {L q k : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) (c : ℂ) (hc : c ≠ 0)
    (hKx : toEuclideanLin K x ≠ 0) :
    let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
    schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
      (leftBlock L k) ψ)) ≤
      operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
        (leftBlock L k) K) *
      schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
        (leftBlock L k) x)) := by
  change schmidtRank (c • (‖toEuclideanLin K x‖⁻¹ : ℂ) •
    WithLp.ofLp (ManyBody.cutVector (leftBlock L k) (toEuclideanLin K x))) ≤ _
  rw [schmidtRank_smul_eq_of_ne_zero c hc,
    schmidtRank_smul_eq_of_ne_zero _ (by
      exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hKx)),
    Entropy.cutVector_toEuclideanLin]
  exact schmidtRank_mulVec_le _ _


/-- The physical clipped filter refines any unit input close to the original
unit ground vector, for every available window and degree. The sharp rank
exponent retains its dependence on the chosen window. AKLV,
arXiv:1301.1162v1, Lemma `l:5`, lines 1025--1052, and lines 1503--1517. -/
theorem exists_aklv_variable_window_filtered_output {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) (hx : ‖x‖ = 1)
    (hxΩ : ‖x - Ω‖ ^ 2 ≤ 1 / 16) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e j : ℂ) • z) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s ∧
        ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
          0 ≤ E ∧ ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
          (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
            (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
          ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 ∧
          ‖x - φ‖ ^ 2 ≤ 1 / 4 ∧ 1 / 2 ≤ ‖⟪φ, x⟫_ℂ‖ ∧
          ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E = 1 ∧
            let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
            let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
            let delta : ℝ := (2 * Real.exp (-2 * (ell : ℝ) *
              Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2
            toEuclideanLin K φ = φ ∧
            operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
              (leftBlock L (a + s / 2)) K) ≤ D ∧ toEuclideanLin K x ≠ 0 ∧
            ∃ c : ℂ, ‖c‖ = 1 ∧
              let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
              ‖ψ‖ = 1 ∧
              schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
                (leftBlock L (a + s / 2)) ψ)) ≤
                  D * schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
                    (leftBlock L (a + s / 2)) x)) ∧
              ‖ψ - φ‖ ^ 2 ≤ 8 * delta * ‖x - φ‖ ^ 2 ∧
              ‖ψ - Ω‖ ^ 2 ≤ 16 * delta + Real.exp (-t / 16) / 50 := by
  classical
  obtain ⟨hq, hg1, e, E0, hregional, hEeq, hE0, hE6, hfilter⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter hs ha Φ h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  refine ⟨hq, hg1, e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht B
  obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hpoly⟩ := hfilter t ht
  have ht0 : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1))
    dsimp only [aklvLogarithmicThreshold] at ht
    linarith
  have hφΩ : ‖φ - Ω‖ ^ 2 ≤ 1 / 100 :=
    hclose.trans (div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num))
  have hxφ : ‖x - φ‖ ^ 2 ≤ 1 / 4 := by
    have hsq := norm_sub_sq_le_two_mul_add x Ω φ
    rw [norm_sub_rev Ω φ] at hsq
    nlinarith
  have hoverlap : 1 / 2 ≤ ‖⟪φ, x⟫_ℂ‖ := by
    have hid := norm_sub_sq (𝕜 := ℂ) φ x
    rw [hφ, hx, norm_sub_rev φ x] at hid
    change ‖x - φ‖ ^ 2 = 1 ^ 2 - 2 * (⟪φ, x⟫_ℂ).re + 1 ^ 2 at hid
    have hre := Complex.re_le_norm ⟪φ, x⟫_ℂ
    nlinarith
  have hoverlap0 : ⟪φ, x⟫_ℂ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hoverlap
    linarith
  have hresNorm : ‖x - ⟪φ, x⟫_ℂ • φ‖ ≤ ‖x - φ‖ := by
    have hp := (Submodule.span ℂ {φ})ᗮ.norm_starProjection_apply_le (x - φ)
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ hφ] at hp
    have hφφ : ⟪φ, φ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hφ]
    simp only [inner_sub_right, hφφ, sub_smul, one_smul] at hp
    convert hp using 1
    congr 1
    module
  have hres : ‖x - ⟪φ, x⟫_ℂ • φ‖ ^ 2 ≤ ‖x - φ‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hresNorm 2
  have hinner : (1 : ℝ) / 4 ≤ ‖⟪φ, x⟫_ℂ‖ ^ 2 := by nlinarith
  refine ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hxφ, hoverlap, ?_⟩
  intro ell
  obtain ⟨p, hdegree, hpE, hfix, _herr, hrank, hperp⟩ := hpoly ell
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
  let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
  let delta : ℝ := (2 * Real.exp (-2 * (ell : ℝ) *
    Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2
  obtain ⟨hKx, c, hc, hψunit, hψerror⟩ :=
    exists_phase_normalized_filter_output K φ x hφ hfix delta hperp hoverlap0
  let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
  have hdelta : 0 ≤ delta := sq_nonneg _
  have hcontract : ‖ψ - φ‖ ^ 2 ≤ 8 * delta * ‖x - φ‖ ^ 2 := by
    calc
      _ ≤ 2 * delta * ‖x - ⟪φ, x⟫_ℂ • φ‖ ^ 2 / ‖⟪φ, x⟫_ℂ‖ ^ 2 := hψerror
      _ ≤ 2 * delta * ‖x - φ‖ ^ 2 / ‖⟪φ, x⟫_ℂ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hres (by positivity)
      _ ≤ 2 * delta * ‖x - φ‖ ^ 2 / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hinner
      _ = _ := by ring
  have hψΩ : ‖ψ - Ω‖ ^ 2 ≤ 16 * delta + Real.exp (-t / 16) / 50 := by
    have hψφ : ‖ψ - φ‖ ^ 2 ≤ 8 * delta :=
      hcontract.trans (by nlinarith)
    have hsq := norm_sub_sq_le_two_mul_add ψ φ Ω
    nlinarith
  refine ⟨p, hdegree, hpE, hfix, hrank, hKx, c, hc, hψunit, ?_, hcontract, hψΩ⟩
  exact (normalized_cut_schmidtRank_le K x c
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hc) hKx).trans
      (Nat.mul_le_mul_right _ hrank)

end TNLean.MPS.AreaLaw

end VariableWindowRefinement

section ChangingTargetStep

section

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

private theorem aklv_regional_minima_eq {L q a s : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (e e' : Fin 3 → ℝ)
    (he : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef)
    (he' : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e' j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e' j : ℂ) • 1).PosSemidef) : e = e' := by
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
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 3 → ℝ) (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (i : ℕ)
    (x y : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let t := aklvSequenceThreshold g (i + 1)
  let ell := aklvSequenceDegree g s (i + 1)
  let B :=
    ManyBody.BondInteraction.twoBlockTruncatedHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
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
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian)
    (e : Fin 3 → ℝ)
    (he : ∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef)
    (i : ℕ) (x : EuclideanSpace ℂ (Fin L → Fin q)) (hx : ‖x‖ = 1)
    (hxΩ : ‖x - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16) :
    ∃ y : EuclideanSpace ℂ (Fin L → Fin q),
      ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ aklvSequenceWeight (i + 1) / 16 ∧
      schmidtRank (WithLp.ofLp (ManyBody.cutVector (leftBlock L (a + s / 2)) y)) ≤
        aklvSequenceFilterRank q g s (i + 1) *
          schmidtRank (WithLp.ofLp (ManyBody.cutVector (leftBlock L (a + s / 2)) x)) ∧
      IsAKLVSequenceStep a s Φ e g Ω i x y := by
  classical
  let t := aklvSequenceThreshold g (i + 1)
  let ell := aklvSequenceDegree g s (i + 1)
  let B :=
    ManyBody.BondInteraction.twoBlockTruncatedHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
  have hxsmall : ‖x - Ω‖ ^ 2 ≤ 1 / 16 := by
    have hw := (aklvSequenceWeight_pos_le_one i).2
    linarith
  obtain ⟨_hq, hg1, e', _E0, he', _hEeq, _hE0, _hE6, hfilter⟩ :=
    exists_aklv_variable_window_filtered_output hs ha Φ h0 h1
      mu g Ω hΩ hground hgap hg hexcited x hx hxsmall
  have heq : e' = e := aklv_regional_minima_eq Φ e' e he' he
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

end

section

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The initial state is an actual normalized polynomial image of a product
vector for the clipped target. AKLV, arXiv:1301.1162v1, lines 1016--1024.
The product overlap is with the clipped target, as in `Initialization`. -/
def IsAKLVSequenceInitialization {L q : ℕ} (a s : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 3 → ℝ) (g : ℝ) (Ω x : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian (a + 2) (a + s - 1) Φ e
    (aklvLogarithmicThreshold g) Finset.univ
  ∃ (E : ℝ) (φ χ : EuclideanSpace ℂ (Fin L → Fin q))
      (p : Polynomial ℝ) (c : ℂ)
      (vL : (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L (a + s / 2))) → ℂ)
      (vR : ((v : {v : Fin L // v ∉ leftBlock L (a + s / 2)}) → Fin q) → ℂ),
    ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
    ‖φ - Ω‖ ^ 2 ≤ Real.exp (-aklvLogarithmicThreshold g / 16) / 100 ∧
    p.natDegree = s ^ 2 ∧ p.eval E = 1 ∧ ‖χ‖ = 1 ∧
    ManyBody.cutVector (leftBlock L (a + s / 2)) χ =
      WithLp.toLp 2 (fun z ↦ vL z.1 * vR z.2) ∧
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    toEuclideanLin K φ = φ ∧ toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
    x = c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ

/-- The physical initialization followed by actual dyadic refinements gives
one sequence with the exact normalized-image relation on every edge and the
product rank bound. AKLV Lemma `l:5`, lines 1003--1052, in the explicit
available-window and actual-gap scope of the module. -/
theorem exists_aklv_physical_changing_target_sequence :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q a : ℕ)
        (Φ : ManyBody.BondInteraction L q)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, 0 ≤ Φ.term j) → (∀ j, Φ.term j ≤ 1) → ‖Ω‖ = 1 →
      Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ Φ.hamiltonian →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let s : ℕ := ⌈A * u ^ 2 / g⌉₊
      a + s + 1 ≤ L →
      2 ≤ q ∧ g ≤ 1 ∧ 21 ≤ s ∧
      Real.log (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) ≤
        198 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      ∃ (e : Fin 3 → ℝ) (E0 : ℝ) (ψ : ℕ → EuclideanSpace ℂ (Fin L → Fin q)),
        (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
          (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e j : ℂ) • z) ∧
          ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        (∀ i, ‖ψ i‖ = 1 ∧ ‖ψ i - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16 ∧
          schmidtRank (WithLp.ofLp (ManyBody.cutVector
            (leftBlock L (a + s / 2)) (ψ i))) ≤ aklvSequenceRankBound q g s i) ∧
        IsAKLVSequenceInitialization a s Φ e g Ω (ψ 0) ∧
        ∀ i, IsAKLVSequenceStep a s Φ e g Ω i (ψ i) (ψ (i + 1)) := by
  classical
  obtain ⟨A, hA, hA21, hinit⟩ := exists_aklv_physical_product_initialization
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited u s ha
  obtain ⟨hq, hg1, hs, hlogD, e, E0, E, φ, p,
      hregional, hEeq, hE0, hE6, _hBpos, _hBnorm, _hE, hφ,
      heigen, _hprojector, hclose, hdegree, hpE, hfix, _hrankK,
      χ, vL, vR, c, hχ, hproduct, _hoverlap, hKχ, hc, hψunit, hψrank, _hψφ, hψΩ⟩ :=
    hinit L q a Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited ha
  let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian (a + 2) (a + s - 1) Φ e
    (aklvLogarithmicThreshold g) Finset.univ
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
  let ψ0 := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
  have hinitRelation : IsAKLVSequenceInitialization a s Φ e g Ω ψ0 :=
    ⟨E, φ, χ, p, c, vL, vR, hφ, heigen, hclose, hdegree,
      hpE, hχ, hproduct, hfix, hKχ, hc, rfl⟩
  let State (i : ℕ) := {x : EuclideanSpace ℂ (Fin L → Fin q) //
    ‖x‖ = 1 ∧ ‖x - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16 ∧
      schmidtRank (WithLp.ofLp (ManyBody.cutVector (leftBlock L (a + s / 2)) x)) ≤
        aklvSequenceRankBound q g s i}
  change 21 ≤ s at hs
  change ‖ψ0‖ = 1 at hψunit
  change ‖ψ0 - Ω‖ ^ 2 ≤ 1 / 16 at hψΩ
  let initial : State 0 := by
    refine ⟨ψ0, hψunit, ?_, ?_⟩
    · simpa only [(aklvSequenceWeight_zero_succ 0).1] using hψΩ
    · rw [(aklvSequenceRankBound_zero_succ q g s 0).1]
      exact hψrank
  have hstep (i : ℕ) (x : State i) :
      ∃ y : State (i + 1), IsAKLVSequenceStep a s Φ e g Ω i x.val y.val := by
    obtain ⟨y, hyunit, hyΩ, hyrank, hrelation⟩ :=
      exists_aklv_dyadic_filtered_output (by omega) ha Φ h0 h1
        mu g Ω hΩ hground hgap hg hexcited e hregional i x.val x.property.1 x.property.2.1
    have hrank : schmidtRank (WithLp.ofLp
        (ManyBody.cutVector (leftBlock L (a + s / 2)) y)) ≤
          aklvSequenceRankBound q g s (i + 1) := by
      rw [(aklvSequenceRankBound_zero_succ q g s i).2]
      exact hyrank.trans (Nat.mul_le_mul_left _ x.property.2.2)
    exact ⟨⟨y, hyunit, hyΩ, hrank⟩, hrelation⟩
  obtain ⟨run, hrun0, hrunStep⟩ := Nat.exists_dependent_sequence
    (fun i (x : State i) (y : State (i + 1)) ↦
      IsAKLVSequenceStep a s Φ e g Ω i x.val y.val) initial hstep
  refine ⟨hq, hg1, hs, hlogD, e, E0, (fun i ↦ (run i).val),
    hregional, hEeq, hE0, hE6, (fun i ↦ (run i).property), ?_, ?_⟩
  · simpa only [hrun0] using hinitRelation
  · exact hrunStep

end TNLean.MPS.AreaLaw

end

end ChangingTargetStep
