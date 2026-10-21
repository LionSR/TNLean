/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RelativeGeneratorLocalization
import TNLean.Circuit.SupportedGaussianIntegral

/-!
# Supported Gaussian averaging on a contiguous chain

A projected relative-evolution equation constructs a unitary path near the
crossing supports. This path is chosen before the observable, Gaussian
variance and time cutoff. Averaging its product with the separately localized
observable gives a supported operator without increasing the observable norm,
together with an explicit approximation bound. The constants depend only on
the interaction range and norm bound.

## Main result

* `exists_supported_gaussian_integral`: one supported path and its
  Gaussian averages, with constants uniform in all chain and observable data.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 381–402.
No gap, information bound or reset conclusion is assumed or asserted here.
-/

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.MPS.AreaLaw

/-- A single supported unitary path yields the localized truncated
Gaussian integrals for every supported observable, variance and cutoff.
Source: TNLean note, `part2a_mps_information.tex`, lines 381–402. -/
theorem exists_supported_gaussian_integral (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (L : ℕ) (h : ChainHamiltonian L q R J) (D : Finset (Fin L))
        (ℓ : ℝ), 0 ≤ ℓ →
        let K := h.doubled.operator
        let K' := (h.swappedDoubled D).operator
        let crossing := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin L) ↦
          Finset.univ.filter (fun y : Fin L ↦
            ∃ x ∈ S, (Nat.dist x.val y.val : ℝ) ≤ ℓ)
        ∃ U : ℝ → Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • siteExpectation (q * q) (N Z)
              (heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin L → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ supportedOperators (q * q) (N Z : Set (Fin L))) ∧
          ∀ (Q : Finset (Fin L))
            (W : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ),
            W ∈ supportedOperators (q * q) (Q : Set (Fin L)) →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                siteExpectation (q * q) (N Q) (heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ supportedOperators (q * q) (B : Set (Fin L)) ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (L : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - ℓ / 2) := by
  classical
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let d : ℝ := 4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)
  let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
  have ha : 0 < a := by
    have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact div_pos (by positivity) hden
  have hd : 0 ≤ d := by positivity
  have hv : 0 < v := by positivity
  refine ⟨a + d, v, by positivity, hv, ?_⟩
  intro q hq L h D ℓ hℓ K K' crossing Z N
  have hqq : 1 ≤ q * q := by nlinarith
  have : NeZero (q * q) := ⟨by omega⟩
  obtain ⟨U, hU0, hU, hunit, hsupport, haverage⟩ :=
    exists_supported_gaussian_integral_of_projection_bounds (q * q)
      (h.swappedDoubled D).operator_isHermitian h.doubled.operator_isHermitian (N Z)
  refine ⟨U, hU0, hU, hunit, hsupport, ?_⟩
  intro Q W hW η T hT B M
  have hgen (s : ℝ) (hs : |s| ≤ T) :
      ‖heisenbergEvolution K' s (K' - K) -
        siteExpectation (q * q) (N Z) (heisenbergEvolution K' s (K' - K))‖ ≤
          d * (L : ℝ) * Real.exp (v * T - ℓ / 2) :=
    (h.norm_relativeGenerator_sub_siteExpectation_le D hq ℓ hℓ s).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hs hv.le) _))
        (mul_nonneg hd (Nat.cast_nonneg _)))
  have hnear (t : ℝ) (ht : |t| ≤ T) :
      ‖heisenbergEvolution K' t W -
        siteExpectation (q * q) (N Q) (heisenbergEvolution K' t W)‖ ≤
          ‖W‖ * a * (L : ℝ) ^ 2 * Real.exp (v * T - ℓ / 2) := by
    have hloc := norm_heisenberg_sub_siteExpectation_chainNeighborhood_le
      (fun X : ChainSupport L R ↦ X) (h.swappedDoubled D).term
      (h.swappedDoubled D).hermitian (h.swappedDoubled D).supported b₀
      (h.swappedDoubled D).sum_norm_terms_containing_le hqq Q
      (isSupportedOn_of_mem_supportedOperators hW) ℓ hℓ t
    have hc : (Q.card : ℝ) ≤ (L : ℝ) := by
      have hcNat : Q.card ≤ L := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ Q
      exact_mod_cast hcNat
    calc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * |t| - ℓ / 2) := hloc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * T - ℓ / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left ht hv.le) _))
          (by positivity)
      _ ≤ a * (L : ℝ) ^ 2 * ‖W‖ * Real.exp (v * T - ℓ / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg W)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) ha.le
      _ = _ := by ring
  have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · norm_num [hL]
    · have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
  have hscale (t : ℝ) (ht : |t| ≤ T) :
      a * (L : ℝ) ^ 2 + d * (L : ℝ) * |t| ≤ (a + d) * (L : ℝ) ^ 2 * (1 + T) := by
    calc
      _ ≤ a * (L : ℝ) ^ 2 + d * (L : ℝ) ^ 2 * T :=
        add_le_add le_rfl (mul_le_mul
          (mul_le_mul_of_nonneg_left hLsq hd) ht (abs_nonneg _) (by positivity))
      _ ≤ _ := by
        nlinarith [mul_nonneg hd (sq_nonneg (L : ℝ)),
          mul_nonneg (mul_nonneg ha.le (sq_nonneg (L : ℝ))) hT]
  have hmono {S S' : Finset (Fin L)} (hSS' : S ⊆ S') : N S ⊆ N S' := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hSS' hx, hxy⟩
  obtain ⟨hMsupport, hMnorm, hMerror⟩ := haverage (N Q) B
    (hmono (Finset.subset_union_left : Q ⊆ Q ∪ Z))
    (hmono (Finset.subset_union_right : Z ⊆ Q ∪ Z)) W η T hT
    (a * (L : ℝ) ^ 2 * Real.exp (v * T - ℓ / 2))
    (d * (L : ℝ) * Real.exp (v * T - ℓ / 2)) (by positivity) (by positivity)
    (fun t ht ↦ by simpa only [mul_assoc] using hnear t ht) hgen
  refine ⟨hMsupport, hMnorm, hMerror.trans ?_⟩
  have hscaleT : a * (L : ℝ) ^ 2 + d * (L : ℝ) * T ≤
      (a + d) * (L : ℝ) ^ 2 * (1 + T) := by
    simpa only [abs_of_nonneg hT] using hscale T (le_of_eq (abs_of_nonneg hT))
  nlinarith only [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscaleT (norm_nonneg W))
    (Real.exp_pos (v * T - ℓ / 2)).le]

end TNLean.MPS.AreaLaw
