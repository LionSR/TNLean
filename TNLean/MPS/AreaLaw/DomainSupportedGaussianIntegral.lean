/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainRelativeGeneratorLocalization
import TNLean.Circuit.SupportedGaussianIntegral

/-!
# Supported Gaussian averaging on finite integer domains

The original doubled and regionally swapped domain operators determine one
supported unitary path. Domain localization bounds the observable and generator
projection errors, and the common Gaussian averaging theorem gives the supported
truncated filter. The constants agree with the chain estimate and precede the
local dimension, domain, Hamiltonian and observable.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 381–402,
in the finite-domain setting of `part0_preamble.tex`, lines 191–215.
-/

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.MPS.AreaLaw

/-- One supported unitary path gives the localized truncated Gaussian integrals
for every supported observable, variance and cutoff on an actual finite integer
domain. This extends the chain argument of the TNLean one-dimensional note,
part2a_mps_information.tex, lines 381–402, to the finite domains specified in
part0_preamble.tex, lines 191–215. No gap or information-reset conclusion is asserted. -/
theorem exists_supported_gaussian_integral_domain (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (Λ : Finset ℤ) (h : DomainHamiltonian Λ q R J)
        (D : Finset (Fin Λ.card)) (m : ℕ),
        let K := h.doubled.operator
        let K' := (h.swappedDoubled D).operator
        let crossing := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin Λ.card) ↦
          S.biUnion (fun x ↦ QuantumCircuit.graphBall (domainGraph Λ) x m)
        ∃ U : ℝ → Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • siteExpectation (q * q) (N Z)
              (heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin Λ.card → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ supportedOperators (q * q) (N Z : Set (Fin Λ.card))) ∧
          ∀ (Q : Finset (Fin Λ.card))
            (W : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ),
            W ∈ supportedOperators (q * q) (Q : Set (Fin Λ.card)) →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                siteExpectation (q * q) (N Q) (heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ supportedOperators (q * q) (B : Set (Fin Λ.card)) ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (Λ.card : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - (m : ℝ) / 2) := by
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
  intro q hq Λ h D m K K' crossing Z N
  have hqq : 1 ≤ q * q := by nlinarith
  have : NeZero (q * q) := ⟨by omega⟩
  have hHerm {q' : ℕ} {J' : ℝ} (g : DomainHamiltonian Λ q' R J') :
      g.operator.IsHermitian :=
    (isSelfAdjoint_sum Finset.univ (fun X _ ↦ (g.hermitian X).isSelfAdjoint)).isHermitian
  obtain ⟨U, hU0, hU, hunit, hsupport, haverage⟩ :=
    exists_supported_gaussian_integral_of_projection_bounds (q * q)
      (hHerm (h.swappedDoubled D)) (hHerm h.doubled) (N Z)
  refine ⟨U, hU0, hU, hunit, hsupport, ?_⟩
  intro Q W hW η T hT B M
  have hgen (s : ℝ) (hs : |s| ≤ T) :
      ‖heisenbergEvolution K' s (K' - K) -
        siteExpectation (q * q) (N Z) (heisenbergEvolution K' s (K' - K))‖ ≤
          d * (Λ.card : ℝ) * Real.exp (v * T - (m : ℝ) / 2) :=
    (h.norm_relativeGenerator_sub_siteExpectation_le D hq m s).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hs hv.le) _))
        (mul_nonneg hd (Nat.cast_nonneg _)))
  have hnear (t : ℝ) (ht : |t| ≤ T) :
      ‖heisenbergEvolution K' t W -
        siteExpectation (q * q) (N Q) (heisenbergEvolution K' t W)‖ ≤
          ‖W‖ * a * (Λ.card : ℝ) ^ 2 * Real.exp (v * T - (m : ℝ) / 2) := by
    have hloc :
        ‖heisenbergEvolution K' t W -
          siteExpectation (q * q) (N Q) (heisenbergEvolution K' t W)‖ ≤
            a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * |t| - (m : ℝ) / 2) := by
      simpa only [Nat.floor_natCast, N, K', DomainHamiltonian.operator, a, v,
        Nat.cast_add, Nat.cast_one] using
        norm_heisenberg_sub_siteExpectation_domainNeighborhood_le
          (fun X : DomainSupport Λ R ↦ X) (h.swappedDoubled D).term
          (h.swappedDoubled D).hermitian (h.swappedDoubled D).supported b₀
          (h.swappedDoubled D).sum_norm_terms_containing_le hqq Q
          (isSupportedOn_of_mem_supportedOperators hW) (m : ℝ) (Nat.cast_nonneg m) t
    have hc : (Q.card : ℝ) ≤ (Λ.card : ℝ) := by
      have hcNat : Q.card ≤ Λ.card := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ Q
      exact_mod_cast hcNat
    calc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * |t| - (m : ℝ) / 2) := hloc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * T - (m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left ht hv.le) _))
          (by positivity)
      _ ≤ a * (Λ.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * T - (m : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg W)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) ha.le
      _ = _ := by ring
  have hmono {S S' : Finset (Fin Λ.card)} (hSS' : S ⊆ S') : N S ⊆ N S' :=
    Finset.biUnion_subset_biUnion_of_subset_left _ hSS'
  obtain ⟨hMsupport, hMnorm, hMerror⟩ := haverage (N Q) B
    (hmono (Finset.subset_union_left : Q ⊆ Q ∪ Z))
    (hmono (Finset.subset_union_right : Z ⊆ Q ∪ Z)) W η T hT
    (a * (Λ.card : ℝ) ^ 2 * Real.exp (v * T - (m : ℝ) / 2))
    (d * (Λ.card : ℝ) * Real.exp (v * T - (m : ℝ) / 2)) (by positivity) (by positivity)
    (fun t ht ↦ by simpa only [mul_assoc] using hnear t ht) hgen
  refine ⟨hMsupport, hMnorm, hMerror.trans ?_⟩
  have hLsq : (Λ.card : ℝ) ≤ (Λ.card : ℝ) ^ 2 := by
    exact_mod_cast (show Λ.card ≤ Λ.card ^ 2 by
      simpa only [pow_two] using Nat.le_mul_self Λ.card)
  have hscaleT : a * (Λ.card : ℝ) ^ 2 + d * (Λ.card : ℝ) * T ≤
      (a + d) * (Λ.card : ℝ) ^ 2 * (1 + T) := by
    calc
      _ ≤ a * (Λ.card : ℝ) ^ 2 + d * (Λ.card : ℝ) ^ 2 * T :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLsq hd) hT)
      _ ≤ _ := by
        nlinarith [mul_nonneg hd (sq_nonneg (Λ.card : ℝ)),
          mul_nonneg (mul_nonneg ha.le (sq_nonneg (Λ.card : ℝ))) hT]
  nlinarith only [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscaleT (norm_nonneg W))
    (Real.exp_pos (v * T - (m : ℝ) / 2)).le]

end TNLean.MPS.AreaLaw
