/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainPartialSwap
import TNLean.MPS.AreaLaw.DomainLiebRobinson

/-!
# Localization of the relative-evolution generator on finite integer domains

The generator formed from the original doubled and regionally swapped domain
operators is localized term by term over actual crossing supports. Intrinsic
graph neighborhoods retain disconnected components. The error is linear in the
number of domain sites, with the same explicit constants as the chain estimate.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 380–400,
in the finite-domain setting of `part0_preamble.tex`, lines 191–215.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Natural-radius localization of the relative-evolution generator on an
actual finite integer domain. This extends the chain localization argument of
TNLean note, part2a_mps_information.tex, lines 380–400, to the finite domains of
part0_preamble.tex, lines 191–215. No spectral gap or reset conclusion is asserted. -/
theorem DomainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le
    {Λ : Finset ℤ} {q R : ℕ} {J : ℝ} (h : DomainHamiltonian Λ q R J)
    (D : Finset (Fin Λ.card)) (hq : 1 ≤ q) (m : ℕ) (t : ℝ) :
    let K := h.doubled.operator
    let K' := (h.swappedDoubled D).operator
    let C := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := Z.biUnion (fun x ↦ QuantumCircuit.graphBall (domainGraph Λ) x m)
    let G := QuantumCircuit.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - QuantumCircuit.siteExpectation (q * q) B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (Λ.card : ℝ) * Real.exp (v * |t| - (m : ℝ) / 2) := by
  classical
  let K := h.doubled.operator
  let g := h.swappedDoubled D
  let K' := g.operator
  let C := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
  let Z := C.biUnion (fun X ↦ X.1)
  let B := Z.biUnion (fun x ↦ graphBall (domainGraph Λ) x m)
  let G := heisenbergEvolution K' t (K' - K)
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
  change ‖G - siteExpectation (q * q) B G‖ ≤
    (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
      (Λ.card : ℝ) * Real.exp (v * |t| - (m : ℝ) / 2)
  have hqq : 1 ≤ q * q := by nlinarith
  have : NeZero (q * q) := ⟨by omega⟩
  have hloc (S : Finset (Fin Λ.card))
      (A : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ)
      (hA : Entropy.IsSupportedOn (n := fun _ ↦ q * q) A S) :
      ‖heisenbergEvolution K' t A - siteExpectation (q * q)
        (S.biUnion (fun x ↦ graphBall (domainGraph Λ) x m))
        (heisenbergEvolution K' t A)‖ ≤
          a * (S.card : ℝ) ^ 2 * ‖A‖ * Real.exp (v * |t| - (m : ℝ) / 2) := by
    simpa only [Nat.floor_natCast, K', DomainHamiltonian.operator, a, v,
      Nat.cast_add, Nat.cast_one] using
      norm_heisenberg_sub_siteExpectation_domainNeighborhood_le
        (fun X : DomainSupport Λ R ↦ X) g.term g.hermitian g.supported b₀
        g.sum_norm_terms_containing_le hqq S hA (m : ℝ) (Nat.cast_nonneg m) t
  have hcommon (S : Finset (Fin Λ.card)) (hS : S ⊆ Z)
      (A : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ)
      (hA : Entropy.IsSupportedOn (n := fun _ ↦ q * q) A S) :
      ‖heisenbergEvolution K' t A - siteExpectation (q * q) B
        (heisenbergEvolution K' t A)‖ ≤
          2 * (a * (S.card : ℝ) ^ 2 * ‖A‖ * Real.exp (v * |t| - (m : ℝ) / 2)) := by
    let N := S.biUnion (fun x ↦ graphBall (domainGraph Λ) x m)
    have hNB : N ⊆ B := Finset.biUnion_subset_biUnion_of_subset_left _ hS
    exact (norm_sub_siteExpectation_le_two_mul_norm_sub_of_mem_supportedOperators B
      (heisenbergEvolution K' t A) (siteExpectation (q * q) N (heisenbergEvolution K' t A))
      (supportedOperators_mono (Finset.coe_subset.mpr hNB)
        (siteExpectation_mem_supportedOperators N (heisenbergEvolution K' t A)))).trans
          (mul_le_mul_of_nonneg_left (hloc S A hA) (by norm_num))
  let e := sitePairConfigurationEquiv (Fin Λ.card) q q
  let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let A (X : DomainSupport Λ R) (b : Bool) := F * T X b * Fᴴ - T X b
  let δ := (LinearMap.id - siteExpectationLM (q * q) B).comp
    (LinearMap.mulLeftRight ℂ
      (NormedSpace.exp (t • (Complex.I • K')), NormedSpace.exp ((-t) • (Complex.I • K'))))
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ X ∈ C, ∑ b : Bool, A X b := hsum
  have hsumδ : G - siteExpectation (q * q) B G = ∑ X ∈ C, ∑ b : Bool, δ (A X b) := by
    change δ (K' - K) = _
    rw [hdiff, map_sum]
    simp only [map_sum]
  have ha : 0 ≤ a := by
    have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact (div_pos (by positivity) hden).le
  have hterm (X : DomainSupport Λ R) (hXC : X ∈ C) (b : Bool) :
      ‖δ (A X b)‖ ≤
        4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - (m : ℝ) / 2) := by
    have hspec := h.partialSwap_term_difference_spec D X b
    have hc : (X.1.card : ℝ) ≤ (R + 1 : ℝ) := by exact_mod_cast X.2.isChainSupport.card_le
    have hn : ‖A X b‖ ≤ 2 * |J| :=
      hspec.2.2.trans (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))
    have hbase := hcommon X.1
      (Finset.subset_biUnion_of_mem (fun X ↦ X.1) hXC) (A X b) hspec.1
    apply hbase.trans
    calc
      2 * (a * (X.1.card : ℝ) ^ 2 * ‖A X b‖ * Real.exp (v * |t| - (m : ℝ) / 2)) ≤
          2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - (m : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) ha)
          hn (norm_nonneg _) (mul_nonneg ha (sq_nonneg _))
      _ = _ := by ring
  have hsumBound : ‖G - siteExpectation (q * q) B G‖ ≤
      (C.card : ℝ) * 2 *
        (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - (m : ℝ) / 2)) := by
    rw [hsumδ]
    calc
      _ ≤ ∑ X ∈ C, ‖∑ b : Bool, δ (A X b)‖ := norm_sum_le _ _
      _ ≤ ∑ X ∈ C, ∑ b : Bool, ‖δ (A X b)‖ :=
        Finset.sum_le_sum (fun X _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _X ∈ C, ∑ _b : Bool,
          4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - (m : ℝ) / 2) :=
        Finset.sum_le_sum (fun X hXC ↦ Finset.sum_le_sum (fun b _ ↦ hterm X hXC b))
      _ = _ := by simp [mul_assoc]
  have hc : (C.card : ℝ) * 2 ≤ (chainCrossConst R : ℝ) * (Λ.card : ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ (C.card : ℝ) * 2 *
        (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - (m : ℝ) / 2)) := hsumBound
    _ ≤ ((chainCrossConst R : ℝ) * (Λ.card : ℝ)) *
        (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - (m : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end TNLean.MPS.AreaLaw
