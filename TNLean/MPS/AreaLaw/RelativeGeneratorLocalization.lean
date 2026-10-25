/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SwappedDoubledHamiltonian
import TNLean.MPS.AreaLaw.PartialSwap
import TNLean.MPS.AreaLaw.LiebRobinson
import TNLean.MPS.AreaLaw.InteractionBudget

/-!
# Localization of the relative-evolution generator on a chain

The relative-evolution generator is localized term by term over crossing
replica differences. Its projection error is bounded by a constant depending
only on the range and interaction bound, times the chain length and an
exponential in time and distance. The sharper boundary cardinality is retained
in the proof; no factor quadratic in the full crossing zone is used.

## Main result

* `ChainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le`: localization
  of the generator with explicit constants and an error linear in `L`.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 380–400.
This estimate does not construct a Gaussian filter or an information reset.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator
open TNLean.Lattice (sheetSwapOp)

namespace TNLean.MPS.AreaLaw

/-- The relative-evolution generator is exponentially close to its
expectation on the neighborhood of the crossing supports, with error linear
in the chain length. Source: TNLean note, `part2a_mps_information.tex`, lines 380–400. -/
theorem ChainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (D : Finset (Fin L)) (hq : 1 ≤ q) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    let K := h.doubled.operator
    let K' := (h.swappedDoubled D).operator
    let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := chainNeighborhood Z ℓ
    let G := QuantumCircuit.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - QuantumCircuit.siteExpectation (q * q) B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (L : ℝ) * Real.exp (v * |t| - ℓ / 2) := by
  classical
  let K := h.doubled.operator
  let g := h.swappedDoubled D
  let K' := g.operator
  let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
  let Z := C.biUnion (fun X ↦ X.1)
  let B := chainNeighborhood Z ℓ
  let G := heisenbergEvolution K' t (K' - K)
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
  change ‖G - siteExpectation (q * q) B G‖ ≤
    (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
      (L : ℝ) * Real.exp (v * |t| - ℓ / 2)
  have hqq : 1 ≤ q * q := by nlinarith
  have : NeZero (q * q) := ⟨by omega⟩
  have hloc (S : Finset (Fin L))
      (A : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ)
      (hA : Entropy.IsSupportedOn (n := fun _ ↦ q * q) A S) :
      ‖heisenbergEvolution K' t A - siteExpectation (q * q)
        (chainNeighborhood S ℓ)
        (heisenbergEvolution K' t A)‖ ≤
          a * (S.card : ℝ) ^ 2 * ‖A‖ * Real.exp (v * |t| - ℓ / 2) := by
    exact norm_heisenberg_sub_siteExpectation_chainNeighborhood_le
      (fun X : ChainSupport L R ↦ X) g.term g.hermitian g.supported b₀
      g.sum_norm_terms_containing_le hqq S hA ℓ hℓ t
  have hcommon (S : Finset (Fin L)) (hS : S ⊆ Z)
      (A : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ)
      (hA : Entropy.IsSupportedOn (n := fun _ ↦ q * q) A S) :
      ‖heisenbergEvolution K' t A - siteExpectation (q * q) B
        (heisenbergEvolution K' t A)‖ ≤
          2 * (a * (S.card : ℝ) ^ 2 * ‖A‖ * Real.exp (v * |t| - ℓ / 2)) := by
    let N := chainNeighborhood S ℓ
    have hNB : N ⊆ B := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hS hx, hxy⟩
    let τA := heisenbergEvolution K' t A
    let A₀ := siteExpectation (q * q) N τA
    let P := siteExpectationLM (q * q) B
    have hfix : P A₀ = A₀ :=
      siteExpectation_of_mem_supportedOperators B
        (supportedOperators_mono (Finset.coe_subset.mpr hNB)
          (siteExpectation_mem_supportedOperators N τA))
    have heq : τA - P τA = (τA - A₀) - P (τA - A₀) := by
      rw [map_sub, hfix]
      abel
    calc
      _ = ‖(τA - A₀) - P (τA - A₀)‖ := congrArg norm heq
      _ ≤ ‖τA - A₀‖ + ‖P (τA - A₀)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖τA - A₀‖ := by
        have := norm_siteExpectation_le B (τA - A₀)
        change ‖P (τA - A₀)‖ ≤ ‖τA - A₀‖ at this
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hloc S A hA) (by norm_num)
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  let A (X : ChainSupport L R) (b : Bool) := F * T X b * Fᴴ - T X b
  let δ := (LinearMap.id - siteExpectationLM (q * q) B).comp
    (LinearMap.mulLeftRight ℂ
      (NormedSpace.exp (t • (Complex.I • K')), NormedSpace.exp ((-t) • (Complex.I • K'))))
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ X ∈ C, ∑ b : Bool, A X b := by
    rw [show K' = F * h.doubled.operator * Fᴴ from h.swappedDoubled_operator D]
    exact hsum
  have hsumδ : G - siteExpectation (q * q) B G = ∑ X ∈ C, ∑ b : Bool, δ (A X b) := by
    change δ (K' - K) = _
    rw [hdiff, map_sum]
    simp only [map_sum]
  have ha : 0 ≤ a := by
    have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact (div_pos (by positivity) hden).le
  have hterm (X : ChainSupport L R) (hXC : X ∈ C) (b : Bool) :
      ‖δ (A X b)‖ ≤
        4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - ℓ / 2) := by
    have hspec := h.partialSwap_term_difference_spec D X b
    have hc : (X.1.card : ℝ) ≤ (R + 1 : ℝ) := by exact_mod_cast X.2.card_le
    have hn : ‖A X b‖ ≤ 2 * |J| :=
      hspec.2.2.trans (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))
    have hbase := hcommon X.1
      (Finset.subset_biUnion_of_mem (fun X ↦ X.1) hXC) (A X b) hspec.1
    apply hbase.trans
    calc
      2 * (a * (X.1.card : ℝ) ^ 2 * ‖A X b‖ * Real.exp (v * |t| - ℓ / 2)) ≤
          2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - ℓ / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) ha)
          hn (norm_nonneg _) (mul_nonneg ha (sq_nonneg _))
      _ = _ := by ring
  have hsumBound : ‖G - siteExpectation (q * q) B G‖ ≤
      (C.card : ℝ) * 2 *
        (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - ℓ / 2)) := by
    rw [hsumδ]
    calc
      _ ≤ ∑ X ∈ C, ‖∑ b : Bool, δ (A X b)‖ := norm_sum_le _ _
      _ ≤ ∑ X ∈ C, ∑ b : Bool, ‖δ (A X b)‖ :=
        Finset.sum_le_sum (fun X _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _X ∈ C, ∑ _b : Bool,
          4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - ℓ / 2) :=
        Finset.sum_le_sum (fun X hXC ↦ Finset.sum_le_sum (fun b _ ↦ hterm X hXC b))
      _ = _ := by simp [mul_assoc]
  have hc : (C.card : ℝ) * 2 ≤
      (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ) := by
    exact_mod_cast hcount
  have hsharp : ‖G - siteExpectation (q * q) B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        ((boundaryEdges L D).card : ℝ) * Real.exp (v * |t| - ℓ / 2) := by
    calc
      _ ≤ (C.card : ℝ) * 2 *
          (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - ℓ / 2)) := hsumBound
      _ ≤ ((chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ)) *
          (4 * |J| * a * (R + 1 : ℝ) ^ 2 * Real.exp (v * |t| - ℓ / 2)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hb : (boundaryEdges L D).card ≤ L := by
    calc
      _ ≤ (Finset.range (L - 1)).card := Finset.card_filter_le _ _
      _ = L - 1 := Finset.card_range _
      _ ≤ L := Nat.sub_le _ _
  have hb' : ((boundaryEdges L D).card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hb
  exact hsharp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb' (by positivity)) (Real.exp_pos _).le)

end TNLean.MPS.AreaLaw
