/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.WeightedGHZ
import TNLean.Circuit.EntropySupport
import TNLean.MPS.AreaLaw.Basic
import QICLean.Analysis.CfcConjugation
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.GroundEnergyBounds
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# A hard truncation whose flat sector enters the low-energy space

ALVV, arXiv:1602.08828v2, Section 4.2, Definition 4.3 and Proposition 4.4(1),
uses the actual regional hard truncation. The truncated-side restricted error
cannot have a length-independent bound under just `t > η`: the clipped flat
sector can itself lie below the requested low-energy cutoff.

The example has one positive contraction on each nearest-neighbor bond. Its
crossing interaction depends on both sites, and the final internal interaction
also acts on both end sites. Both actual ground energies are `3/4`. At `t = 3/2`
and `η = 1`, a unit vector in the closed truncated low-energy space has
discrepancy `K - 3/2`. No claim about the original-side restricted error is made.

The source comparison and the distinction from a sufficiently large cutoff are
recorded in `docs/audits/2026-10-29_hard_truncation_cutoff.md` and the QICLean note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
The source paper is unchanged.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.HardTruncationCutoff

/-- The actual qubit chain has sites `0, …, K+1`. -/
abbrev Config (K : ℕ) := Fin (K + 2) → Fin 2

private def bit {K : ℕ} (i : Fin (K + 2)) (σ : Config K) : ℝ := (σ i).val

private theorem bit_bounds {K : ℕ} (i : Fin (K + 2)) (σ : Config K) :
    0 ≤ bit i σ ∧ bit i σ ≤ 1 := by
  dsimp only [bit]
  constructor
  · positivity
  · exact_mod_cast (show (σ i).val ≤ 1 by omega)

private def oneSite (K : ℕ) (i : Fin (K + 2)) : Matrix (Config K) (Config K) ℂ :=
  diagonal fun σ ↦ (bit i σ : ℂ)

private def boundaryWeight (K : ℕ) (σ : Config K) : ℝ :=
  (1 - bit (0 : Fin (K + 2)) σ / 4) * (1 - bit (1 : Fin (K + 2)) σ)

private def internalWeight (K : ℕ) (j : Fin K) (σ : Config K) : ℝ :=
  if j.val + 1 = K then
    (bit ⟨K, by omega⟩ σ + bit ⟨K + 1, by omega⟩ σ) / 2
  else bit ⟨j.val + 1, by omega⟩ σ

private def boundary (K : ℕ) : Matrix (Config K) (Config K) ℂ :=
  diagonal fun σ ↦ (boundaryWeight K σ : ℂ)

private def internalTerm (K : ℕ) (j : Fin K) : Matrix (Config K) (Config K) ℂ :=
  diagonal fun σ ↦ (internalWeight K j σ : ℂ)

/-- The crossing bond is `(I-P₁(0)/4)P₀(1)`; internal bonds are the indicated
one-site projections, with the final bond the average of its two projections.
This is an explicit original-chain input to ALVV Definition 4.3. -/
def bondTerm (K : ℕ) : Fin (K + 1) → Matrix (Config K) (Config K) ℂ :=
  Fin.cases (boundary K) (internalTerm K)

/-- The actual sum of the internal bonds of the contiguous region `{1,…,K+1}`. -/
def regionalHamiltonian (K : ℕ) : Matrix (Config K) (Config K) ℂ :=
  ∑ j : Fin K, internalTerm K j

/-- The original Hamiltonian, with exactly one term on each bond. -/
def hamiltonian (K : ℕ) : Matrix (Config K) (Config K) ℂ :=
  ∑ i, bondTerm K i

/-- ALVV's actual hard truncation at regional minimum zero and `t=3/2`. -/
def truncatedHamiltonian (K : ℕ) : Matrix (Config K) (Config K) ℂ :=
  energyTruncation (regionalHamiltonian K) (3 / 2) + boundary K

/-- The closed spectral projection at the actual ground energy `3/4` plus `η=1`. -/
def truncatedLowProjection (K : ℕ) : Matrix (Config K) (Config K) ℂ :=
  cfc (fun x : ℝ ↦ if x ≤ 7 / 4 then 1 else 0) (truncatedHamiltonian K)

private def regionalWeight (K : ℕ) (σ : Config K) : ℝ := ∑ j, internalWeight K j σ

private def totalWeight (K : ℕ) (σ : Config K) : ℝ :=
  boundaryWeight K σ + regionalWeight K σ

private def truncatedWeight (K : ℕ) (σ : Config K) : ℝ :=
  min (regionalWeight K σ) (3 / 2) + boundaryWeight K σ

private theorem regional_diagonal (K : ℕ) :
    regionalHamiltonian K = diagonal (fun σ ↦ (regionalWeight K σ : ℂ)) := by
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [regionalHamiltonian, internalTerm, regionalWeight]
  · simp [regionalHamiltonian, internalTerm, diagonal_apply_ne _ h]

/-- The region/complement decomposition is derived from the original bond sum. -/
theorem hamiltonian_eq_region_add_boundary (K : ℕ) :
    hamiltonian K = regionalHamiltonian K + bondTerm K 0 := by
  simp only [hamiltonian, bondTerm, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    regionalHamiltonian]
  exact add_comm _ _

/-- The regional operator is exactly the original bond sum selected by the
contiguous site interval `{1,…,K+1}`, as in ALVV Definition 4.3. -/
theorem regionalHamiltonian_eq_internal_bond_sum (K : ℕ) :
    regionalHamiltonian K = ∑ i ∈ Finset.univ.filter
      (fun i : Fin (K + 1) ↦ 1 ≤ i.val ∧ i.val + 1 < K + 2), bondTerm K i := by
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  have hsucc (j : Fin K) : 1 ≤ j.succ.val ∧ j.succ.val + 1 < K + 2 := by
    dsimp
    omega
  simp only [Fin.val_zero, show ¬ (1 ≤ 0 ∧ 0 + 1 < K + 2) by omega,
    ite_false, hsucc, ite_true, zero_add, bondTerm, Fin.cases_succ, regionalHamiltonian]

private theorem total_diagonal (K : ℕ) :
    hamiltonian K = diagonal (fun σ ↦ (totalWeight K σ : ℂ)) := by
  rw [hamiltonian_eq_region_add_boundary, regional_diagonal]
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [bondTerm, boundary, totalWeight]
  · simp [bondTerm, boundary, diagonal_apply_ne _ h]

private theorem truncated_diagonal (K : ℕ) :
    truncatedHamiltonian K = diagonal (fun σ ↦ (truncatedWeight K σ : ℂ)) := by
  rw [truncatedHamiltonian, regional_diagonal, energyTruncation,
    Matrix.cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [boundary, truncatedWeight]
  · simp [boundary, diagonal_apply_ne _ h]

private theorem internal_bounds (K : ℕ) (j : Fin K) (σ : Config K) :
    0 ≤ internalWeight K j σ ∧ internalWeight K j σ ≤ 1 := by
  unfold internalWeight
  split_ifs
  · obtain ⟨h0, h1⟩ := bit_bounds (⟨K, by omega⟩ : Fin (K + 2)) σ
    obtain ⟨h0', h1'⟩ := bit_bounds (⟨K + 1, by omega⟩ : Fin (K + 2)) σ
    constructor <;> linarith
  · exact bit_bounds _ _

private theorem boundary_bounds (K : ℕ) (σ : Config K) :
    0 ≤ boundaryWeight K σ ∧ boundaryWeight K σ ≤ 1 := by
  obtain ⟨h0, h1⟩ := bit_bounds (0 : Fin (K + 2)) σ
  obtain ⟨h0', h1'⟩ := bit_bounds (1 : Fin (K + 2)) σ
  dsimp only [boundaryWeight]
  constructor
  · exact mul_nonneg (by linarith) (by linarith)
  · nlinarith [mul_nonneg (bit (0 : Fin (K + 2)) σ) (1 - bit (1 : Fin (K + 2)) σ)]

private theorem diagonal_positive_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (0 : Matrix ι ι ℂ) ≤ diagonal (fun i ↦ (w i : ℂ)) ∧
      diagonal (fun i ↦ (w i : ℂ)) ≤ 1 := by
  constructor
  · exact (Matrix.PosSemidef.diagonal fun i ↦ Complex.zero_le_real.mpr (hw i).1).nonneg
  · apply Matrix.le_iff.mpr
    have heq : (1 : Matrix ι ι ℂ) - diagonal (fun i ↦ (w i : ℂ)) =
        diagonal (fun i ↦ ((1 - w i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h, diagonal_apply, Complex.ofReal_sub]
    rw [heq]
    exact Matrix.PosSemidef.diagonal fun i ↦ Complex.zero_le_real.mpr (by linarith [(hw i).2])

/-- Every actual original bond term is a positive contraction. -/
theorem bondTerm_positive_contraction (K : ℕ) (i : Fin (K + 1)) :
    0 ≤ bondTerm K i ∧ bondTerm K i ≤ 1 := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact diagonal_positive_contraction _ (boundary_bounds K)
  · exact diagonal_positive_contraction _ (internal_bounds K j)

private theorem oneSite_mem {K : ℕ} (i : Fin (K + 2)) (S : Set (Fin (K + 2)))
    (hi : i ∈ S) : oneSite K i ∈ QuantumCircuit.supportedOperators 2 S := by
  apply QuantumCircuit.supportedOperators_mono (Set.singleton_subset_iff.mpr hi)
  simpa only [oneSite, bit, Complex.ofReal_natCast] using
    QuantumCircuit.diagonal_comp_eval_mem_supportedOperators i (fun x ↦ (x.val : ℂ))

private theorem boundary_formula (K : ℕ) :
    boundary K = (1 - (1 / 4 : ℂ) • oneSite K 0) * (1 - oneSite K 1) := by
  simp only [boundary, oneSite, ← diagonal_one, ← diagonal_smul, diagonal_sub,
    diagonal_mul_diagonal]
  congr 1
  funext σ
  simp only [boundaryWeight, Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem internal_formula (K : ℕ) (j : Fin K) :
    internalTerm K j = if j.val + 1 = K then
      (1 / 2 : ℂ) • (oneSite K ⟨K, by omega⟩ + oneSite K ⟨K + 1, by omega⟩)
    else oneSite K ⟨j.val + 1, by omega⟩ := by
  unfold internalTerm internalWeight
  split_ifs <;> ext σ τ <;>
    simp [oneSite, diagonal_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_div] <;> ring

/-- Actual nearest-neighbor supports are derived for all terms, including both endpoints. -/
theorem bondTerm_supported (K : ℕ) (i : Fin (K + 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin (K + 2) ↦ 2) (bondTerm K i)
      (interval (K + 2) i.val (i.val + 2)) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    change boundary K ∈ _
    rw [boundary_formula]
    apply QuantumCircuit.mul_mem_supportedOperators
    · exact Submodule.sub_mem _ (QuantumCircuit.one_mem_supportedOperators _)
        (Submodule.smul_mem _ _ (oneSite_mem 0 _ (by simp [interval])))
    · exact Submodule.sub_mem _ (QuantumCircuit.one_mem_supportedOperators _)
        (oneSite_mem 1 _ (by simp [interval]))
  · apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    change internalTerm K j ∈ _
    rw [internal_formula]
    split_ifs with hj
    · apply Submodule.smul_mem
      apply Submodule.add_mem
      · exact oneSite_mem _ _ (by simp only [interval, Finset.mem_filter,
          Finset.mem_univ, true_and]; dsimp; omega)
      · exact oneSite_mem _ _ (by simp only [interval, Finset.mem_filter,
          Finset.mem_univ, true_and]; dsimp; omega)
    · exact oneSite_mem _ _ (by simp only [interval, Finset.mem_filter,
        Finset.mem_univ, true_and]; dsimp; omega)

private def groundConfig (K : ℕ) : Config K := fun i ↦ if i = 0 then 1 else 0
private def highConfig (K : ℕ) : Config K := fun _ ↦ 1

private theorem regional_nonneg (K : ℕ) (σ : Config K) : 0 ≤ regionalWeight K σ :=
  Finset.sum_nonneg fun j _ ↦ (internal_bounds K j σ).1

private theorem regional_ge_one_of_first_bit {K : ℕ} (hK : 2 ≤ K)
    (σ : Config K) (hσ : σ 1 = 1) : 1 ≤ regionalWeight K σ := by
  have hfirst : internalWeight K ⟨0, by omega⟩ σ = 1 := by
    simp [internalWeight, bit, show 0 + 1 ≠ K by omega, hσ]
  have hle := Finset.single_le_sum (fun j _ ↦ (internal_bounds K j σ).1)
    (Finset.mem_univ (⟨0, by omega⟩ : Fin K))
  simpa only [regionalWeight, hfirst] using hle

private theorem ground_lower_bounds {K : ℕ} (hK : 2 ≤ K) (σ : Config K) :
    3 / 4 ≤ totalWeight K σ ∧ 3 / 4 ≤ truncatedWeight K σ := by
  have hA := regional_nonneg K σ
  have hB := (boundary_bounds K σ).1
  have hbit := bit_bounds (0 : Fin (K + 2)) σ
  by_cases hσ : σ 1 = 0
  · have hBeq : boundaryWeight K σ = 1 - bit (0 : Fin (K + 2)) σ / 4 := by
      simp [boundaryWeight, bit, hσ]
    have hmin : 0 ≤ min (regionalWeight K σ) (3 / 2) := le_min hA (by norm_num)
    dsimp only [totalWeight, truncatedWeight]
    constructor <;> linarith
  · have hσ' : σ 1 = 1 := by apply Fin.ext; have := (σ 1).isLt; omega
    have hAge := regional_ge_one_of_first_bit hK σ hσ'
    have hmin : 1 ≤ min (regionalWeight K σ) (3 / 2) := le_min hAge (by norm_num)
    dsimp only [totalWeight, truncatedWeight]
    constructor <;> linarith

private theorem ground_weights (K : ℕ) :
    regionalWeight K (groundConfig K) = 0 ∧
      totalWeight K (groundConfig K) = 3 / 4 ∧
      truncatedWeight K (groundConfig K) = 3 / 4 := by
  have hz : regionalWeight K (groundConfig K) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hK : K ≠ 0 := by omega
    simp [internalWeight, bit, groundConfig, Fin.ext_iff, hK,
      show j.val + 1 ≠ 0 by omega]
  simp [totalWeight, truncatedWeight, boundaryWeight, bit, groundConfig, hz]

/-- Both actual Hamiltonians have attained ground energy `3/4`; the regional
Hamiltonian has attained minimum zero. No ground energy is supplied as input. -/
theorem actual_ground_energies {K : ℕ} (hK : 2 ≤ K) :
    let Ω : Config K → ℂ := Pi.single (groundConfig K) 1
    star Ω ⬝ᵥ Ω = 1 ∧ regionalHamiltonian K *ᵥ Ω = 0 ∧
      (regionalHamiltonian K).PosSemidef ∧
      hamiltonian K *ᵥ Ω = (3 / 4 : ℂ) • Ω ∧
      (hamiltonian K - (3 / 4 : ℂ) • 1).PosSemidef ∧
      truncatedHamiltonian K *ᵥ Ω = (3 / 4 : ℂ) • Ω ∧
      (truncatedHamiltonian K - (3 / 4 : ℂ) • 1).PosSemidef := by
  intro Ω
  have hdiag_lower (w : Config K → ℝ) (hw : ∀ σ, 3 / 4 ≤ w σ) :
      (diagonal (fun σ ↦ (w σ : ℂ)) - (3 / 4 : ℂ) • 1).PosSemidef := by
    rw [smul_one_eq_diagonal, diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro σ
    change 0 ≤ (w σ : ℂ) - 3 / 4
    exact_mod_cast (sub_nonneg.mpr (hw σ) : (0 : ℝ) ≤ w σ - 3 / 4)
  obtain ⟨hA, hH, hF⟩ := ground_weights K
  refine ⟨by simp [Ω], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regional_diagonal]
    simp [Ω, diagonal_mulVec_single, hA]
  · rw [regional_diagonal]
    exact Matrix.PosSemidef.diagonal fun σ ↦ Complex.zero_le_real.mpr (regional_nonneg K σ)
  · rw [total_diagonal]
    simp [Ω, diagonal_mulVec_single, ← Pi.single_smul', hH]
  · rw [total_diagonal]
    exact hdiag_lower _ fun σ ↦ (ground_lower_bounds hK σ).1
  · rw [truncated_diagonal]
    simp [Ω, diagonal_mulVec_single, ← Pi.single_smul', hF]
  · rw [truncated_diagonal]
    exact hdiag_lower _ fun σ ↦ (ground_lower_bounds hK σ).2

private theorem high_weights (K : ℕ) :
    regionalWeight K (highConfig K) = K ∧ boundaryWeight K (highConfig K) = 0 := by
  have hone (j : Fin K) : internalWeight K j (highConfig K) = 1 := by
    simp [internalWeight, bit, highConfig]
  simp [regionalWeight, hone, boundaryWeight, bit, highConfig]

/-- A unit high-energy basis vector lies in the actual closed truncated low-energy
space at `3/4+1`, while its original energy is `K`. ALVV Proposition 4.4(1). -/
theorem high_vector_in_truncated_low_space {K : ℕ} (hK : 2 ≤ K) :
    let ψ : EuclideanSpace ℂ (Config K) := WithLp.toLp 2 (Pi.single (highConfig K) 1)
    ‖ψ‖ = 1 ∧ hamiltonian K *ᵥ WithLp.ofLp ψ = (K : ℂ) • WithLp.ofLp ψ ∧
      truncatedHamiltonian K *ᵥ WithLp.ofLp ψ = (3 / 2 : ℂ) • WithLp.ofLp ψ ∧
      truncatedLowProjection K *ᵥ WithLp.ofLp ψ = WithLp.ofLp ψ := by
  intro ψ
  obtain ⟨hA, hB⟩ := high_weights K
  have hKreal : (3 / 2 : ℝ) ≤ K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hHt : truncatedWeight K (highConfig K) = 3 / 2 := by
    simp [truncatedWeight, hA, hB, min_eq_right hKreal]
  refine ⟨by simp [ψ, EuclideanSpace.norm_eq], ?_, ?_, ?_⟩
  · rw [total_diagonal]
    simp [ψ, diagonal_mulVec_single, ← Pi.single_smul', totalWeight, hA, hB]
  · rw [truncated_diagonal]
    simp [ψ, diagonal_mulVec_single, ← Pi.single_smul', hHt]
  · rw [truncatedLowProjection, truncated_diagonal,
      Matrix.cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    norm_num [ψ, diagonal_mulVec_single, hHt]

/-- The actual truncated-side restricted discrepancy grows without bound with
the region length, at fixed `t=3/2>η=1`. Only this side of ALVV Proposition 4.4(1)
is refuted; the original-side projection is not used. -/
theorem truncated_low_discrepancy_lower_bound {K : ℕ} (hK : 2 ≤ K) :
    (K : ℝ) - 3 / 2 ≤
      ‖(hamiltonian K - truncatedHamiltonian K) * truncatedLowProjection K‖ := by
  obtain ⟨hA, hB⟩ := high_weights K
  have hKreal : (3 / 2 : ℝ) ≤ K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hHt : truncatedWeight K (highConfig K) = 3 / 2 := by
    simp [truncatedWeight, hA, hB, min_eq_right hKreal]
  have hnonneg : 0 ≤ (K : ℝ) - 3 / 2 := by linarith
  have htotal : totalWeight K (highConfig K) = (K : ℝ) := by simp [totalWeight, hA, hB]
  rw [total_diagonal, truncatedLowProjection, truncated_diagonal,
    Matrix.cfc_diagonal _ _ ((Set.finite_range _).continuousOn _), diagonal_sub,
    diagonal_mul_diagonal, Matrix.l2_opNorm_diagonal]
  -- Bound the sup norm below by the entry at the high-energy configuration, whose
  -- discrepancy weight is exactly `K - 3/2` since `3/2 ≤ 7/4` keeps it in the window.
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ (highConfig K))
  simp only [htotal, hHt, if_pos (show (3 / 2 : ℝ) ≤ 7 / 4 by norm_num),
    Complex.ofReal_one, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- No length-independent constant bounds the actual truncated-side error for
all positive-contraction nearest-neighbor chains under merely `t>η`.
The fixed source parameters here are `t=3/2`, `η=1`, and ground energy `3/4`. -/
theorem exists_truncated_low_discrepancy_gt (C : ℝ) :
    ∃ K : ℕ, 2 ≤ K ∧ C <
      ‖(hamiltonian K - truncatedHamiltonian K) * truncatedLowProjection K‖ := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max C 0 + 2)
  have hK2real : (2 : ℝ) < K := by linarith [le_max_right C 0]
  have hK2 : 2 ≤ K := by exact_mod_cast hK2real.le
  refine ⟨K, hK2, lt_of_lt_of_le ?_ (truncated_low_discrepancy_lower_bound hK2)⟩
  linarith [le_max_left C 0]

end TNLean.MPS.AreaLaw.HardTruncationCutoff
