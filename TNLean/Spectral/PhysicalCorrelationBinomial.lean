/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DecayingCorrelations
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# All-separation binomial expansion of physical correlations

The complementary transfer map is decomposed into generalized eigenspaces
using Mathlib. On each component the commuting binomial formula gives an
exact finite expansion, including at zero separation and zero eigenvalue.
No diagonalizability or assumed spectral expansion is required.

Source: arXiv:2011.12127, Section II.B.3, lines 433–441.

**Local fix (Jordan factors and nilpotent transients):** The source's
pure-exponential claim needs the all-separation binomial correction; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private theorem transfer_pairing_pow_binomial {D : ℕ}
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    {μ : ℂ} {v : Matrix (Fin D) (Fin D) ℂ} {k : ℕ}
    (hv : ((T - μ • 1) ^ k) v = 0) (n : ℕ) :
    F ((T ^ n) v) = ∑ j ∈ Finset.range k,
      (n.choose j : ℂ) * μ ^ (n - j) * F (((T - μ • 1) ^ j) v) := by
  classical
  let N := T - μ • 1
  have hcomm : Commute N (μ • 1) := (Algebra.commutes μ N).symm
  have hbin : F ((T ^ n) v) = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * μ ^ (n - j) * F ((N ^ j) v) := by
    conv_lhs => rw [show T = N + μ • 1 by simp [N], hcomm.add_pow n]
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply,
      Module.End.natCast_apply, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply, map_smul, map_nsmul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hbin]
  rcases le_total k (n + 1) with hk | hk
  · symm
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    have hkj : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    have hzero : (N ^ j) v = 0 := Module.End.pow_map_zero_of_le hkj hv
    change (n.choose j : ℂ) * μ ^ (n - j) * F ((N ^ j) v) = 0
    rw [hzero, map_zero, mul_zero]
  · apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    have hnj : n < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hnj]

private theorem transfer_pairing_exists_binomial {D : ℕ}
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    ∃ s : Finset ℂ, ∃ c : ℂ → ℕ → ℂ,
      (∀ μ ∈ s, T.HasEigenvalue μ) ∧ ∀ n : ℕ,
        F ((T ^ n) Z) = ∑ μ ∈ s, ∑ j ∈ Finset.range (T.maxGenEigenspaceIndex μ),
          (n.choose j : ℂ) * μ ^ (n - j) * c μ j := by
  classical
  have hZ : Z ∈ ⨆ μ : ℂ, T.maxGenEigenspace μ := by
    rw [T.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨v, hv, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hZ
  have hnil (μ : ℂ) : ((T - μ • 1) ^ T.maxGenEigenspaceIndex μ) (v μ) = 0 := by
    have h := hv μ
    rw [T.maxGenEigenspace_eq] at h
    simpa only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker,
      Algebra.algebraMap_eq_smul_one] using h
  refine ⟨v.support, fun μ j => F (((T - μ • 1) ^ j) (v μ)), ?_, ?_⟩
  · intro μ hμ
    apply Module.End.hasEigenvalue_of_hasGenEigenvalue
      (k := T.maxGenEigenspaceIndex μ)
    rw [Module.End.hasGenEigenvalue_iff]
    intro hbot
    have h := hv μ
    rw [T.maxGenEigenspace_eq, hbot, Submodule.mem_bot] at h
    exact (Finsupp.mem_support_iff.mp hμ) h
  · intro n
    rw [← hsum, map_finsuppSum, map_finsuppSum]
    apply Finset.sum_congr rfl
    intro μ _
    exact transfer_pairing_pow_binomial T F (hnil μ) n

/-- Every centered physical connected correlator has an exact finite binomial
spectral expansion at every separation. The cutoff is the generalized-eigenspace
stabilization index of the actual complementary transfer map; zero eigenvalues
are retained rather than discarded. -/
theorem physicalConnectedCorrelator_exists_binomial_expansion {d D : ℕ}
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) :
    let T := Kraus.transferMap A - fixedPointProj ρ hρ
    ∃ s : Finset ℂ, ∃ c : ℂ → ℕ → ℂ,
      (∀ μ ∈ s, T.HasEigenvalue μ) ∧
      ∀ n : ℕ, physicalConnectedCorrelator A ρ hρ L₁ L₂ X Y n =
        ∑ μ ∈ s, ∑ j ∈ Finset.range (T.maxGenEigenspaceIndex μ),
          (n.choose j : ℂ) * μ ^ (n - j) * c μ j := by
  exact transfer_pairing_exists_binomial
    (Kraus.transferMap A - fixedPointProj ρ hρ)
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (physicalObservableTransfer A L₁ X))
    (physicalObservableTransfer A L₂ Y ρ -
      fixedPointProj ρ hρ (physicalObservableTransfer A L₂ Y ρ))

end MPSTensor
