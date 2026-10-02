/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductParentHamiltonian

/-!
# Continuity of independent-bond parent Hamiltonians

A continuous bond vector gives continuous local parent terms and a continuous
Hamiltonian on each finite chain. Applied to the normalized direct-sum bond,
this is the continuity assertion in Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
-/

namespace MPSTensor

/-- The complementary rank-one operator depends continuously on its bond vector.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem continuous_bondPenalty (q : ℕ) :
    Continuous (bondPenalty (q := q)) := by
  apply continuous_matrix
  intro i j
  exact continuous_const.sub ((continuous_apply i).mul (continuous_apply j).star)

/-- Embedding a bond penalty at a fixed position preserves its continuous
parameter dependence. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem continuous_bondPenaltyAt {q N : ℕ} (hN : 1 ≤ N) (i : Fin N) :
    Continuous (fun η : Fin q → ℂ => bondPenaltyAt η hN i) := by
  apply continuous_matrix
  intro s t
  simp only [bondPenaltyAt, MPOTensor.embedLocalOperator_apply,
    MPOTensor.oneSiteOperator]
  split_ifs
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_bondPenalty q))
  · exact continuous_const

/-- The finite-chain independent-bond Hamiltonian varies continuously with
its bond vector. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem continuous_bondProductParentHamiltonian {q N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun η : Fin q → ℂ => bondProductParentHamiltonian η hN) := by
  exact continuous_finsetSum _ fun i _ => continuous_bondPenaltyAt hN i

/-- Encoding the normalized bond by a single physical index preserves
continuity. Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem continuous_normalizedBondInterpolationVector {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (normalizedBondInterpolationVector D₀ D₁) := by
  apply continuous_pi
  intro x
  exact (continuous_apply _).comp
    ((continuous_apply _).comp (continuous_normalizedBondInterpolationMatrix h₀ h₁))

/-- The normalized direct-sum bond path has continuous finite-chain parent
Hamiltonians. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem continuous_normalizedBondInterpolation_parent {D₀ D₁ N : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (hN : 1 ≤ N) :
    Continuous (fun γ : ℝ => bondProductParentHamiltonian
      (normalizedBondInterpolationVector D₀ D₁ γ) hN) :=
  (continuous_bondProductParentHamiltonian hN).comp
    (continuous_normalizedBondInterpolationVector h₀ h₁)

end MPSTensor
