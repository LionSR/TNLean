/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodeTorusSectors

/-!
# Physical amplitudes of the four primal toric-code torus states

The printed primal tensor fixes its four virtual labels from the physical spins.
Consequently its contraction with arbitrary bond matrices has exactly one surviving
assignment of bond ends. For the four identity/Pauli-Z closures this gives a common
bond-compatibility support and the two explicit seam-parity signs.

Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`, lines
2451–2465; arXiv:1001.3807, Definition 5.6 and Theorem 5.9, lines 1515–1621.
The contraction uses the oriented torus network, including separate opposite bonds.
It agrees with the simple-graph PEPS convention when both periods are at least three.
No claim that these four vectors exhaust a parent-Hamiltonian kernel is made here.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

private abbrev PhysicalConfig := TorusVertex width height →
  ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup

private def primalBondEnds (σ : PhysicalConfig (width := width) (height := height))
    (v : TorusVertex width height) :
    ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup :=
  ((quantumDoublePrimalLabels ToricCodeGroup (σ v)).2.1,
    (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1 + 1, v.2))).2.2.2,
    (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1, v.2 + 1))).2.2.1,
    (quantumDoublePrimalLabels ToricCodeGroup (σ v)).1)

omit [NeZero width] [NeZero height] in
private theorem primalBondEnds_site
    (σ : PhysicalConfig (width := width) (height := height))
    (v : TorusVertex width height) :
    ((primalBondEnds σ v).2.2.2, (primalBondEnds σ v).1,
      (primalBondEnds σ (v.1, v.2 - 1)).2.2.1,
      (primalBondEnds σ (v.1 - 1, v.2)).2.1) =
      quantumDoublePrimalLabels ToricCodeGroup (σ v) := by
  simp [primalBondEnds]

private theorem torusBondNetwork_primal_eq_prod
    (σ : PhysicalConfig (width := width) (height := height))
    (Oh Ov : TorusVertex width height → Matrix ToricCodeGroup ToricCodeGroup ℂ) :
    torusBondNetwork (fun v c => quantumDoublePrimalTensor ToricCodeGroup
      c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov =
      ∏ v, Oh v (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1 + 1, v.2))).2.2.2
          (quantumDoublePrimalLabels ToricCodeGroup (σ v)).2.1 *
        Ov v (quantumDoublePrimalLabels ToricCodeGroup (σ v)).1
          (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1, v.2 + 1))).2.2.1 := by
  classical
  unfold torusBondNetwork
  rw [Finset.sum_eq_single (primalBondEnds σ)]
  · simp only [quantumDoublePrimalTensor, primalBondEnds_site, ite_true,
      Finset.prod_const_one, mul_one]
    rfl
  · intro β _ hβ
    have hbad : ∃ v, ((β v).2.2.2, (β v).1,
        (β (v.1, v.2 - 1)).2.2.1, (β (v.1 - 1, v.2)).2.1) ≠
        quantumDoublePrimalLabels ToricCodeGroup (σ v) := by
      by_contra h
      push Not at h
      apply hβ
      funext v
      have hv := h v
      have hr := h (v.1 + 1, v.2)
      have ht := h (v.1, v.2 + 1)
      exact Prod.ext (congrArg (fun c => c.2.1) hv)
        (Prod.ext (by simpa [primalBondEnds] using congrArg (fun c => c.2.2.2) hr)
          (Prod.ext (by simpa [primalBondEnds] using congrArg (fun c => c.2.2.1) ht)
            (congrArg Prod.fst hv)))
    obtain ⟨v, hv⟩ := hbad
    have hz : (∏ v, quantumDoublePrimalTensor ToricCodeGroup
        (β v).2.2.2 (β v).1 (β (v.1, v.2 - 1)).2.2.1
          (β (v.1 - 1, v.2)).2.1 (σ v)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (by simp [quantumDoublePrimalTensor, hv])
    rw [hz, mul_zero]
  · simp

/-- The virtual labels determined by the physical spins match across each oriented bond.
These are the exact support constraints of the primal toric-code torus contraction. -/
def IsToricCodeBondCompatible
    (σ : PhysicalConfig (width := width) (height := height)) : Prop :=
  ∀ v : TorusVertex width height,
    (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1 + 1, v.2))).2.2.2 =
      (quantumDoublePrimalLabels ToricCodeGroup (σ v)).2.1 ∧
    (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1, v.2 + 1))).2.2.1 =
      (quantumDoublePrimalLabels ToricCodeGroup (σ v)).1

/-- The horizontal and vertical Pauli-Z seam phases, on the labels determined by the
physical configuration. The identity closure contributes no phase. -/
noncomputable def toricCodeSeamPhase (g h : ToricCodeGroup)
    (σ : PhysicalConfig (width := width) (height := height)) : ℂ :=
  ∏ v : TorusVertex width height,
    (if v.1 + 1 = 0 then (-1 : ℂ) ^ ((Multiplicative.toAdd h).val *
      (Multiplicative.toAdd (quantumDoublePrimalLabels ToricCodeGroup (σ v)).2.1).val)
      else 1) *
    (if v.2 + 1 = 0 then (-1 : ℂ) ^ ((Multiplicative.toAdd g).val *
      (Multiplicative.toAdd (quantumDoublePrimalLabels ToricCodeGroup (σ v)).1).val)
      else 1)

open Classical in
/-- The actual twisted primal contraction is the bond-compatibility indicator multiplied
by the two explicit seam signs. There is no omitted normalization factor. -/
theorem toricCodeTorusState_apply (g h : ToricCodeGroup)
    (σ : PhysicalConfig (width := width) (height := height)) :
    toricCodeTorusState g h σ =
      if IsToricCodeBondCompatible σ then toricCodeSeamPhase g h σ else 0 := by
  classical
  unfold toricCodeTorusState torusGClosure
  rw [torusBondNetwork_primal_eq_prod]
  by_cases hc : IsToricCodeBondCompatible σ
  · rw [ite_eq_left hc]
    apply Finset.prod_congr rfl
    intro v _
    simp only [torusHorizontalClosure, torusVerticalClosure, toricCodeBondRep_diagonal]
    split_ifs <;> simp [Matrix.one_apply, (hc v).1, (hc v).2]
  · rw [ite_eq_right hc]
    obtain ⟨v, hv⟩ : ∃ v, ¬
        ((quantumDoublePrimalLabels ToricCodeGroup (σ (v.1 + 1, v.2))).2.2.2 =
          (quantumDoublePrimalLabels ToricCodeGroup (σ v)).2.1 ∧
        (quantumDoublePrimalLabels ToricCodeGroup (σ (v.1, v.2 + 1))).2.2.1 =
          (quantumDoublePrimalLabels ToricCodeGroup (σ v)).1) := by
      simpa only [IsToricCodeBondCompatible, not_forall] using hc
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [torusHorizontalClosure, torusVerticalClosure, toricCodeBondRep_diagonal]
    rcases not_and_or.mp hv with hh | hv
    · split_ifs <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hh]
    · split_ifs <;> simp [Matrix.diagonal_apply, Matrix.one_apply, Ne.symm hv]

open Classical in
/-- With no twists, the literal primal tensor has coefficient one on every compatible
physical configuration and zero elsewhere. -/
@[simp] theorem toricCodeTorusState_one_one_apply
    (σ : PhysicalConfig (width := width) (height := height)) :
    toricCodeTorusState 1 1 σ = if IsToricCodeBondCompatible σ then 1 else 0 := by
  classical
  rw [toricCodeTorusState_apply]
  simp [toricCodeSeamPhase]

/-- All four twists have exactly the same physical support; their difference lies in
relative seam signs, rather than in a restriction to disjoint configuration supports. -/
theorem toricCodeTorusState_ne_zero_iff (g h : ToricCodeGroup)
    (σ : PhysicalConfig (width := width) (height := height)) :
    toricCodeTorusState g h σ ≠ 0 ↔ IsToricCodeBondCompatible σ := by
  classical
  rw [toricCodeTorusState_apply]
  have hp : toricCodeSeamPhase g h σ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    apply mul_ne_zero <;> split_ifs <;> simp
  split_ifs <;> simp_all

end TNLean.PEPS
