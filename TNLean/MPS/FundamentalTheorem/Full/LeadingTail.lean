/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.LeadingPartner
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap
import TNLean.MPS.FundamentalTheorem.Full.ProportionalTail

/-!
# Leading phase relation and erased-tail asymptotics

This module records the leading peeling data obtained from eventual
proportionality of two restricted BNT block families.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem II.1, line 1182.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section LeadingTail

/-- **Leading phase relation and leading-erased tail asymptotic.**

Source context: arXiv:1606.00608, Theorem II.1, line 1182. After the leading
`B`-block has been shown to have a non-decaying overlap with some `A`-block,
the leading-partner lemma identifies that block as the leading `A`-block.
Corollary eqV then supplies the phase relation used to start the peeling
argument, and the selected-summand cancellation gives the leading-erased tail
asymptotic.

The conclusion keeps the proportionality scalar sequence for the assembled
weighted sums together with the normalized leading-tail estimate.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma exists_leading_phase_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ (ζ : ℂ) (c : ℕ → ℂ),
      ‖ζ‖ = 1 ∧
      (∀ N : ℕ,
        mpvState (d := d) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N =
          ζ ^ N • mpvState (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N) ∧
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      (∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) ∧
      Tendsto
        (fun N : ℕ =>
          ‖(μA ⟨0, Nat.pos_of_ne_zero hrA⟩ ^ N)⁻¹ •
            ((∑ j ∈ Finset.univ.erase ⟨0, Nat.pos_of_ne_zero hrA⟩,
                (μA j) ^ N • mpvState (d := d) (A j) N) -
              c N •
                (∑ k ∈ Finset.univ.erase ⟨0, Nat.pos_of_ne_zero hrB⟩,
                  (μB k) ^ N • mpvState (d := d) (B k) N))‖)
        atTop (nhds (0 : ℝ)) := by
  classical
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hnd_exists : ∃ j : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0) := by
    by_contra h
    push Not at h
    exact fixed_right_leading_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp (by simpa [b0] using h)
  obtain ⟨j, hnd⟩ := hnd_exists
  have hj : j = a0 :=
    leading_right_nondecaying_partner_eq_leading_left_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp j (by simpa [b0] using hnd)
  subst j
  have hnd0 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B b0) N) atTop (nhds 0) := by
    simpa using hnd
  obtain ⟨ζ, hζ, hPhase⟩ :=
    exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT
      A B hA hB a0 b0 hnd0
  obtain ⟨c, hc, hState, hTail⟩ :=
    exists_dominant_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hζ (by simpa [a0, b0] using hPhase) hProp
  exact ⟨ζ, c, hζ, by simpa [a0, b0] using hPhase, hc, hState, hTail⟩

end LeadingTail

end MPSTensor
