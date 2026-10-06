/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphAveragingBondState

/-!
# Nonvanishing of the actual regular averaging graph state

At the all-identity physical bond configuration, the actual regrouped
coefficient counts vertex group labels which agree across every edge, with
the positive site-average normalization. The constant identity labeling is
one such choice. Thus the real part of this coefficient is positive and the
actual graph contraction is nonzero. This includes empty graphs,
disconnected graphs, and isolated vertices without further hypotheses.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019. This is an
auxiliary nonvanishing consequence for the actual regular graph tensor,
not a parent-Hamiltonian or ground-space membership statement.

**Local fix (group-average normalization):** Normalized site averages give
the factor |G|⁻ᴺ. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The all-identity physical bond coefficient counts edge-constant vertex labels. Source: SCP10,
Section 7, lines 2938–3019. -/
theorem graphBondRegrouping_regularAveragingSite_one :
    graphBondRegrouping (Γ := Γ) (graphBondNetwork (graphAveragingSite (leftRegularMatrix G)))
      (fun _ => (1, 1)) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        (Nat.card {q : V → G // ∀ e : Edge Γ, q e.1.2 = q e.1.1} : ℂ) := by
  classical
  rw [graphBondRegrouping_averagingSite_coherent]
  have heq (q : V → G) (e : Edge Γ) :
      (1 : G) = q e.1.2 * (q e.1.1)⁻¹ ↔ q e.1.2 = q e.1.1 := by
    rw [eq_comm, mul_inv_eq_one]
  simp only [leftRegularMatrix_apply, mul_one, heq, Fintype.prod_boole]
  rw [← Finset.mul_sum, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The all-identity coefficient is strictly positive in its real part. Source: SCP10, Section 7,
lines 2938–3019. -/
theorem graphBondRegrouping_regularAveragingSite_one_re_pos :
    0 < (graphBondRegrouping (Γ := Γ)
      (graphBondNetwork (graphAveragingSite (leftRegularMatrix G))) (fun _ => (1, 1))).re := by
  classical
  let : Nonempty {q : V → G // ∀ e : Edge Γ, q e.1.2 = q e.1.1} :=
    ⟨⟨fun _ => 1, fun _ => rfl⟩⟩
  have hcount := Nat.card_pos (α := {q : V → G // ∀ e : Edge Γ, q e.1.2 = q e.1.1})
  rw [graphBondRegrouping_regularAveragingSite_one]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-- The actual regular averaging graph state is nonzero, including empty graphs. Source: SCP10,
Section 7, lines 2938–3019. -/
theorem graphBondNetwork_regularAveragingSite_ne_zero :
    graphBondNetwork (Γ := Γ) (graphAveragingSite (leftRegularMatrix G)) ≠ 0 := by
  have hp := graphBondRegrouping_regularAveragingSite_one_re_pos (Γ := Γ) (G := G)
  intro hzero
  rw [hzero, map_zero, Pi.zero_apply, Complex.zero_re] at hp
  exact lt_irrefl _ hp
end TNLean.PEPS
