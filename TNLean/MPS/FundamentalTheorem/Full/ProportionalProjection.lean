/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Adjusted scalar projections for proportional BNT expansions

This module packages the scalar-norm and projection identities obtained from
eventual proportionality of assembled BNT block tensors. It deliberately stops
before any fixed-block coefficient isolation or tail linear-independence
argument.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  lines 1170--1192.
-/

open scoped BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section ProportionalProjection

/-- **Eventual adjusted scalar and normalized projected sums.**

Source context: arXiv:1606.00608, lines 1170--1192. In the proportional
block-selection argument, one first obtains an eventual scalar sequence relating
the assembled weighted MPV sums, then divides by selected nonzero weights, and
then projects against a fixed block. If the two normalized weighted state sums
have norms tending to one, the same scalar sequence also has adjusted modulus
tending to one. This lemma packages exactly these two consequences; it does
not assert any fixed-block coefficient identity or any linear independence of
the remaining tail. -/
lemma exists_adjusted_scalar_norm_and_inner_sequence_of_eventuallyNonzeroProportionalMPV₂
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (μ ν : ℂ) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hA_norm : Tendsto
      (fun N : ℕ =>
        ‖(μ ^ N)⁻¹ •
          (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N)‖)
      atTop (nhds (1 : ℝ)))
    (hB_norm : Tendsto
      (fun N : ℕ =>
        ‖(ν ^ N)⁻¹ •
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)‖)
      atTop (nhds (1 : ℝ))) :
    ∃ c : ℕ → ℂ,
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      Tendsto (fun N : ℕ => ‖c N * (ν / μ) ^ N‖) atTop (nhds (1 : ℝ)) ∧
      ∀ {D : ℕ} (X : MPSTensor d D),
        ∀ᶠ N in atTop,
          (μ ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            (c N * (ν / μ) ^ N) *
              ((ν ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) := by
  obtain ⟨c, hc, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  have hAdjusted :
      Tendsto (fun N : ℕ => ‖c N * (ν / μ) ^ N‖) atTop (nhds (1 : ℝ)) :=
    tendsto_norm_adjusted_weighted_mpvState_scalar_of_eventually_tendsto_norm_one
      A B c μ ν hμ hν hState hA_norm hB_norm
  have hInner :
      ∀ {D : ℕ} (X : MPSTensor d D),
        ∀ᶠ N in atTop,
          (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) :=
    eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
      A B c hState
  refine ⟨c, hc, hAdjusted, ?_⟩
  intro D X
  refine (hInner X).mono ?_
  intro N hN
  let S : ℂ := ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N
  rw [hN]
  change (μ ^ N)⁻¹ * (c N * S) =
    (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S)
  calc
    (μ ^ N)⁻¹ * (c N * S) = ((μ ^ N)⁻¹ * c N) * S := by ring
    _ = ((c N * (ν / μ) ^ N) * (ν ^ N)⁻¹) * S := by
      rw [adjusted_scalar_factor_eq (c N) μ ν N hμ hν]
    _ = (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S) := by ring

end ProportionalProjection

end MPSTensor
