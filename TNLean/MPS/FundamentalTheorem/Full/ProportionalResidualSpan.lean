/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs

/-!
# Residual-span coefficient extraction

This module contains the linear-algebra coefficient-extraction lemmas used in
the proportional peeling argument for the Fundamental Theorem of MPS.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem `thm1`, line 1182.
-/

open Filter

namespace MPSTensor

section ProportionalResidualSpan

/-- **Selected coefficient extraction modulo a residual span.**

This is a pure linear-algebra form of the coefficient-isolation step. If two
expressions differ only by terms in the span of a residual family, and the
selected vector is not in that residual span, then the selected coefficients
agree.

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. In the paper,
Lemma `Lem1` is used to separate a fixed BNT block from the remaining
contributions. This lemma records the algebraic separation needed once the
appropriate residual-span exclusion has been proved.

**Scope restriction (residual-span exclusion):** The hypothesis
`v₀ ∉ Submodule.span ℂ (Set.range u)` is not a new source hypothesis for
CPSV16; it is the local algebraic condition that must be derived from the BNT
separation argument before this lemma can be used in a source-faithful proof.
See `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma selected_coefficient_eq_of_residual_span
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {κ : Type*} (u : κ → E) {v₀ R S : E} {a b : ℂ}
    (hR : R ∈ Submodule.span ℂ (Set.range u))
    (hS : S ∈ Submodule.span ℂ (Set.range u))
    (hEq : a • v₀ + R = b • v₀ + S)
    (hnot : v₀ ∉ Submodule.span ℂ (Set.range u)) :
    a = b := by
  by_contra hne
  have hdiff_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hdiff_mem : (a - b) • v₀ ∈ Submodule.span ℂ (Set.range u) := by
    have hdiff_eq : (a - b) • v₀ = S - R := by
      calc
        (a - b) • v₀ = a • v₀ - b • v₀ := by rw [sub_smul]
        _ = a • v₀ + R - R - b • v₀ := by abel
        _ = b • v₀ + S - R - b • v₀ := by rw [hEq]
        _ = S - R := by abel
    rw [hdiff_eq]
    exact (Submodule.span ℂ (Set.range u)).sub_mem hS hR
  have hv₀_mem : v₀ ∈ Submodule.span ℂ (Set.range u) := by
    have hscaled :
        (a - b)⁻¹ • ((a - b) • v₀) ∈ Submodule.span ℂ (Set.range u) :=
      (Submodule.span ℂ (Set.range u)).smul_mem _ hdiff_mem
    simpa [smul_smul, inv_mul_cancel₀ hdiff_ne] using hscaled
  exact hnot hv₀_mem

/-- **Eventual selected coefficient extraction modulo residual spans.**

This is the eventual form of
`selected_coefficient_eq_of_residual_span`, suited to the CPSV16 line-1182
peeling argument where Lemma `Lem1` supplies statements only for sufficiently
large chain lengths.

**Scope restriction (residual-span exclusion):** The eventual exclusion of the
selected MPV state from the residual span must be derived from the BNT
separation argument. It is not an additional hypothesis of the source theorem;
see `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma eventually_selected_coefficient_eq_of_residual_span
    {κ : Type*}
    {E : ℕ → Type*} [∀ N, AddCommGroup (E N)] [∀ N, Module ℂ (E N)]
    (u : (N : ℕ) → κ → E N) (v₀ R S : (N : ℕ) → E N)
    (a b : ℕ → ℂ)
    (hR : ∀ᶠ N in atTop, R N ∈ Submodule.span ℂ (Set.range (u N)))
    (hS : ∀ᶠ N in atTop, S N ∈ Submodule.span ℂ (Set.range (u N)))
    (hEq : ∀ᶠ N in atTop, a N • v₀ N + R N = b N • v₀ N + S N)
    (hnot : ∀ᶠ N in atTop, v₀ N ∉ Submodule.span ℂ (Set.range (u N))) :
    ∀ᶠ N in atTop, a N = b N := by
  filter_upwards [hR, hS, hEq, hnot] with N hRN hSN hEqN hnotN
  exact selected_coefficient_eq_of_residual_span (u N) hRN hSN hEqN hnotN

end ProportionalResidualSpan

end MPSTensor
