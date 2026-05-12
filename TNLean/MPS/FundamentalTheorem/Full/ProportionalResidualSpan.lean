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
  Theorem II.1, line 1182.
-/

open Filter

namespace MPSTensor

section ProportionalResidualSpan

/-- **Linear independence gives residual-span exclusion.**

Source context: arXiv:1606.00608, Theorem II.1, line 1182. The paper uses
CPSV16, Lem1 to separate a fixed BNT block from the remaining contributions.
If the selected vector together with the residual family is linearly
independent, then the selected vector is not in the span of the residual
family; this is the elementary linear-algebra consequence needed by the
residual-span coefficient extraction.

**Scope restriction (derived separation input):** The linear-independence
hypothesis is not a new source hypothesis for CPSV16. In a source-faithful
application it must be derived from the BNT separation argument, or replaced by
the equivalent residual-span exclusion supplied by that argument. See
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma selected_notMem_residual_span_of_linearIndependent_option
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {κ : Type*} (u : κ → E) (v₀ : E)
    (hLI : LinearIndependent ℂ
      (fun o : Option κ =>
        match o with
        | none => v₀
        | some k => u k)) :
    v₀ ∉ Submodule.span ℂ (Set.range u) := by
  classical
  have hnone_not_mem : (none : Option κ) ∉ Set.range some := by
    rintro ⟨k, hk⟩
    cases hk
  have himage :
      ((fun o : Option κ =>
          match o with
          | none => v₀
          | some k => u k) '' Set.range some) = Set.range u := by
    ext x
    constructor
    · rintro ⟨o, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨some k, ⟨k, rfl⟩, rfl⟩
  simpa [himage] using hLI.notMem_span_image (s := Set.range some) (x := none) hnone_not_mem

/-- **Eventual residual-span exclusion from eventual selected-plus-residual
linear independence.**

This is the eventual form of
`selected_notMem_residual_span_of_linearIndependent_option`, suited to the
CPSV16 line-1182 peeling argument where the block-separation statement is used
only for sufficiently large chain lengths.

**Scope restriction (derived separation input):** The eventual
linear-independence hypothesis is an intermediate condition that must be
derived from the BNT separation argument before this lemma can be used in a
source-faithful proof; see
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma eventually_selected_notMem_residual_span_of_linearIndependent_option
    {κ : Type*}
    {E : ℕ → Type*} [∀ N, AddCommGroup (E N)] [∀ N, Module ℂ (E N)]
    (u : (N : ℕ) → κ → E N) (v₀ : (N : ℕ) → E N)
    (hLI : ∀ᶠ N in atTop, LinearIndependent ℂ
      (fun o : Option κ =>
        match o with
        | none => v₀ N
        | some k => u N k)) :
    ∀ᶠ N in atTop, v₀ N ∉ Submodule.span ℂ (Set.range (u N)) := by
  filter_upwards [hLI] with N hLIN
  exact selected_notMem_residual_span_of_linearIndependent_option (u N) (v₀ N) hLIN

/-- **Selected coefficient extraction modulo a residual span.**

This is a pure linear-algebra form of the coefficient-isolation step. If two
expressions differ only by terms in the span of a residual family, and the
selected vector is not in that residual span, then the selected coefficients
agree.

Source context: arXiv:1606.00608, Theorem II.1, line 1182. In the paper,
CPSV16, Lem1 is used to separate a fixed BNT block from the remaining
contributions. After the selected vector has been separated from the residual
span, equality modulo that residual span forces equality of the selected
coefficients.

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
    exact ((Submodule.span ℂ (Set.range u)).smul_mem_iff hdiff_ne).mp hdiff_mem
  exact hnot hv₀_mem

/-- **Eventual selected coefficient extraction modulo residual spans.**

This is the eventual form of
`selected_coefficient_eq_of_residual_span`, suited to the CPSV16 line-1182
peeling argument where CPSV16, Lem1 supplies statements only for sufficiently
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
