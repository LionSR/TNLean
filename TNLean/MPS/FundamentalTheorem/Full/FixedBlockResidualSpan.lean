/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap

/-!
# Fixed-block residual-span exclusion

The direct residual-span consequence of the fixed-block Lem1
linear-independence input in CPSV16 Theorem II.1 is isolated here.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Corollary Lem1 and Theorem thm1, lines 1182--1185.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **Fixed-right residual-span exclusion from Lemma Lem1.**

Source: arXiv:1606.00608, Corollary Lem1 and Theorem thm1, line 1182.
If a fixed `B`-block has vanishing overlap with every `A`-block, then
Corollary Lem1 gives eventual linear independence of the family consisting
of all `A`-blocks and this fixed `B`-block. Therefore, for all sufficiently
large lengths, the fixed `B` MPV state is not in the span of the `A` MPV
states.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma eventually_fixed_right_notMem_left_span_of_all_overlaps_decay_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (k₀ : Fin rB)
    (hAllDecay : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₀) N) atTop (nhds 0)) :
    ∀ᶠ N in atTop,
      mpvState (d := d) (B k₀) N ∉
        Submodule.span ℂ (Set.range fun j : Fin rA => mpvState (d := d) (A j) N) := by
  classical
  have hLI :=
    eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT
      A B hA hB k₀ hAllDecay
  refine hLI.mono ?_
  intro N hLIN
  have hnot_range :
      (Sum.inr (0 : Fin 1) : Sum (Fin rA) (Fin 1)) ∉
        Set.range (fun j : Fin rA => Sum.inl (β := Fin 1) j) := by
    rintro ⟨j, hj⟩
    cases hj
  have himage :
      ((Sum.elim
          (fun j : Fin rA => mpvState (d := d) (A j) N)
          (fun _ : Fin 1 => mpvState (d := d) (B k₀) N)) ''
        Set.range (fun j : Fin rA => Sum.inl (β := Fin 1) j)) =
          Set.range (fun j : Fin rA => mpvState (d := d) (A j) N) := by
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Sum.inl j, ⟨j, rfl⟩, rfl⟩
  simpa [himage] using
    hLIN.notMem_span_image
      (s := Set.range (fun j : Fin rA => Sum.inl (β := Fin 1) j))
      (x := Sum.inr (0 : Fin 1)) hnot_range

/-- **Fixed-left residual-span exclusion from Lemma Lem1.**

Source: arXiv:1606.00608, Corollary Lem1 and Theorem thm1, lines
1182--1185. This is the symmetric form of
`eventually_fixed_right_notMem_left_span_of_all_overlaps_decay_CFBNT`: if a
fixed `A`-block has vanishing overlap with every `B`-block, then the fixed
`A` MPV state is eventually outside the span of the `B` MPV states.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma eventually_fixed_left_notMem_right_span_of_all_overlaps_decay_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (j₀ : Fin rA)
    (hAllDecay : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k) N) atTop (nhds 0)) :
    ∀ᶠ N in atTop,
      mpvState (d := d) (A j₀) N ∉
        Submodule.span ℂ (Set.range fun k : Fin rB => mpvState (d := d) (B k) N) := by
  classical
  have hLI :=
    eventually_linearIndependent_all_right_single_left_of_all_overlaps_decay_CFBNT
      A B hA hB j₀ hAllDecay
  refine hLI.mono ?_
  intro N hLIN
  have hnot_range :
      (Sum.inr (0 : Fin 1) : Sum (Fin rB) (Fin 1)) ∉
        Set.range (fun k : Fin rB => Sum.inl (β := Fin 1) k) := by
    rintro ⟨k, hk⟩
    cases hk
  have himage :
      ((Sum.elim
          (fun k : Fin rB => mpvState (d := d) (B k) N)
          (fun _ : Fin 1 => mpvState (d := d) (A j₀) N)) ''
        Set.range (fun k : Fin rB => Sum.inl (β := Fin 1) k)) =
          Set.range (fun k : Fin rB => mpvState (d := d) (B k) N) := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Sum.inl k, ⟨k, rfl⟩, rfl⟩
  simpa [himage] using
    hLIN.notMem_span_image
      (s := Set.range (fun k : Fin rB => Sum.inl (β := Fin 1) k))
      (x := Sum.inr (0 : Fin 1)) hnot_range

end HeteroEqualCase

end MPSTensor
