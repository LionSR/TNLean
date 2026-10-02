/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicPrimitiveGroundSpace
import TNLean.MPS.ParentHamiltonian.PrimitiveSectorRepresentatives

/-!
# Inequivalent primitive presentations of periodically blocked local spaces

Blocking a periodic tensor by a positive multiple of its period gives a
finite primitive family with faithful invariant matrices. Selecting one
representative of each gauge-phase class produces a nonempty, pairwise
inequivalent family with the same joint local MPS space at every chain
length, including zero. The representative tensors and invariant matrices
are inherited from the compressed sectors.

These are finite support identities. They require neither supplied sector
inequivalence nor positivity assumptions on ambient dimensions. The positive
sector dimensions are obtained from the periodic compression. Their role in
quasi-local state classification is separate from this finite presentation.

Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; CPSV16, arXiv:1606.00608, Proposition `prop:char-BNT`
and Theorem `thm1`; Nachtergaele, arXiv:cond-mat/9410110,
Section 3 and Lemma `disjoint`.

**Local fix (powered roots):** The period-removing compression uses the
corrected peripheral period documented in
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D m : ℕ}

/-- A periodic tensor, blocked by any positive multiple of its period,
admits a nonempty finite family of pairwise gauge-phase inequivalent primitive
sectors with faithful invariant matrices and the exact same joint support
at every length. No sector inequivalence assumption is supplied.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; CPSV16, arXiv:1606.00608, Proposition `prop:char-BNT`
and Theorem `thm1`; Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`. -/
theorem IsPeriodic.exists_inequivalent_primitive_groundStatePresentation_of_dvd
    {A : MPSTensor d D} (hA : IsPeriodic m A) (p : ℕ)
    (hp : 0 < p) (hdiv : m ∣ p) :
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ a, 0 < dim a),
        let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
        ∃ (B : (a : Fin g) → MPSTensor (blockPhysDim d p) (dim a))
          (ρ : (a : Fin g) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
          (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
          BlocksNotGaugePhaseEquiv B ∧
          (∀ N, groundSpaceES (blockTensor A p) N =
            groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) := by
  classical
  obtain ⟨dim, hdim, B, ρ, _htotal, hP, hρ, hGS⟩ :=
    hA.exists_isPrimitiveMPS_groundSpaceDecomposition_of_dvd p hp hdiv
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  obtain ⟨g, sel, _hsel, hpos, hP', hρ', hDistinct, hCover, hGS'⟩ :=
    exists_primitive_sector_representatives (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ
  have hr : 0 < m.gcd p := by
    rw [Nat.gcd_eq_left hdiv]
    exact hA.period_pos
  obtain ⟨k, _e, _he⟩ := hCover ⟨0, hr⟩
  exact ⟨g, Fin.pos k, (fun k => dim (sel k)), hpos,
    (fun k => B (sel k)), (fun k => ρ (sel k)), hP', hρ', hDistinct,
    fun N => (hGS N).trans (hGS' N)⟩

/-- Blocking a periodic tensor by its period gives a nonempty primitive
sector presentation with faithful invariant matrices, derived pairwise
inequivalence, and exact support at every chain length, including zero.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`;
CPSV16, arXiv:1606.00608, Proposition `prop:char-BNT` and Theorem `thm1`. -/
theorem IsPeriodic.exists_inequivalent_primitive_groundStatePresentation
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ a, 0 < dim a),
        let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
        ∃ (B : (a : Fin g) → MPSTensor (blockPhysDim d m) (dim a))
          (ρ : (a : Fin g) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
          (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
          BlocksNotGaugePhaseEquiv B ∧
          (∀ N, groundSpaceES (blockTensor A m) N =
            groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) := by
  exact hA.exists_inequivalent_primitive_groundStatePresentation_of_dvd
    m hA.period_pos (dvd_refl m)

end MPSTensor
