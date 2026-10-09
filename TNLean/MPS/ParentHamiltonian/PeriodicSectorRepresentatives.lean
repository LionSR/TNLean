/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.Dichotomy
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients
import TNLean.MPS.ParentHamiltonian.PrimitiveSectorRepresentatives

/-!
# Periodic representatives preserving open-boundary support

A finite periodic family can be reduced to a literal subfamily of pairwise
inequivalent sectors without changing its joint open-boundary spaces. The
MPV phase classes are used only to recover gauge transformations. The exact
support identities then follow from gauge invariance of open-boundary spaces,
not merely from equality of periodic vectors.

The proportionality in the phase relation is an explicit hypothesis of the
first two lemmas. It is supplied internally by the existing phase-class
construction in the representative theorem. No pairwise inequivalence,
primitivity, invariant density matrix, or nonempty-family assumption is added.

Sources: arXiv:1708.00029, Proposition equal-or-orthogonal-generalized;
Nachtergaele, arXiv:cond-mat/9410110, Section 4 and Lemma disjoint.
This module gives algebraic support equalities, independently of the remaining
joint intersection and infinite-volume classification arguments.
-/

open Filter
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d DA DB m n : ℕ}

/-- Periodic tensors whose periodic vectors differ by a fixed nonzero scalar
power have equal bond dimensions and are gauge-phase equivalent.
Proportionality is part of the explicit phase-relation hypothesis.
Source: arXiv:1708.00029, Proposition equal-or-orthogonal-generalized;
Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint. -/
theorem MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isPeriodic
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (h : MPVBlockPhaseEquiv A B) :
    ∃ e : DA = DB, GaugePhaseEquiv (e ▸ A) B := by
  let : NeZero DA := ⟨hA.bondDim_ne_zero⟩
  let : NeZero DB := ⟨hB.bondDim_ne_zero⟩
  rcases periodicOverlapDichotomy A B hA hB with hDecay | ⟨e, hRep⟩
  · classical
    obtain ⟨ζ, _, hmpv⟩ := h
    have hma := hA.period_pos
    have hmb := hB.period_pos
    have hg : Tendsto (fun k : ℕ => n * (k + 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) tendsto_id
      calc k ≤ k + 1 := Nat.le_succ k
        _ ≤ n * (k + 1) := Nat.le_mul_of_pos_left _ hmb
    have hg' : Tendsto (fun k : ℕ => m * (k + 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) tendsto_id
      calc k ≤ k + 1 := Nat.le_succ k
        _ ≤ m * (k + 1) := Nat.le_mul_of_pos_left _ hma
    have hf : Tendsto (fun k : ℕ => m * (n * (k + 1))) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) hg
      exact Nat.le_mul_of_pos_left _ hma
    have hAA : Tendsto (fun k : ℕ => mpvOverlap A A (m * (n * (k + 1)))) atTop
        (nhds (m : ℂ)) := (periodicSelfOverlap_tendsto A hA).comp hg
    have hBB : Tendsto (fun k : ℕ => mpvOverlap B B (m * (n * (k + 1)))) atTop
        (nhds (n : ℂ)) := by
      refine ((periodicSelfOverlap_tendsto B hB).comp hg').congr fun k => ?_
      simp only [Function.comp]
      rw [show n * (m * (k + 1)) = m * (n * (k + 1)) by ring]
    have hAB : Tendsto (fun k : ℕ => mpvOverlap A B (m * (n * (k + 1)))) atTop (nhds 0) :=
      hDecay.comp hf
    have hkey : ∀ N : ℕ, 0 < N →
        mpvOverlap B B N * mpvOverlap A A N = mpvOverlap A B N * star (mpvOverlap A B N) := by
      intro N hN
      rw [mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos hmpv N hN,
        mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_pos hmpv N hN,
        star_mul', star_pow, star_star, mpvOverlap_star_swap, mul_pow]
      simp only [← Complex.star_def]
      ring
    have h1 : Tendsto (fun k : ℕ => mpvOverlap A B (m * (n * (k + 1))) *
        star (mpvOverlap A B (m * (n * (k + 1))))) atTop (nhds ((n : ℂ) * (m : ℂ))) :=
      (hBB.mul hAA).congr fun k =>
        hkey _ (Nat.mul_pos hma (Nat.mul_pos hmb (Nat.succ_pos k)))
    have h2 := hAB.mul hAB.star
    have := tendsto_nhds_unique h1 h2
    simp at this
    omega
  · refine ⟨e, ?_⟩
    cases e
    simpa only [cast_eq] using gaugePhaseEquiv_symm (gaugePhaseEquiv_of_repeatedBlocks hRep)

/-- Phase-related periodic tensors have identical open-boundary spaces at
all lengths. The gauge is recovered before passing to open boundaries.
Source: arXiv:1708.00029, Proposition equal-or-orthogonal-generalized;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem MPVBlockPhaseEquiv.groundSpaceES_eq_of_isPeriodic
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (h : MPVBlockPhaseEquiv A B) (N : ℕ) : groundSpaceES A N = groundSpaceES B N := by
  obtain ⟨e, he⟩ := h.dim_eq_and_gaugePhaseEquiv_of_isPeriodic hA hB
  cases e
  exact he.groundSpaceES_eq N

variable {b : ℕ} {dim : Fin b → ℕ} {per : Fin b → ℕ}

/-- Selecting MPV phase-class representatives of a periodic family preserves
its joint open-boundary space at every length. Nonzero weights do not change
that space. Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma
commutation (ii) and Section 4; arXiv:1708.00029, Proposition
equal-or-orthogonal-generalized. -/
theorem MPVPhaseClassData.groundSpaceES_toTensorFromBlocks_eq_representatives_of_isPeriodic
    (A : ∀ j, MPSTensor d (dim j)) (classes : MPVPhaseClassData A)
    (hA : ∀ j, IsPeriodic (per j) (A j))
    (μ : Fin b → ℂ) (hμ : ∀ j, μ j ≠ 0) (N : ℕ) :
    groundSpaceES (toTensorFromBlocks μ A) N =
      groundSpaceES (toTensorFromBlocks (fun _ => 1) (fun k => A (classes.repr k))) N := by
  let : ∀ j, NeZero (dim j) := fun j => ⟨(hA j).bondDim_ne_zero⟩
  rw [groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ,
    groundSpaceES_toTensorFromBlocks_eq_iSup (fun _ => 1)
      (fun k => A (classes.repr k)) (fun _ => one_ne_zero)]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    obtain ⟨k, q, rfl⟩ := classes.exists_enum_eq j
    rw [← (classes.enum_phase k q).groundSpaceES_eq_of_isPeriodic
      (hA (classes.repr k)) (hA (classes.enum k q)) N]
    exact le_iSup (fun j => groundSpaceES (A (classes.repr j)) N) k
  · exact iSup_le fun k => le_iSup (fun j => groundSpaceES (A j) N) (classes.repr k)

/-- Every finite periodic family admits a literal subfamily of pairwise
inequivalent periodic representatives, with a gauge cover of the original
family and exact joint open-boundary support at every length. The family
may be empty. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4 and
Lemma disjoint; arXiv:1708.00029, Proposition
equal-or-orthogonal-generalized. -/
theorem exists_periodic_sector_representatives
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (hA : ∀ j, IsPeriodic (per j) (A j)) :
    ∃ (g : ℕ) (sel : Fin g → Fin b), Function.Injective sel ∧
      (∀ k, 0 < dim (sel k)) ∧
      (∀ k, IsPeriodic (per (sel k)) (A (sel k))) ∧
      BlocksNotGaugePhaseEquiv (fun k => A (sel k)) ∧
      (∀ j, ∃ k, ∃ e : dim (sel k) = dim j,
        GaugePhaseEquiv (e ▸ A (sel k)) (A j)) ∧
      ∀ N, groundSpaceES (toTensorFromBlocks μ A) N =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) (fun k => A (sel k))) N := by
  let classes := mpvPhaseClassData A
  have hinj : Function.Injective classes.repr := by
    intro i j hij
    by_contra hne
    have e : dim (classes.repr i) = dim (classes.repr j) := congrArg dim hij
    apply classes.blocks_not_equiv i j hne e
    exact gaugePhaseEquiv_cast_idx A A hij.symm rfl
      (GaugeEquiv.refl (A (classes.repr j))).toGaugePhaseEquiv
  refine ⟨classes.g, classes.repr, hinj, (fun k => Nat.pos_of_ne_zero
    (hA (classes.repr k)).bondDim_ne_zero), (fun k => hA (classes.repr k)),
    classes.blocks_not_equiv, ?_,
    classes.groundSpaceES_toTensorFromBlocks_eq_representatives_of_isPeriodic A hA μ hμ⟩
  intro j
  obtain ⟨k, q, rfl⟩ := classes.exists_enum_eq j
  obtain ⟨e, he⟩ := (classes.enum_phase k q).dim_eq_and_gaugePhaseEquiv_of_isPeriodic
    (hA (classes.repr k)) (hA (classes.enum k q))
  exact ⟨k, e, he⟩

end MPSTensor

