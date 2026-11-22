/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import QICLean.Spectral.Gap.WeightedPositiveKernel

/-!
# The local sections of a periodic interaction kernel

A translated interaction acts on each fixed-outside coefficient section by the
original local operator. For a positive interaction, a periodic Hamiltonian
kernel equation therefore supplies every local section equation.

Source: the local-kernel step in SPWC10, arXiv:0909.5347, Theorem 5 proof,
lines 869--880 of `Papers/0909.5347/main.tex`.

The facts are stated for the terms and the Hamiltonian of the translation-invariant
interaction of a local matrix (`ManyBody.Interaction.translationInvariant`).
-/

namespace MPSTensor

variable {d R N : ℕ}

/-! ### Translates of a local matrix on the ring

The terms and the Hamiltonian of the translation-invariant interaction of a local matrix `h`
on the ring (`ManyBody.Interaction.translationInvariant`), for \(R \le N\); statements about vectors
take the operators `Matrix.toEuclideanLin`. -/

section TranslationInvariant

open scoped ComplexOrder MatrixOrder
open ManyBody.Interaction (translationInvariant)

/-- Restricting a term of the translates of `h` to its own window gives `h` applied to that same
section. Source: SPWC10, Theorem 5 proof, lines 869--880. -/
theorem cyclicRestrictES_toEuclideanLin_translationInvariant_term (hRN : R ≤ N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N) (τ : Cfg d N) (ψ : MPVSpace d N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    cyclicRestrictES (Fin.pos i) R i τ
        (Matrix.toEuclideanLin ((translationInvariant N h).term i) ψ) =
      Matrix.toEuclideanLin h (cyclicRestrictES (Fin.pos i) R i τ ψ) := by
  have : NeZero N := NeZero.of_pos i.pos
  ext ω
  change Matrix.toEuclideanLin ((translationInvariant N h).term i) ψ
    (cyclicCfg (Fin.pos i) R i ω τ) = _
  rw [toEuclideanLin_translationInvariant_term_apply hRN]
  have hrestrict : cyclicRestrictES (Fin.pos i) R i
      (cyclicCfg (Fin.pos i) R i ω τ) ψ = cyclicRestrictES (Fin.pos i) R i τ ψ := by
    ext ν
    exact congrFun (cyclicRestrictₗ_cyclicCfg_outside (Fin.pos i) i ω τ ψ.ofLp) ν
  have hextract : extractWindow R i (cyclicCfg (Fin.pos i) R i ω τ) = ω :=
    extractWindow_replaceWindow R hRN i τ ω
  rw [hrestrict, hextract]

/-- A term of the translates of `h` annihilates a vector precisely when `h` kills every actual
coefficient section on its window. Source: SPWC10, Theorem 5 proof, lines 869--880. -/
theorem toEuclideanLin_translationInvariant_term_eq_zero_iff_sections (hRN : R ≤ N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N) (ψ : MPVSpace d N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N h).term i) ψ = 0 ↔
      ∀ τ : Cfg d N, Matrix.toEuclideanLin h (cyclicRestrictES (Fin.pos i) R i τ ψ) = 0 := by
  have : NeZero N := NeZero.of_pos i.pos
  constructor
  · intro hzero τ
    rw [← cyclicRestrictES_toEuclideanLin_translationInvariant_term hRN h i τ ψ, hzero, map_zero]
  · intro hzero
    ext σ
    rw [toEuclideanLin_translationInvariant_term_apply hRN]
    exact congrArg (fun v : MPVSpace d R ↦ v (extractWindow R i σ)) (hzero σ)

/-- For a positive semidefinite `h`, the kernel equation of the Hamiltonian of the translates of
`h` on the ring is equivalent to every local section equation. Source: SPWC10, Theorem 5 proof,
lines 869--880. -/
theorem toEuclideanLin_hamiltonian_translationInvariant_eq_zero_iff_sections [NeZero N]
    (hRN : R ≤ N) (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (ψ : MPVSpace d N) :
    Matrix.toEuclideanLin (translationInvariant N h).hamiltonian ψ = 0 ↔
      ∀ (i : Fin N) (τ : Cfg d N),
        Matrix.toEuclideanLin h (cyclicRestrictES (Fin.pos i) R i τ ψ) = 0 := by
  have hterm (i : Fin N) :
      (Matrix.toEuclideanLin ((translationInvariant N h).term i)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.nonneg_iff_posSemidef.mp
      (ManyBody.Interaction.translationInvariant_term_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hh) i))
  rw [ManyBody.Interaction.hamiltonian, map_sum, WeightedPositiveKernel.apply_sum_eq_zero_iff
    hterm ψ]
  exact forall_congr' fun i ↦
    toEuclideanLin_translationInvariant_term_eq_zero_iff_sections hRN h i ψ

/-- If a term of the translates of `h` on the ring annihilates a vector, then on every spectator
section of an active interval containing its window, the corresponding term of the translates
of `h` on that interval annihilates the section. The interaction range stays fixed. Source:
finite-range identity extension in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem toEuclideanLin_translationInvariant_term_rightFiber_eq_zero_of_eq_zero
    {W : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hWN : W ≤ N) (s : Fin N) (q : Fin W)
    (hqR : q.val + R ≤ W) (ψ : MPVSpace d N)
    (hzero : haveI : NeZero N := ⟨by omega⟩; Matrix.toEuclideanLin ((translationInvariant N h).term
      (cyclicForwardSite s q.val)) ψ = 0)
    (τ : Cfg d (N - W)) :
    haveI : NeZero W := ⟨by omega⟩;
    Matrix.toEuclideanLin ((translationInvariant W h).term q)
      (ContinuousLinearMap.rightFiber
        (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s ψ) τ) = 0 := by
  have : NeZero W := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  rw [toEuclideanLin_translationInvariant_term_eq_zero_iff_sections (by omega : R ≤ N)] at hzero
  rw [toEuclideanLin_translationInvariant_term_eq_zero_iff_sections (by omega : R ≤ W)]
  intro σ
  convert hzero ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) using 2
  ext ω
  change cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s ψ (cyclicCfg (Fin.pos q) R q ω σ, τ) =
    ψ (cyclicCfg (Fin.pos (cyclicForwardSite s q.val)) R (cyclicForwardSite s q.val) ω
      ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)))
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply,
    cyclicCfg_join_cyclicActiveBlock hWN s q hqR]

end TranslationInvariant

end MPSTensor
