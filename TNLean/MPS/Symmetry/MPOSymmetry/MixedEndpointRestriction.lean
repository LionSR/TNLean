/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointIntersection
import TNLean.MPS.ParentHamiltonian.CyclicWindow

/-!
# Contiguous restrictions of the extended endpoint supports

A family of coefficient spaces closed under fixing the first or last
physical letter is closed under every positive-length contiguous restriction.
For the extended supports, the one-site recursions give this closure without
injectivity of the tensor or any hypothesis on the inserted matrix.

Source: arXiv:2203.12563, Section 5, lines 1687–1692.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Closure under fixing either endpoint implies closure under every
positive-length contiguous restriction. The proof enlarges the chosen
window one site at a time and then fixes the added site to its exterior
configuration value. -/
theorem contiguousRestrictₗ_mem_of_restriction_closed
    (S : (N : ℕ) → Submodule ℂ (NSiteSpace d N))
    (hLast : ∀ {M : ℕ}, 0 < M → ∀ {φ : NSiteSpace d (M + 1)},
      φ ∈ S (M + 1) → ∀ j : Fin d, restrictLast φ j ∈ S M)
    (hFirst : ∀ {M : ℕ}, 0 < M → ∀ {φ : NSiteSpace d (M + 1)},
      φ ∈ S (M + 1) → ∀ i : Fin d, restrictFirst φ i ∈ S M)
    {N L : ℕ} (hL : 0 < L) (s : ℕ) (hs : s + L ≤ N)
    (τ : Cfg d N) {ψ : NSiteSpace d N} (hψ : ψ ∈ S N) :
    contiguousRestrictₗ s L hs τ ψ ∈ S L := by
  suffices h : ∀ k M, N - M = k → 0 < M → ∀ t (ht : t + M ≤ N),
      contiguousRestrictₗ t M ht τ ψ ∈ S M by
    exact h (N - L) L rfl hL s hs
  intro k
  induction k with
  | zero =>
      intro M hgap _ t ht
      have hMN : M = N := by omega
      subst M
      have ht0 : t = 0 := by omega
      subst t
      have hfull : contiguousRestrictₗ 0 N ht τ ψ = ψ := by
        ext σ
        simp only [contiguousRestrictₗ_apply, contiguousCfg_zero_full]
      rw [hfull]
      exact hψ
  | succ k ih =>
      intro M hgap hM t ht
      have hgap' : N - (M + 1) = k := by omega
      have hMN : M + 1 ≤ N := by omega
      cases t with
      | zero =>
          have hlong := ih (M + 1) hgap' (by omega) 0 (by omega)
          have hshort := hLast hM hlong (τ ⟨M, by omega⟩)
          simpa only [contiguousRestrictₗ_restrictLast, Nat.zero_add,
            Function.update_eq_self] using hshort
      | succ t =>
          have hlong := ih (M + 1) hgap' (by omega) t (by omega)
          have hshort := hFirst hM hlong (τ ⟨t, by omega⟩)
          simpa only [contiguousRestrictₗ_restrictFirst,
            Function.update_eq_self] using hshort

namespace MPOSymmetry

/-- Fixing the last physical letter preserves the positive-length
extended support, without an injectivity hypothesis.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem restrictLast_insertedGroundSpace_mem
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {L : ℕ} (hL : 0 < L) {ψ : NSiteSpace d (L + 1)}
    (hψ : ψ ∈ insertedGroundSpace A W (L + 1)) (j : Fin d) :
    restrictLast ψ j ∈ insertedGroundSpace A W L := by
  obtain ⟨X, rfl⟩ := hψ
  rw [insertedGroundSpaceMap_restrictLast A W hL]
  exact ⟨_, rfl⟩

/-- Fixing the first physical letter preserves the positive-length
extended support, without an injectivity hypothesis.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem restrictFirst_insertedGroundSpace_mem
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {L : ℕ} (hL : 0 < L) {ψ : NSiteSpace d (L + 1)}
    (hψ : ψ ∈ insertedGroundSpace A W (L + 1)) (i : Fin d) :
    restrictFirst ψ i ∈ insertedGroundSpace A W L := by
  obtain ⟨X, rfl⟩ := hψ
  rw [insertedGroundSpaceMap_restrictFirst A W hL]
  exact ⟨_, rfl⟩

/-- Every positive-length contiguous restriction of an extended boundary
vector is an extended boundary vector. No injectivity or nonvanishing
condition is needed for this inclusion.
Source: arXiv:2203.12563, Section 5, lines 1687–1692. -/
theorem contiguousRestrictₗ_insertedGroundSpace_mem
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {N L : ℕ} (hL : 0 < L) (s : ℕ) (hs : s + L ≤ N)
    (τ : Cfg d N) {ψ : NSiteSpace d N}
    (hψ : ψ ∈ insertedGroundSpace A W N) :
    contiguousRestrictₗ s L hs τ ψ ∈ insertedGroundSpace A W L :=
  contiguousRestrictₗ_mem_of_restriction_closed (insertedGroundSpace A W)
    (fun {_M} hM {_φ} hφ j => restrictLast_insertedGroundSpace_mem A W hM hφ j)
    (fun {_M} hM {_φ} hφ i => restrictFirst_insertedGroundSpace_mem A W hM hφ i)
    hL s hs τ hψ

end MPOSymmetry
end MPSTensor
