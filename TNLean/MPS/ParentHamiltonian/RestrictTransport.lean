/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.SuffixWindow
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Arithmetic transport for open-chain restriction maps

Reindexing the `N`-site state space along an equality of total lengths, and the
resulting transport of the parent-Hamiltonian open-chain restriction maps
(`contiguousRestrictₗ`, `tailRestrictₗ`) across
arithmetic-equal indexings of the total length. These transport identities serve
the periodic-chain normal-form range-reduction argument
(see [Cirac--Perez-Garcia--Schuch--Verstraete 2021, arXiv:2011.12127,
Section IV.C, lines 2049--2094]), where intermediate induction steps naturally produce
states indexed by \(K + 1 + L₀\) that have to be viewed as states indexed by
\(K + (L₀ + 1)\), or states indexed by \(N - (L₀ + 1) + (L₀ + 1)\) that have to be
viewed as states indexed by \(N\).

Because `NSiteSpace d N = (Fin N → Fin d) → ℂ` depends definitionally on \(N\),
two states whose length-witnesses are propositionally but not definitionally
equal cannot be compared directly. The canonical solution is to reindex via
`Fin.cast`, which this file represents as a `LinearEquiv`.

## Main contents

* `MPSTensor.reindexSites` — the linear equivalence
  `NSiteSpace d M ≃ₗ[ℂ] NSiteSpace d N` induced by a proof \(h : M = N\).
* `MPSTensor.reindexSites_groundSpaceMap` — compatibility of the ground-space
  map with reindexing, so ground-space membership transports through \(h\).
* `MPSTensor.contiguousRestrictₗ_reindex_window` — transport
  `contiguousRestrictₗ` under an equality of window lengths.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 2049--2094
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Reindexing `NSiteSpace` along an equality of lengths -/

/-- The linear equivalence between `NSiteSpace d M` and `NSiteSpace d N`
induced by a proof \(h : M = N\), reindexing configurations via `Fin.cast`. -/
def reindexSites {d : ℕ} {M N : ℕ} (h : M = N) :
    NSiteSpace d M ≃ₗ[ℂ] NSiteSpace d N :=
  LinearEquiv.funCongrLeft ℂ ℂ
    (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl (Fin d)))

@[simp] theorem reindexSites_apply {M N : ℕ} (h : M = N)
    (ψ : NSiteSpace d M) (σ : Fin N → Fin d) :
    reindexSites h ψ σ = ψ (σ ∘ Fin.cast h) := rfl

/-! ### Interaction with `groundSpaceMap` -/

/-- Reindexing a ground-space image produces the ground-space image at the new
length with the same boundary matrix. -/
@[simp] theorem reindexSites_groundSpaceMap (A : MPSTensor d D) {M N : ℕ}
    (h : M = N) (X : Matrix (Fin D) (Fin D) ℂ) :
    reindexSites h (groundSpaceMap A M X) = groundSpaceMap A N X := by
  subst h; rfl

/-- Ground-space membership transports along an equality of total lengths. -/
theorem reindexSites_mem_groundSpace {A : MPSTensor d D} {M N : ℕ} (h : M = N)
    {ψ : NSiteSpace d M} (hψ : ψ ∈ groundSpace A M) :
    reindexSites h ψ ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range] at hψ ⊢
  obtain ⟨X, rfl⟩ := hψ
  exact ⟨X, (reindexSites_groundSpaceMap A h X).symm⟩

/-! ### Transport for `contiguousRestrictₗ` -/

/-- Transport `contiguousRestrictₗ` across an equality of window lengths
\(M = M'\). -/
theorem contiguousRestrictₗ_reindex_window
    {N : ℕ} {s M M' : ℕ} (hM : M = M') (hsM : s + M ≤ N) (hsM' : s + M' ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    reindexSites hM (contiguousRestrictₗ s M hsM τ ψ) =
      contiguousRestrictₗ s M' hsM' τ ψ := by
  subst hM; rfl

/-- Fixing the first \(K\) sites of a contiguous \((K + L)\)-window leaves the
contiguous \(L\)-window that starts at \(s + K\), with the fixed prefix inserted into
the outside configuration. -/
theorem tailRestrictₗ_contiguousRestrictₗ
    {N s K L : ℕ} (hsKL : s + (K + L) ≤ N)
    (u : Fin K → Fin d) (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    tailRestrictₗ u (contiguousRestrictₗ s (K + L) hsKL τ ψ) =
      contiguousRestrictₗ (s + K) L (by omega)
        (fun k => if h : s ≤ k.val ∧ k.val < s + K
          then u ⟨k.val - s, by omega⟩ else τ k) ψ := by
  ext σ
  simp only [tailRestrictₗ_apply, contiguousRestrictₗ_apply]
  congr 1
  ext ⟨k, hk⟩
  simp only [contiguousCfg]
  by_cases hLeft : s ≤ k ∧ k < s + K
  · rw [dite_eq_left (show s ≤ k ∧ k < s + (K + L) by omega)]
    rw [dite_eq_right (show ¬(s + K ≤ k ∧ k < s + K + L) by omega)]
    rw [dite_eq_left hLeft]
    have hidx : (⟨k - s, by omega⟩ : Fin (K + L)) =
        Fin.castAdd L (⟨k - s, by omega⟩ : Fin K) := by
      ext
      simp [Fin.castAdd]
    rw [hidx, Fin.append_left]
  · by_cases hRight : s + K ≤ k ∧ k < s + K + L
    · rw [dite_eq_left (show s ≤ k ∧ k < s + (K + L) by omega)]
      rw [dite_eq_left hRight]
      have hidx : (⟨k - s, by omega⟩ : Fin (K + L)) =
          Fin.natAdd K (⟨k - (s + K), by omega⟩ : Fin L) := by
        ext
        simp [Fin.natAdd]
        omega
      rw [hidx, Fin.append_right]
    · rw [dite_eq_right (show ¬(s ≤ k ∧ k < s + (K + L)) by omega)]
      rw [dite_eq_right hRight]
      rw [dite_eq_right hLeft]

end MPSTensor
