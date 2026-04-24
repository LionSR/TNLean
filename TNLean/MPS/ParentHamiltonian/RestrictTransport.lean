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

This file provides a small reusable API for transporting the parent-Hamiltonian
open-chain restriction maps (`contiguousRestrictₗ`, `tailRestrictₗ`,
`restrictFirst`) across arithmetic-equal indexings of the total length. It is
aimed at the periodic-chain normal-form range-reduction argument
(see [CPGSV21, §IV.C]), where intermediate induction steps naturally produce
states indexed by `K + 1 + L₀` that have to be viewed as states indexed by
`K + (L₀ + 1)`, or states indexed by `N - (L₀ + 1) + (L₀ + 1)` that have to be
viewed as states indexed by `N`.

Because `NSiteSpace d N = (Fin N → Fin d) → ℂ` depends definitionally on `N`,
two states whose length-witnesses are propositionally but not definitionally
equal cannot be compared directly. The canonical solution is to reindex via
`Fin.cast`, which this file packages as a `LinearEquiv`.

## Main contents

* `MPSTensor.reindexSites` — the linear equivalence
  `NSiteSpace d M ≃ₗ[ℂ] NSiteSpace d N` induced by a proof `h : M = N`.
* `MPSTensor.reindexSites_groundSpaceMap` — reindexing commutes with
  `groundSpaceMap`, so ground-space membership transports through `h`.
* `MPSTensor.tailRestrictₗ_snoc` — pushing the last entry of a `(K+1)`-prefix
  into the first suffix position, bridging `K + 1 + L` and `K + (L + 1)`.
* `MPSTensor.tailRestrictₗ_reindex_prefix` /
  `MPSTensor.tailRestrictₗ_reindex_tail` — transport `tailRestrictₗ` under
  equalities of the prefix or tail length.
* `MPSTensor.contiguousRestrictₗ_reindex_window` /
  `MPSTensor.contiguousRestrictₗ_reindex_total` — transport
  `contiguousRestrictₗ` under equalities of the window or total length.
* `MPSTensor.tailRestrictₗ_reindex_of_le` — tail restriction of a state on `N`
  sites through the identification `N = (N - L) + L`.

## References

* [CPGSV21] arXiv:2011.12127, §IV.C
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Reindexing `NSiteSpace` along an equality of lengths -/

/-- The linear equivalence between `NSiteSpace d M` and `NSiteSpace d N`
induced by a proof `h : M = N`, reindexing configurations via `Fin.cast`. -/
def reindexSites {d : ℕ} {M N : ℕ} (h : M = N) :
    NSiteSpace d M ≃ₗ[ℂ] NSiteSpace d N where
  toFun ψ σ := ψ (σ ∘ Fin.cast h)
  invFun ψ σ := ψ (σ ∘ Fin.cast h.symm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ψ := by subst h; rfl
  right_inv ψ := by subst h; rfl

@[simp] theorem reindexSites_apply {M N : ℕ} (h : M = N)
    (ψ : NSiteSpace d M) (σ : Fin N → Fin d) :
    reindexSites h ψ σ = ψ (σ ∘ Fin.cast h) := rfl

@[simp] theorem reindexSites_symm_apply {M N : ℕ} (h : M = N)
    (ψ : NSiteSpace d N) (σ : Fin M → Fin d) :
    (reindexSites (d := d) h).symm ψ σ = ψ (σ ∘ Fin.cast h.symm) := rfl

@[simp] theorem reindexSites_rfl (M : ℕ) (ψ : NSiteSpace d M) :
    reindexSites (rfl : M = M) ψ = ψ := rfl

/-- Composition of two `reindexSites` equivalences is a single `reindexSites`
along the transitive equality. -/
theorem reindexSites_trans {L M N : ℕ} (h₁ : L = M) (h₂ : M = N)
    (ψ : NSiteSpace d L) :
    reindexSites h₂ (reindexSites h₁ ψ) = reindexSites (h₁.trans h₂) ψ := by
  subst h₁; rfl

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

/-! ### Transport for `tailRestrictₗ` -/

/-- Pushing the final entry of a `(K+1)`-prefix into the first suffix position.
For `ψ : NSiteSpace d (K + 1 + L)`, the `(K+1)`-prefix `Fin.snoc u j` yields the
same tail state as `restrictFirst` at `j` of the `K`-prefix `u` applied to the
reindexed state in `NSiteSpace d (K + (L + 1))`.

This is the key compatibility bridging `K + 1 + L₀` and `K + (L₀ + 1)` that
arises in the periodic normal-form range-reduction induction. -/
theorem tailRestrictₗ_snoc {K L : ℕ} (u : Fin K → Fin d) (j : Fin d)
    (ψ : NSiteSpace d (K + 1 + L)) :
    tailRestrictₗ (Fin.snoc u j) ψ =
      restrictFirst
        (tailRestrictₗ u
          (reindexSites (show K + 1 + L = K + (L + 1) by
            rw [Nat.add_assoc, Nat.add_comm 1 L]) ψ)) j := by
  ext σ
  simp only [tailRestrictₗ_apply, restrictFirst_apply, reindexSites_apply]
  rw [Fin.append_right_cons]
  rfl

/-- Transport `tailRestrictₗ` across an equality of prefix lengths `K = K'`:
fixing the prefix `u : Fin K → Fin d` on a state in `NSiteSpace d (K + L)` is
equivalent to fixing the pulled-back prefix on the reindexed state in
`NSiteSpace d (K' + L)`. -/
theorem tailRestrictₗ_reindex_prefix {K K' L : ℕ} (hK : K = K')
    (u : Fin K → Fin d) (ψ : NSiteSpace d (K + L)) :
    tailRestrictₗ u ψ =
      tailRestrictₗ (u ∘ Fin.cast hK.symm)
        (reindexSites (congrArg (· + L) hK) ψ) := by
  subst hK; rfl

/-- Transport `tailRestrictₗ` across an equality of tail lengths `L = L'`:
reindexing the target commutes with reindexing the source. -/
theorem tailRestrictₗ_reindex_tail {K L L' : ℕ} (hL : L = L')
    (u : Fin K → Fin d) (ψ : NSiteSpace d (K + L)) :
    reindexSites hL (tailRestrictₗ u ψ) =
      tailRestrictₗ u
        (reindexSites (congrArg (K + ·) hL) ψ) := by
  subst hL; rfl

/-- Tail restriction of a state on `N` sites through the identification
`N = (N - L) + L`, which holds when `L ≤ N`. Useful when the periodic induction
splits a full chain at a boundary position and views what remains as a suffix
window. -/
theorem tailRestrictₗ_reindex_of_le {N L : ℕ} (hLN : L ≤ N)
    (u : Fin (N - L) → Fin d) (ψ : NSiteSpace d N) (σ : Fin L → Fin d) :
    tailRestrictₗ u
        (reindexSites (show N = (N - L) + L from
          (Nat.sub_add_cancel hLN).symm) ψ) σ =
      ψ (Fin.append u σ ∘ Fin.cast
        (show N = (N - L) + L from (Nat.sub_add_cancel hLN).symm)) := by
  rfl

/-! ### Transport for `contiguousRestrictₗ` -/

/-- Transport `contiguousRestrictₗ` across an equality of window lengths
`M = M'`. -/
theorem contiguousRestrictₗ_reindex_window
    {N : ℕ} {s M M' : ℕ} (hM : M = M') (hsM : s + M ≤ N) (hsM' : s + M' ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    reindexSites hM (contiguousRestrictₗ s M hsM τ ψ) =
      contiguousRestrictₗ s M' hsM' τ ψ := by
  subst hM; rfl

/-- Transport `contiguousRestrictₗ` across an equality of total lengths
`N = N'`: the state, the outside configuration, and both bounding proofs all
travel along `Fin.cast`. -/
theorem contiguousRestrictₗ_reindex_total
    {N N' : ℕ} {s M : ℕ} (hN : N = N') (hsM : s + M ≤ N) (hsM' : s + M ≤ N')
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    contiguousRestrictₗ s M hsM τ ψ =
      contiguousRestrictₗ s M hsM' (τ ∘ Fin.cast hN.symm)
        (reindexSites hN ψ) := by
  subst hN; rfl

end MPSTensor
