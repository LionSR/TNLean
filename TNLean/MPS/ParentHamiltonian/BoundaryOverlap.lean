/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.SuffixWindow

/-!
# Boundary overlaps for cyclic parent-Hamiltonian windows

This file records the elementary boundary-matrix identities obtained by deleting
one endpoint from a cyclic window.  The identities are used in the closing
boundary comparison for normal parent-Hamiltonian uniqueness.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If a non-repeating cyclic `(L + 1)`-window is represented by the boundary
matrix `Y`, then fixing its first site to `j` represents the shifted length-`L`
window by the boundary matrix `Y * A j`. -/
theorem cyclicRestrictₗ_restrictFirst_groundSpaceMap {A : MPSTensor d D}
    {N L : ℕ} (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N)
    {Y : Matrix (Fin D) (Fin D) ℂ}
    (hY : cyclicRestrictₗ hN (L + 1) i τ ψ = groundSpaceMap A (L + 1) Y)
    (j : Fin d) :
    cyclicRestrictₗ hN L (cyclicForwardSite i 1)
        (fun k => if (k.val + N - i.val) % N = 0 then j else τ k) ψ =
      groundSpaceMap A L (Y * A j) := by
  rw [← cyclicRestrictₗ_restrictFirst hN hLN i τ ψ j, hY,
    restrictFirst_groundSpaceMap]

/-- If a cyclic `(L + 1)`-window is represented by the boundary matrix `Y`, then
fixing its last site to `j` represents the initial length-`L` window by the
boundary matrix `A j * Y`. -/
theorem cyclicRestrictₗ_restrictLast_groundSpaceMap {A : MPSTensor d D}
    {N L : ℕ} (hN : 0 < N)
    (i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N)
    {Y : Matrix (Fin D) (Fin D) ℂ}
    (hY : cyclicRestrictₗ hN (L + 1) i τ ψ = groundSpaceMap A (L + 1) Y)
    (j : Fin d) :
    cyclicRestrictₗ hN L i
        (fun k => if (k.val + N - i.val) % N = L then j else τ k) ψ =
      groundSpaceMap A L (A j * Y) := by
  rw [← cyclicRestrictₗ_restrictLast hN i τ ψ j, hY, restrictLast_groundSpaceMap]

/-- Adjacent cyclic windows have compatible boundary matrices on their common
length-`L` overlap.

The hypothesis `hτ` says that, after the first window is restricted at its first
site and the second window is restricted at its last site, the two outside
configurations give the same restricted vector on the common overlap. -/
theorem adjacent_cyclicRestrictₗ_witness_overlap
    {A : MPSTensor d D} {N L : ℕ}
    (hInj : IsNBlkInjective A L) (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i : Fin N) (τ₁ τ₂ : Fin N → Fin d) (ψ : NSiteSpace d N)
    {Y₁ Y₂ : Matrix (Fin D) (Fin D) ℂ}
    (hY₁ : cyclicRestrictₗ hN (L + 1) i τ₁ ψ = groundSpaceMap A (L + 1) Y₁)
    (hY₂ : cyclicRestrictₗ hN (L + 1) (cyclicForwardSite i 1) τ₂ ψ =
      groundSpaceMap A (L + 1) Y₂)
    (a b : Fin d)
    (hτ :
      (fun k => if (k.val + N - i.val) % N = 0 then a else τ₁ k) =
        (fun k => if (k.val + N - (cyclicForwardSite i 1).val) % N = L then b
          else τ₂ k)) :
    Y₁ * A a = A b * Y₂ := by
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  have hFirst :=
    cyclicRestrictₗ_restrictFirst_groundSpaceMap
      (A := A) hN hLN i τ₁ ψ hY₁ a
  have hLast :=
    cyclicRestrictₗ_restrictLast_groundSpaceMap
      (A := A) hN (cyclicForwardSite i 1) τ₂ ψ hY₂ b
  exact hFirst.symm.trans (by rw [hτ]; exact hLast)

end MPSTensor
