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

This file records the elementary matrix identities obtained by deleting one
endpoint from a cyclic window.  The identities are used in the closure-property
comparison for normal parent-Hamiltonian uniqueness.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If a non-repeating cyclic `(L + 1)`-window is represented by the matrix `Y`,
then fixing its first site to `j` represents the shifted length-`L` window by the
matrix `Y * A j`. -/
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

/-- If a cyclic `(L + 1)`-window is represented by the matrix `Y`, then fixing
its last site to `j` represents the initial length-`L` window by the matrix
`A j * Y`. -/
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

/-- Adjacent cyclic windows have compatible matrices on their common length-`L`
overlap.

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

/-- Adjacent cyclic windows with the same outside configuration have compatible
boundary matrices. -/
theorem adjacent_cyclicRestrictₗ_witness_overlap_common_background
    {A : MPSTensor d D} {N L : ℕ}
    (hInj : IsNBlkInjective A L) (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i : Fin N) (ρ : Fin N → Fin d) (ψ : NSiteSpace d N)
    {Y₁ Y₂ : Matrix (Fin D) (Fin D) ℂ}
    (hY₁ : cyclicRestrictₗ hN (L + 1) i ρ ψ = groundSpaceMap A (L + 1) Y₁)
    (hY₂ : cyclicRestrictₗ hN (L + 1) (cyclicForwardSite i 1) ρ ψ =
      groundSpaceMap A (L + 1) Y₂) :
    Y₁ * A (ρ i) = A (ρ (cyclicForwardSite i (L + 1))) * Y₂ := by
  refine adjacent_cyclicRestrictₗ_witness_overlap
    (A := A) hInj hN hLN i ρ ρ ψ hY₁ hY₂
    (ρ i) (ρ (cyclicForwardSite i (L + 1))) ?_
  ext k
  have hleft :
      (if (k.val + N - i.val) % N = 0 then ρ i else ρ k) = ρ k := by
    by_cases hzero : (k.val + N - i.val) % N = 0
    · rw [if_pos hzero]
      have hk : k = i := by
        have hk' := eq_cyclic_site_of_offset_eq (N := N) hN (i := i) (k := k) hzero
        simpa [Nat.mod_eq_of_lt i.isLt] using hk'
      rw [hk]
    · rw [if_neg hzero]
  have hright :
      (if (k.val + N - (cyclicForwardSite i 1).val) % N = L then
          ρ (cyclicForwardSite i (L + 1)) else ρ k) = ρ k := by
    by_cases hlast : (k.val + N - (cyclicForwardSite i 1).val) % N = L
    · rw [if_pos hlast]
      have hkStep : k = cyclicForwardSite (cyclicForwardSite i 1) L := by
        have hk' := eq_cyclic_site_of_offset_eq (N := N) hN
          (i := cyclicForwardSite i 1) (k := k) (r := L) hlast
        simpa [cyclicForwardSite] using hk'
      have hk : k = cyclicForwardSite i (L + 1) := by
        calc
          k = cyclicForwardSite (cyclicForwardSite i 1) L := hkStep
          _ = cyclicForwardSite i (1 + L) := by rw [cyclicForwardSite_forwardSite]
          _ = cyclicForwardSite i (L + 1) := by congr 1; omega
      rw [hk]
    · rw [if_neg hlast]
  rw [hleft, hright]

/-- A finite chain of adjacent matrix identities gives a single word-product
identity. -/
theorem boundary_witness_product_of_adjacent_overlaps
    {A : MPSTensor d D} {n : ℕ}
    (Y : Fin (n + 1) → Matrix (Fin D) (Fin D) ℂ)
    (a b : Fin n → Fin d)
    (hStep : ∀ r : Fin n,
      Y (Fin.castSucc r) * A (a r) = A (b r) * Y (Fin.succ r)) :
    Y 0 * evalWord A (List.ofFn a) =
      evalWord A (List.ofFn b) * Y (Fin.last n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h0 : Y 0 * A (a 0) = A (b 0) * Y 1 := by
        simpa using hStep 0
      let Ytail : Fin (n + 1) → Matrix (Fin D) (Fin D) ℂ := fun r => Y (Fin.succ r)
      let atail : Fin n → Fin d := a ∘ Fin.succ
      let btail : Fin n → Fin d := b ∘ Fin.succ
      have hStepTail : ∀ r : Fin n,
          Ytail (Fin.castSucc r) * A (atail r) = A (btail r) * Ytail (Fin.succ r) := by
        intro r
        have h := hStep (Fin.succ r)
        simpa [Ytail, atail, btail] using h
      have htail := ih Ytail atail btail hStepTail
      rw [evalWord_ofFn_succ A a, evalWord_ofFn_succ A b]
      calc
        Y 0 * (A (a 0) * evalWord A (List.ofFn (a ∘ Fin.succ)))
            = (Y 0 * A (a 0)) * evalWord A (List.ofFn (a ∘ Fin.succ)) := by
                rw [Matrix.mul_assoc]
        _ = (A (b 0) * Y 1) * evalWord A (List.ofFn (a ∘ Fin.succ)) := by
                rw [h0]
        _ = A (b 0) * (Ytail 0 * evalWord A (List.ofFn atail)) := by
                simp [Ytail, atail, Matrix.mul_assoc]
        _ = A (b 0) * (evalWord A (List.ofFn btail) * Ytail (Fin.last n)) := by
                rw [htail]
        _ = (A (b 0) * evalWord A (List.ofFn (b ∘ Fin.succ))) *
              Y (Fin.last (n + 1)) := by
                simp [Ytail, btail, Matrix.mul_assoc]

/-- Iterating adjacent cyclic-window overlaps gives the corresponding
word-product identity between the endpoint matrices. -/
theorem adjacent_cyclicRestrictₗ_witness_product
    {A : MPSTensor d D} {N L n : ℕ}
    (hInj : IsNBlkInjective A L) (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i₀ : Fin N) (τ : Fin (n + 1) → Fin N → Fin d) (ψ : NSiteSpace d N)
    (Y : Fin (n + 1) → Matrix (Fin D) (Fin D) ℂ)
    (a b : Fin n → Fin d)
    (hY : ∀ r : Fin (n + 1),
      cyclicRestrictₗ hN (L + 1) (cyclicForwardSite i₀ r.val) (τ r) ψ =
        groundSpaceMap A (L + 1) (Y r))
    (hτ : ∀ r : Fin n,
      (fun k => if (k.val + N - (cyclicForwardSite i₀ r.val).val) % N = 0
        then a r else τ (Fin.castSucc r) k) =
      (fun k => if (k.val + N - (cyclicForwardSite i₀ (r.val + 1)).val) % N = L
        then b r else τ (Fin.succ r) k)) :
    Y 0 * evalWord A (List.ofFn a) =
      evalWord A (List.ofFn b) * Y (Fin.last n) := by
  apply boundary_witness_product_of_adjacent_overlaps
  intro r
  have hY₁ := hY (Fin.castSucc r)
  have hY₂ : cyclicRestrictₗ hN (L + 1)
      (cyclicForwardSite (cyclicForwardSite i₀ r.val) 1) (τ (Fin.succ r)) ψ =
        groundSpaceMap A (L + 1) (Y (Fin.succ r)) := by
    simpa [cyclicForwardSite_forwardSite, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hY (Fin.succ r)
  have hτr :
      (fun k => if (k.val + N - (cyclicForwardSite i₀ r.val).val) % N = 0
        then a r else τ (Fin.castSucc r) k) =
      (fun k => if
        (k.val + N - (cyclicForwardSite (cyclicForwardSite i₀ r.val) 1).val) % N = L
        then b r else τ (Fin.succ r) k) := by
    simpa [cyclicForwardSite_forwardSite, Nat.add_assoc]
      using hτ r
  exact adjacent_cyclicRestrictₗ_witness_overlap
    (A := A) hInj hN hLN (cyclicForwardSite i₀ r.val)
    (τ (Fin.castSucc r)) (τ (Fin.succ r)) ψ hY₁ hY₂ (a r) (b r) hτr

/-- Iterating adjacent cyclic-window overlaps with a common outside
configuration gives the corresponding word-product identity. -/
theorem adjacent_cyclicRestrictₗ_witness_product_common_background
    {A : MPSTensor d D} {N L n : ℕ}
    (hInj : IsNBlkInjective A L) (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i₀ : Fin N) (ρ : Fin N → Fin d) (ψ : NSiteSpace d N)
    (Y : Fin (n + 1) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ r : Fin (n + 1),
      cyclicRestrictₗ hN (L + 1) (cyclicForwardSite i₀ r.val) ρ ψ =
        groundSpaceMap A (L + 1) (Y r)) :
    Y 0 * evalWord A (List.ofFn (fun r : Fin n => ρ (cyclicForwardSite i₀ r.val))) =
      evalWord A (List.ofFn (fun r : Fin n =>
        ρ (cyclicForwardSite (cyclicForwardSite i₀ r.val) (L + 1)))) *
        Y (Fin.last n) := by
  apply boundary_witness_product_of_adjacent_overlaps
  intro r
  have hY₁ := hY (Fin.castSucc r)
  have hY₂ : cyclicRestrictₗ hN (L + 1)
      (cyclicForwardSite (cyclicForwardSite i₀ r.val) 1) ρ ψ =
        groundSpaceMap A (L + 1) (Y (Fin.succ r)) := by
    simpa [cyclicForwardSite_forwardSite, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hY (Fin.succ r)
  exact adjacent_cyclicRestrictₗ_witness_overlap_common_background
    (A := A) hInj hN hLN (cyclicForwardSite i₀ r.val) ρ ψ hY₁ hY₂

end MPSTensor
