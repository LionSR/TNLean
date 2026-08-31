/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport
import QICLean.Analysis.FiniteRangeKnabe

/-!
# Cyclic windows as open parent Hamiltonians

This file identifies a finite cyclic block of periodic parent-Hamiltonian terms
with the corresponding open-chain Hamiltonian on its active sites.  If the
periodic interaction range is `R` and the block contains `m` local terms, the
active interval has exactly `W = m + R - 1` sites.

The construction is the geometric input needed to apply the finite-range Knabe
inequality after the open-chain gap estimate.  It does not compare periodic and
open kernels.

## References

* Knabe, J. Stat. Phys. 52, 627 (1988).
* Pérez-García et al., arXiv:quant-ph/0608197, lines 1483--1489.
* Cirac--Perez-García--Schuch--Verstraete, arXiv:2011.12127, lines 2194--2197.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The periodic local-term family indexed by the cyclic group of sites. -/
noncomputable def zmodLocalTermES {N : ℕ} [NeZero N]
    (A : MPSTensor d D) (R : ℕ) :
    ZMod N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  fun s ↦ localTermES A R ((ZMod.finEquiv N).symm s)

/-- Reindexing periodic local terms by `ZMod N` preserves their total sum. -/
theorem sum_zmodLocalTermES_eq_parentHamiltonianES {N : ℕ} [NeZero N]
    (A : MPSTensor d D) (R : ℕ) :
    (∑ s : ZMod N, zmodLocalTermES A R s) = parentHamiltonianES A R N := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  calc
    (∑ s : ZMod N, zmodLocalTermES A R s) =
        ∑ i : Fin N, zmodLocalTermES A R (ZMod.finEquiv N i) :=
      ((ZMod.finEquiv N).toEquiv.sum_comp (zmodLocalTermES A R)).symm
    _ = ∑ i : Fin N, localTermES A R i := by
      simp [zmodLocalTermES]

/-- Addition in `ZMod N` is cyclic forward motion on the corresponding finite site. -/
theorem finEquiv_symm_add_eq_cyclicForwardSite {N : ℕ} [NeZero N]
    (s : ZMod N) (q : ℕ) :
    (ZMod.finEquiv N).symm (s + q) =
      cyclicForwardSite ((ZMod.finEquiv N).symm s) q := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
      apply Fin.ext
      change (s.val + (q : ZMod (N + 1)).val) % (N + 1) =
        (s.val + q) % (N + 1)
      rw [ZMod.val_natCast, Nat.add_mod_mod]

/-- Two range-`R` cyclic windows are disjoint when their oriented start
separation `e` satisfies `R ≤ e` and `e + R ≤ N`. -/
theorem cyclicWindowsDisjoint_cyclicForwardSite_of_oriented_separation
    {N R e : ℕ} (hR : R ≤ e) (he : e + R ≤ N) (i : Fin N) :
    CyclicWindowsDisjoint R i (cyclicForwardSite i e) := by
  intro k hki hkj
  let a := (k.val + N - i.val) % N
  let b := (k.val + N - (cyclicForwardSite i e).val) % N
  have haR : a < R := hki
  have hbR : b < R := hkj
  have haN : a < N := by omega
  have hbN : b < N := by omega
  have hka : k = cyclicForwardSite i a := by
    simpa [a, cyclicForwardSite] using
      eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k) (r := a) rfl
  have hkb : k = cyclicForwardSite (cyclicForwardSite i e) b := by
    simpa [b, cyclicForwardSite] using
      eq_cyclic_site_of_offset_eq (Fin.pos (cyclicForwardSite i e))
        (i := cyclicForwardSite i e) (k := k) (r := b) rfl
  have hebN : e + b < N := by omega
  have heq : cyclicForwardSite i a = cyclicForwardSite i (e + b) := by
    rw [← cyclicForwardSite_forwardSite]
    exact hka.symm.trans hkb
  have hval := congrArg Fin.val heq
  simp only [cyclicForwardSite, Fin.val_mk] at hval
  have hmodEq : i.val + a ≡ i.val + (e + b) [MOD N] := by
    simpa [Nat.ModEq] using hval
  have hcancel : a ≡ e + b [MOD N] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl i.val) hmodEq
  have hab : a = e + b := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt haN, Nat.mod_eq_of_lt hebN] using hcancel
  omega

/-- The oriented-separation condition gives the commutation hypothesis used in
the finite-range Knabe inequality. -/
theorem zmodLocalTermES_commute_of_oriented_separation {N R e : ℕ} [NeZero N]
    (A : MPSTensor d D) (hR : R ≤ e) (he : e + R ≤ N)
    (s : ZMod N) (v : EuclideanSpace ℂ (Cfg d N)) :
    zmodLocalTermES A R s (zmodLocalTermES A R (s + (e : ZMod N)) v) =
      zmodLocalTermES A R (s + (e : ZMod N)) (zmodLocalTermES A R s v) := by
  rw [zmodLocalTermES, zmodLocalTermES,
    finEquiv_symm_add_eq_cyclicForwardSite]
  exact localTermES_commute_of_cyclic_windows_disjoint A (by omega)
    (cyclicWindowsDisjoint_cyclicForwardSite_of_oriented_separation hR he _) v

/-- Split a periodic configuration into a cyclic active block of length `W` and
its ordered complement. -/
def cyclicActiveBlockConfigEquiv {N : ℕ} (d W : ℕ) (hWN : W ≤ N) (s : Fin N) :
    Cfg d N ≃ Cfg d W × Cfg d (N - W) :=
  ((Equiv.sumArrowEquivProdArrow (Fin W) (Fin (N - W)) (Fin d)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
      (cyclicWindowIndexEquiv W N hWN s))).symm

/-- The Hilbert-space reindexing that exposes a cyclic active block and its
spectator sites. -/
noncomputable def cyclicActiveBlockConfigLinearIsometryEquiv {N : ℕ}
    (d W : ℕ) (hWN : W ≤ N) (s : Fin N) :
    EuclideanSpace ℂ (Cfg d N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d W × Cfg d (N - W)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (cyclicActiveBlockConfigEquiv d W hWN s)

/-- Joining active and spectator configurations is the inverse cyclic-block split. -/
@[simp] theorem cyclicActiveBlockConfigEquiv_symm_apply_window {N W : ℕ}
    (hWN : W ≤ N) (s : Fin N) (σ : Cfg d W) (τ : Cfg d (N - W))
    (r : Fin W) :
    (cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)
        (cyclicForwardSite s r.val) = σ r := by
  change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
      (cyclicWindowIndexEquiv W N hWN s)
      ((Equiv.sumArrowEquivProdArrow (Fin W) (Fin (N - W)) (Fin d)).symm
        (σ, τ))
      (cyclicWindowIndexEquiv W N hWN s (Sum.inl r)) = σ r
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

end MPSTensor
