/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FinSum
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient

/-!
# Zero padding of open-chain interactions into a cyclic family

The local terms of an open \(N\)-site chain can be indexed by a cyclic group
\(\mathbb Z/P\mathbb Z\), with \(P\ge N\), by setting every term beyond
the last nonwrapping start equal to zero. Their sum remains the original open
Hamiltonian. The padded terms are symmetric projections and commute at every
oriented cyclic separation of at least the interaction range.

This construction permits the cyclic finite-range Knabe inequality to be
applied to open chains. The resulting open-chain criterion is a consequence
of the finite-range coefficient derivation documented in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`; it is not the
nearest-neighbor periodic statement printed in Knabe (1988).
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The nonwrapping range-\(R\) interactions on an \(N\)-site open chain,
indexed by \(\mathbb Z/P\mathbb Z\) and set equal to zero at every
inactive start. The cyclic period indexes the terms; it does not add physical
sites to the Hilbert space. -/
noncomputable def zmodOpenLocalTermES {N P : ℕ} [NeZero P]
    (A : MPSTensor d D) (R : ℕ) (hR : 0 < R) :
    ZMod P → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  fun s => if hs : s.val + R ≤ N then
    localTermES A R ⟨s.val, by omega⟩ else 0

/-- Every padded term is a symmetric projection, including the zero terms. -/
theorem zmodOpenLocalTermES_isSymmetricProjection {N P R : ℕ} [NeZero P]
    (A : MPSTensor d D) (hR : 0 < R) (s : ZMod P) :
    (zmodOpenLocalTermES (N := N) A R hR s).IsSymmetricProjection := by
  unfold zmodOpenLocalTermES
  split_ifs
  · exact localTermES_isSymmetricProjection A R _
  · exact ⟨by simp [IsIdempotentElem], LinearMap.IsSymmetric.zero⟩

/-- The active padded interactions commute at every oriented cyclic separation
between \(R\) and \(P-R\), as required by the cyclic Knabe inequality. -/
theorem zmodOpenLocalTermES_commute_of_oriented_separation
    {N P R e : ℕ} [NeZero P] (A : MPSTensor d D)
    (hR : 0 < R) (heR : R ≤ e) (heP : e + R ≤ P)
    (s : ZMod P) (v : EuclideanSpace ℂ (Cfg d N)) :
    zmodOpenLocalTermES A R hR s (zmodOpenLocalTermES A R hR (s + (e : ZMod P)) v) =
      zmodOpenLocalTermES A R hR (s + (e : ZMod P)) (zmodOpenLocalTermES A R hR s v) := by
  have he : e < P := by omega
  have hval : (e : ZMod P).val = e := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt he]
  have hsep : s.val + R ≤ (s + (e : ZMod P)).val ∨
      (s + (e : ZMod P)).val + R ≤ s.val := by
    by_cases hwrap : s.val + e < P
    · left
      rw [ZMod.val_add, hval, Nat.mod_eq_of_lt hwrap]
      omega
    · right
      have h := ZMod.val_add_val_of_le (a := s) (b := (e : ZMod P)) (by omega)
      rw [hval] at h
      omega
  unfold zmodOpenLocalTermES
  split_ifs with hs ht
  · rcases hsep with hsep | hsep
    · exact localTermES_commute_of_cyclic_windows_disjoint A (by omega)
        (cyclicWindowsDisjoint_of_nonwrapping_ordered ht hsep) v
    · exact localTermES_commute_of_cyclic_windows_disjoint A (by omega)
        (cyclicWindowsDisjoint_of_nonwrapping_ordered hs hsep).symm v
  · simp
  · simp
  · simp

/-- If the cyclic period is at least the physical volume, summing the padded
interactions gives precisely the original open-chain parent Hamiltonian. -/
theorem sum_zmodOpenLocalTermES_eq_openParentHamiltonianES
    {N P R : ℕ} [NeZero P] (A : MPSTensor d D) (hR : 0 < R) (hNP : N ≤ P) :
    (∑ s : ZMod P, zmodOpenLocalTermES (N := N) A R hR s) =
      openParentHamiltonianES A R N := by
  classical
  let f : Fin N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
    fun i => if i.val + R ≤ N then localTermES A R i else 0
  have hsum : openParentHamiltonianES A R N = ∑ i : Fin N, f i := by
    rw [openParentHamiltonianES]
    change (∑ i : {i : Fin N // i.val + R ≤ N}, localTermES A R i.1) = _
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val + R ≤ N),
          localTermES A R i := (Finset.sum_subtype _ (fun i => by simp) _).symm
      _ = _ := by rw [Finset.sum_filter]
  rw [hsum, Fin.sum_castLE_extend_zero f hNP]
  cases P with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ P =>
    change (∑ s : Fin (P + 1), _) = _
    refine Finset.sum_congr rfl ?_
    intro s _
    change (if hs : s.val + R ≤ N then localTermES A R ⟨s.val, _⟩ else 0) = _
    by_cases hlt : s.val < N
    · simp only [hlt, dite_true, f]
      split_ifs with hs
      · rfl
      · rfl
    · have hinactive : ¬s.val + R ≤ N := by omega
      simp [hlt, hinactive]

end MPSTensor
