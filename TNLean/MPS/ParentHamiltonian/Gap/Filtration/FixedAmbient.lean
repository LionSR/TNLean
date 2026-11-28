/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Semisimple
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import QICLean.ManyBody.Hamiltonian.Martingale.ProjectionCancellation
import QICLean.Analysis.Projection.CommutingProjectionProduct

/-!
# Fixed-ambient open-chain ground projections

This file realizes the projections in Nachtergaele's martingale argument on one
fixed \(N\)-site Hilbert space. The prefix Hamiltonian at level \(n\) contains the
nonwrapping local interactions whose support lies in \([0,n)\). Its kernel
projection is therefore a decreasing family on this fixed ambient Hilbert
space, rather than a family whose ambient type changes with \(n\).

For the local interval \([n-l,n+1)\), the ground projection is the kernel
projection of the sum over starts \(n-l\leq i\) and \(i+L\leq n+1\). We prove the
outside-window commutation used between equations \(Enpsi\) and \(Enpsi2\) in the
proof of Theorem 2.1(i).

## References

* Nachtergaele, arXiv:cond-mat/9410110, equation (En), lines 1060--1073.
* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(i), equations \(Enpsi\)
  and \(Enpsi2\), lines 1206--1220.
-/

open scoped BigOperators InnerProductSpace
open FrustrationFree.NestedGroundProjections

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-- Ordered nonwrapping windows are cyclically site-disjoint. -/
theorem cyclicWindowsDisjoint_of_nonwrapping_ordered {N L : ℕ} {i j : Fin N}
    (hj : j.val + L ≤ N) (hij : i.val + L ≤ j.val) :
    CyclicWindowsDisjoint L i j := by
  intro k hki hkj
  let ri := (k.val + N - i.val) % N
  let rj := (k.val + N - j.val) % N
  have hkiEq := eq_cyclic_site_of_offset_eq (Fin.pos i)
    (i := i) (k := k) (r := ri) rfl
  have hkjEq := eq_cyclic_site_of_offset_eq (Fin.pos j)
    (i := j) (k := k) (r := rj) rfl
  have hirN : i.val + ri < N := by omega
  have hjrN : j.val + rj < N := by omega
  have hkri : k.val = i.val + ri := by
    simpa only [Fin.val_mk, Nat.mod_eq_of_lt hirN] using congrArg Fin.val hkiEq
  have hkrj : k.val = j.val + rj := by
    simpa only [Fin.val_mk, Nat.mod_eq_of_lt hjrN] using congrArg Fin.val hkjEq
  omega

/-- The fixed-ambient ground projection of the prefix \([0,n)\). -/
noncomputable def openPrefixGroundProjectionES (A : MPTensor α (Fin D))
    (L N n : ℕ) :
    EuclideanSpace ℂ (Fin N → α) →ₗ[ℂ] EuclideanSpace ℂ (Fin N → α) :=
  (LinearMap.ker
      (Matrix.toEuclideanLin
          ((parentChainInteraction A L N).restrict fun i ↦ i.val + L ≤
              n).hamiltonian)).starProjection.toLinearMap

/-- The fixed-ambient local ground projection on \([n-l,n+1)\).

Its Hamiltonian sums exactly the starts satisfying \(n-l\leq i\) and
\(i+L\leq n+1\). -/
noncomputable def openIntervalGroundProjectionES (A : MPTensor α (Fin D))
    (L l N n : ℕ) :
    EuclideanSpace ℂ (Fin N → α) →ₗ[ℂ] EuclideanSpace ℂ (Fin N → α) :=
  (LinearMap.ker
    (Matrix.toEuclideanLin
        ((parentChainInteraction A L N).restrict fun i ↦ n + 1 - (l + 1) ≤ i.val ∧ i.val + L ≤ n +
            1).hamiltonian)).starProjection.toLinearMap

/-- Prefix kernels decrease when the prefix grows. -/
theorem ker_hamiltonian_prefix_parentChainInteraction_antitone (A : MPTensor α (Fin D))
    (L N : ℕ) :
    Antitone fun n => LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A L N).restrict fun i ↦ i.val + L ≤ n).hamiltonian) := by
  intro m n hmn v hv
  rw [ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff
    (posSemidef_parentChainInteraction_term A L N)] at hv ⊢
  exact fun i hi ↦ hv i (hi.trans hmn)

/-- The prefix kernel projections form Nachtergaele's decreasing ground-space
filtration on the single ambient \(N\)-site Hilbert space. -/
noncomputable def fixedAmbientNestedGroundProjectionsES (A : MPTensor α (Fin D))
    (L N : ℕ) :
    FrustrationFree.NestedGroundProjections
      (E := EuclideanSpace ℂ (Fin N → α)) where
  projection := openPrefixGroundProjectionES A L N
  isSymmetricProjection n := by
    exact Submodule.isSymmetricProjection_starProjection _
  antitone_range := by
    intro m n hmn
    simpa only [openPrefixGroundProjectionES, Submodule.range_starProjection] using
      ker_hamiltonian_prefix_parentChainInteraction_antitone A L N hmn

/-- A prefix Hamiltonian ending before a suffix interval starts commutes with
that interval Hamiltonian: every pair of their terms has disjoint windows. -/
theorem hamiltonian_prefix_parentChainInteraction_commute_restrict
    (A : MPTensor α (Fin D)) {L l N m n : ℕ} (hsep : m ≤ n - l) :
    (Matrix.toEuclideanLin
        ((parentChainInteraction A L N).restrict fun i ↦ i.val + L ≤ m).hamiltonian).comp
        (Matrix.toEuclideanLin
            ((parentChainInteraction A L N).restrict fun i ↦ n - l ≤ i.val ∧ i.val + L ≤
                n).hamiltonian) =
      (Matrix.toEuclideanLin
          ((parentChainInteraction A L N).restrict fun i ↦ n - l ≤ i.val ∧ i.val + L ≤
              n).hamiltonian).comp
        (Matrix.toEuclideanLin
            ((parentChainInteraction A L N).restrict fun i ↦ i.val + L ≤ m).hamiltonian) := by
  rw [← Matrix.toEuclideanLin_mul, ← Matrix.toEuclideanLin_mul]
  exact congrArg _ (ManyBody.Interaction.commute_hamiltonian_restrict _ _ fun i j hi hj ↦
    commute_parentChainInteraction_term_of_add_le A (by omega)).eq

/-- Prefix and local-interval ground projections commute when their supporting
Hamiltonians are disjoint.  Hamiltonian commutation makes both kernels and their
orthogonal complements invariant, which yields projection commutation. -/
theorem openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
    (A : MPTensor α (Fin D)) {L l N m n : ℕ} (hsep : m ≤ n - l) :
    (openPrefixGroundProjectionES A L N m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        (openPrefixGroundProjectionES A L N m) := by
  apply LinearMap.IsSymmetric.kernelProjection_commute_of_commute
    (Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_hamiltonian_restrict_parentChainInteraction A L N _)).isSymmetric
  exact hamiltonian_prefix_parentChainInteraction_commute_restrict A (by omega)

/-- Once a prefix extends past \(n\), its ground space is contained in the local
ground space on \([n-l,n+1)\). -/
theorem ker_hamiltonian_prefix_parentChainInteraction_le_ker_restrict
    (A : MPTensor α (Fin D)) {L l N m n : ℕ} (hnm : n < m) :
    LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A L N).restrict fun i ↦ i.val + L ≤ m).hamiltonian) ≤
      LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A L N).restrict fun i ↦ n + 1 - (l + 1) ≤ i.val ∧ i.val + L ≤
                  n + 1).hamiltonian) := by
  intro v hv
  rw [ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff
    (posSemidef_parentChainInteraction_term A L N)] at hv ⊢
  exact fun i hi ↦ hv i (by omega)

/-- Prefix and local-interval ground projections commute when the local ground
space contains the prefix ground space. -/
theorem openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
    (A : MPTensor α (Fin D)) {L l N m n : ℕ} (hnm : n < m) :
    (openPrefixGroundProjectionES A L N m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        (openPrefixGroundProjectionES A L N m) := by
  exact Submodule.starProjection_commute_of_le
    (ker_hamiltonian_prefix_parentChainInteraction_le_ker_restrict
      A hnm)

/-- The physical fixed-ambient martingale difference commutes with the local
ground projection outside the active interval \([n-l,n]\).

For \(m<n-l\), both prefix projections in \(E_m=G_m-G_{m+1}\) are supported to
the left of \([n-l,n+1)\). For \(n<m\), both prefix kernels are contained in the
local interval kernel. -/
theorem fixedAmbient_martingaleDifference_commute_openIntervalGroundProjectionES
    (A : MPTensor α (Fin D)) {L l N m n : ℕ} (hout : m < n - l ∨ n < m) :
    ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m) := by
  simp only [FrustrationFree.NestedGroundProjections.martingaleDifference,
    fixedAmbientNestedGroundProjectionsES, LinearMap.sub_comp, LinearMap.comp_sub]
  rcases hout with hleft | hright
  · rw [openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A (by omega),
      openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A (by omega)]
  · rw [openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
        A hright,
      openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
        A (by omega)]

/-- Physical fixed-ambient form of the closed-interval cancellation identity in
Nachtergaele's proof of Theorem 2.1(i).

Here \(G_m\) is the kernel projection of the prefix Hamiltonian on \([0,m)\),
\(E_m=G_m-G_{m+1}\), and \(Q_n\) is the kernel projection of the local Hamiltonian
on \([n-l,n+1)\). -/
theorem inner_sum_fixedAmbient_martingaleDifference_openIntervalGroundProjectionES_eq_Icc
    (A : MPTensor α (Fin D)) {L N n l : ℕ} (hn : n < N)
    (v : EuclideanSpace ℂ (Fin N → α)) :
    inner ℂ v (∑ m ∈ Finset.range N,
        (fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m
          (openIntervalGroundProjectionES A L l N n
            ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference n v))) =
      inner ℂ (∑ m ∈ Finset.Icc (n - l) n,
        (fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m v)
        (openIntervalGroundProjectionES A L l N n
          ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference n v)) := by
  apply inner_sum_martingaleDifference_localProjection_eq_inner_sum_Icc
    (fixedAmbientNestedGroundProjectionsES A L N)
    (openIntervalGroundProjectionES A L l N n) N n l hn
  intro m hout
  exact fixedAmbient_martingaleDifference_commute_openIntervalGroundProjectionES
    A hout

end MPSTensor
