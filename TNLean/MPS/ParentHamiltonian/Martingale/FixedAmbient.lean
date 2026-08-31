/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Semisimple
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.ProjectionCancellation

/-!
# Fixed-ambient open-chain ground projections

This file realizes the projections in Nachtergaele's martingale argument on one
fixed \(N\)-site Hilbert space. The prefix Hamiltonian at level \(n\) contains the
nonwrapping local interactions whose support lies in \([0,n)\). Its kernel
projection is therefore a decreasing family on
`EuclideanSpace ℂ (Cfg d N)`, rather than a family whose ambient type changes
with \(n\).

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

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The kernel projection of a linear map commutes with the kernel projection
of a commuting symmetric operator.

The point is not merely that the operators commute. Commutation makes
\(\ker S\) invariant under \(T\); symmetry of \(T\) makes its orthogonal complement
invariant as well. Hence the orthogonal projection onto \(\ker S\) commutes with
\(T\), and the same invariant-subspace argument applied to \(\ker T\) gives
commutation of the two kernel projections. -/
theorem IsSymmetric.kernelProjection_commute_of_commute {S T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric)
    (hcomm : S.comp T = T.comp S) :
    (LinearMap.ker S).starProjection.toLinearMap.comp
        (LinearMap.ker T).starProjection.toLinearMap =
      (LinearMap.ker T).starProjection.toLinearMap.comp
        (LinearMap.ker S).starProjection.toLinearMap := by
  let PS := (LinearMap.ker S).starProjection.toLinearMap
  let PT := (LinearMap.ker T).starProjection.toLinearMap
  have hkerS : LinearMap.ker S ∈ Module.End.invtSubmodule T := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simpa [hx] using congrArg (fun f : E →ₗ[ℂ] E => f x) hcomm
  have hkerSperp : (LinearMap.ker S)ᗮ ∈ Module.End.invtSubmodule T :=
    hT.orthogonalComplement_mem_invtSubmodule hkerS
  have hPST : Commute PS T := by
    apply (LinearMap.IsIdempotentElem.commute_iff
      (Submodule.isSymmetricProjection_starProjection
        (LinearMap.ker S)).isIdempotentElem).mpr
    simpa only [PS, Submodule.range_starProjection, Submodule.ker_starProjection] using
      And.intro hkerS hkerSperp
  have hkerT : LinearMap.ker T ∈ Module.End.invtSubmodule PS := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simpa [hx] using congrArg (fun f : E →ₗ[ℂ] E => f x) hPST.eq.symm
  have hkerTperp : (LinearMap.ker T)ᗮ ∈ Module.End.invtSubmodule PS :=
    (Submodule.isSymmetricProjection_starProjection (LinearMap.ker S)).isSymmetric
      |>.orthogonalComplement_mem_invtSubmodule hkerT
  have hPTPS : Commute PT PS := by
    apply (LinearMap.IsIdempotentElem.commute_iff
      (Submodule.isSymmetricProjection_starProjection
        (LinearMap.ker T)).isIdempotentElem).mpr
    simpa only [PT, Submodule.range_starProjection, Submodule.ker_starProjection] using
      And.intro hkerT hkerTperp
  simpa only [PS, PT, Module.End.mul_eq_comp] using hPTPS.eq.symm

end LinearMap

/-- Orthogonal projections onto nested submodules commute. -/
theorem Submodule.starProjection_commute_of_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {U V : Submodule ℂ E}
    (hUV : U ≤ V) :
    U.starProjection.toLinearMap.comp V.starProjection.toLinearMap =
      V.starProjection.toLinearMap.comp U.starProjection.toLinearMap := by
  have hleft : U.starProjection.toLinearMap.comp V.starProjection.toLinearMap =
      U.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    change U.starProjection (V.starProjection x) = U.starProjection x
    exact congrArg (fun f : E →L[ℂ] E => f x)
      (Submodule.starProjection_comp_starProjection_of_le hUV)
  have hright : V.starProjection.toLinearMap.comp U.starProjection.toLinearMap =
      U.starProjection.toLinearMap := by
    ext x
    apply ext_inner_left ℂ
    intro y
    calc
      ⟪y, V.starProjection (U.starProjection x)⟫_ℂ =
          ⟪V.starProjection y, U.starProjection x⟫_ℂ :=
        (V.starProjection_isSymmetric y (U.starProjection x)).symm
      _ = ⟪U.starProjection (V.starProjection y), x⟫_ℂ :=
        (U.starProjection_isSymmetric (V.starProjection y) x).symm
      _ = ⟪U.starProjection y, x⟫_ℂ := by
        rw [← ContinuousLinearMap.comp_apply,
          Submodule.starProjection_comp_starProjection_of_le hUV]
      _ = ⟪y, U.starProjection x⟫_ℂ := U.starProjection_isSymmetric y x
  exact hleft.trans hright.symm

namespace MPSTensor

variable {d D : ℕ}

/-- A nonwrapping interaction start whose length-\(L\) support lies in the prefix
\([0,n)\) of a fixed \(N\)-site chain. -/
abbrev OpenPrefixStart (L N n : ℕ) :=
  {i : NonwrappingStart L N // i.1.val + L ≤ n}

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

/-- The parent Hamiltonian of the prefix \([0,n)\), acting on the fixed ambient
space of an \(N\)-site open chain. -/
noncomputable def openPrefixParentHamiltonianES (A : MPSTensor d D)
    (L N n : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : OpenPrefixStart L N n, localTermES A L i.1.1

/-- The fixed-ambient ground projection of the prefix \([0,n)\). -/
noncomputable def openPrefixGroundProjectionES (A : MPSTensor d D)
    (L N n : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (LinearMap.ker (openPrefixParentHamiltonianES A L N n)).starProjection.toLinearMap

/-- The fixed-ambient local ground projection on \([n-l,n+1)\).

Its Hamiltonian sums exactly the starts satisfying \(n-l\leq i\) and
\(i+L\leq n+1\). -/
noncomputable def openIntervalGroundProjectionES (A : MPSTensor d D)
    (L l N n : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (LinearMap.ker
    (openSuffixParentHamiltonianES A L (l + 1) N (n + 1))).starProjection.toLinearMap

/-- If a fixed-ambient prefix Hamiltonian annihilates a vector, every local
interaction contained in that prefix annihilates it. -/
theorem localTermES_eq_zero_of_openPrefixParentHamiltonianES_eq_zero
    (A : MPSTensor d D) (L N n : ℕ) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : openPrefixParentHamiltonianES A L N n v = 0)
    (i : OpenPrefixStart L N n) :
    localTermES A L i.1.1 v = 0 := by
  rw [openPrefixParentHamiltonianES] at hv
  exact ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun i : OpenPrefixStart L N n => localTermES A L i.1.1)
    (fun i => localTermES_isSymmetricProjection A L i.1.1) hv i

/-- Prefix kernels decrease when the prefix grows. -/
theorem ker_openPrefixParentHamiltonianES_antitone (A : MPSTensor d D)
    (L N : ℕ) :
    Antitone fun n => LinearMap.ker (openPrefixParentHamiltonianES A L N n) := by
  intro m n hmn v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [openPrefixParentHamiltonianES, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact localTermES_eq_zero_of_openPrefixParentHamiltonianES_eq_zero A L N n hv
    ⟨i.1, i.2.trans hmn⟩

/-- The prefix kernel projections form Nachtergaele's decreasing ground-space
filtration on the single ambient \(N\)-site Hilbert space. -/
noncomputable def fixedAmbientNestedGroundProjectionsES (A : MPSTensor d D)
    (L N : ℕ) :
    FrustrationFree.NestedGroundProjections
      (E := EuclideanSpace ℂ (Cfg d N)) where
  projection := openPrefixGroundProjectionES A L N
  isSymmetricProjection n := by
    exact Submodule.isSymmetricProjection_starProjection _
  antitone_range := by
    intro m n hmn
    simpa only [openPrefixGroundProjectionES, Submodule.range_starProjection] using
      ker_openPrefixParentHamiltonianES_antitone A L N hmn

/-- The fixed-ambient prefix Hamiltonian is positive. -/
theorem openPrefixParentHamiltonianES_isPositive (A : MPSTensor d D)
    (L N n : ℕ) : (openPrefixParentHamiltonianES A L N n).IsPositive := by
  rw [openPrefixParentHamiltonianES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i.1.1

/-- A fixed-ambient suffix-interval Hamiltonian is positive. -/
theorem openSuffixParentHamiltonianES_isPositive (A : MPSTensor d D)
    (L l N n : ℕ) : (openSuffixParentHamiltonianES A L l N n).IsPositive := by
  rw [openSuffixParentHamiltonianES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i.1

/-- A prefix Hamiltonian ending before a suffix interval starts commutes with
that interval Hamiltonian.  The proof expands both finite sums and uses
site-disjoint commutation for every pair of local interactions. -/
theorem openPrefixParentHamiltonianES_commute_openSuffixParentHamiltonianES
    (A : MPSTensor d D) {L l N m n : ℕ} (hLN : L ≤ N)
    (hsep : m ≤ n - l) :
    (openPrefixParentHamiltonianES A L N m).comp
        (openSuffixParentHamiltonianES A L l N n) =
      (openSuffixParentHamiltonianES A L l N n).comp
        (openPrefixParentHamiltonianES A L N m) := by
  apply LinearMap.ext
  intro v
  simp only [openPrefixParentHamiltonianES, openSuffixParentHamiltonianES,
    LinearMap.comp_apply, LinearMap.sum_apply]
  simp_rw [map_sum]
  rw [Finset.sum_comm'
    (s := Finset.univ)
    (t := fun _ => Finset.univ.filter fun i : NonwrappingStart L N =>
      n - l ≤ i.1.val ∧ i.1.val + L ≤ n)
    (t' := Finset.univ.filter fun i : NonwrappingStart L N =>
      n - l ≤ i.1.val ∧ i.1.val + L ≤ n)
    (s' := fun _ => Finset.univ)
    (fun _ _ => by simp)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_filter] at hj
  apply Finset.sum_congr rfl
  intro i _
  exact localTermES_commute_of_cyclic_windows_disjoint A hLN
    (cyclicWindowsDisjoint_of_nonwrapping_ordered j.2 (by omega)) v

/-- Prefix and local-interval ground projections commute when their supporting
Hamiltonians are disjoint.  The passage from Hamiltonian commutation to kernel-
projection commutation uses the invariant-subspace theorem
`LinearMap.IsSymmetric.kernelProjection_commute_of_commute`. -/
theorem openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
    (A : MPSTensor d D) {L l N m n : ℕ} (hLN : L ≤ N)
    (hsep : m ≤ n - l) :
    (openPrefixGroundProjectionES A L N m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        (openPrefixGroundProjectionES A L N m) := by
  apply LinearMap.IsSymmetric.kernelProjection_commute_of_commute
    (openSuffixParentHamiltonianES_isPositive A L (l + 1) N (n + 1)).isSymmetric
  exact openPrefixParentHamiltonianES_commute_openSuffixParentHamiltonianES A hLN
    (by omega)

/-- Once a prefix extends past \(n\), its ground space is contained in the local
ground space on \([n-l,n+1)\). -/
theorem ker_openPrefixParentHamiltonianES_le_ker_openSuffixParentHamiltonianES
    (A : MPSTensor d D) {L l N m n : ℕ} (hnm : n < m) :
    LinearMap.ker (openPrefixParentHamiltonianES A L N m) ≤
      LinearMap.ker (openSuffixParentHamiltonianES A L (l + 1) N (n + 1)) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [openSuffixParentHamiltonianES, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  exact localTermES_eq_zero_of_openPrefixParentHamiltonianES_eq_zero A L N m hv
    ⟨i, by omega⟩

/-- Prefix and local-interval ground projections commute when the local ground
space contains the prefix ground space. -/
theorem openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
    (A : MPSTensor d D) {L l N m n : ℕ} (hnm : n < m) :
    (openPrefixGroundProjectionES A L N m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        (openPrefixGroundProjectionES A L N m) := by
  exact Submodule.starProjection_commute_of_le
    (ker_openPrefixParentHamiltonianES_le_ker_openSuffixParentHamiltonianES
      A hnm)

/-- The physical fixed-ambient martingale difference commutes with the local
ground projection outside the active interval \([n-l,n]\).

For \(m<n-l\), both prefix projections in \(E_m=G_m-G_{m+1}\) are supported to
the left of \([n-l,n+1)\). For \(n<m\), both prefix kernels are contained in the
local interval kernel. -/
theorem fixedAmbient_martingaleDifference_commute_openIntervalGroundProjectionES
    (A : MPSTensor d D) {L l N m n : ℕ} (hLN : L ≤ N)
    (hout : m < n - l ∨ n < m) :
    ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m).comp
        (openIntervalGroundProjectionES A L l N n) =
      (openIntervalGroundProjectionES A L l N n).comp
        ((fixedAmbientNestedGroundProjectionsES A L N).martingaleDifference m) := by
  simp only [FrustrationFree.NestedGroundProjections.martingaleDifference,
    fixedAmbientNestedGroundProjectionsES, LinearMap.sub_comp, LinearMap.comp_sub]
  rcases hout with hleft | hright
  · rw [openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A hLN (by omega),
      openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A hLN (by omega)]
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
    (A : MPSTensor d D) {L N n l : ℕ} (hLN : L ≤ N) (hn : n < N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
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
    A hLN hout

end MPSTensor
