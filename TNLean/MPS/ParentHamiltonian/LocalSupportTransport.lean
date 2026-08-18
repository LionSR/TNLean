/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.LocalSupport
import TNLean.MPS.ParentHamiltonian.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Three-site local support and cyclic transport

This file first identifies the three-site MPS ground space with the
intersection of the kernels of its two adjacent length-two parent interactions.
It then transports local relations between these interactions to every
translated three-site window of a longer periodic chain, including a generic
anticommutator quadratic-form inequality and the commuting specialization.

The chain-length hypothesis is (3 \leq N), matching the (N>2) condition in
arXiv:1606.00608, Theorem 3.10 and the local relation
\([\tau_1(P_2),P_2]=0\) in Definition 3.9.

## Main statements

* `adjacent_localTerm_eq_zero_iff_mem_groundSpace_succ` characterizes the
  \((L+1)\)-site ground space by the two adjacent length-\(L\) kernels.
* `groundSpace_three_eq_adjacent_twoSite_parent_kernels` gives the three-site
  specialization for the canonical two-site parent interaction.
* `re_inner_localTermES_adjacent_twoSite_forward_ge_of_threeSite` and
  `re_inner_localTermES_adjacent_twoSite_backward_ge_of_threeSite` transport a
  three-site anticommutator quadratic-form estimate to every cyclic adjacent pair.
* `localTerm_adjacent_twoSite_commute_of_threeSite_zero_one_commute` transports
  the three-site commutator to every translated three-site window.

## References

* arXiv:2011.12127, Section IV.C.
* arXiv:1606.00608, Definition 3.9 and Appendix D, Definition D.2.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Three-site kernel intersection -/

/-- On an injective MPS tensor, a vector on \(L+1\) sites lies in the local MPS
ground space precisely when both adjacent length-\(L\) parent interactions
annihilate it.

This is the function-space form of the standard MPS intersection property. It
is obtained from the Euclidean-space statement without changing the two local
operators.

Source: arXiv:2011.12127, Section IV.C, lines 2013--2078. -/
theorem adjacent_localTerm_eq_zero_iff_mem_groundSpace_succ
    {A : MPSTensor d D} (hA : IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : NSiteSpace d (L + 1)} :
    localTerm A L (L + 1) (0 : Fin (L + 1)) v = 0 ∧
        localTerm A L (L + 1) (1 : Fin (L + 1)) v = 0 ↔
      v ∈ groundSpace A (L + 1) := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have h := adjacent_localTermES_eq_zero_iff_mem_groundSpaceES_succ
    hA hL (v := e.symm v)
  simpa [localTermES, e, mem_groundSpaceES_iff] using h

/-- The three-site MPS ground space of an injective tensor is the intersection
of the kernels of the two adjacent canonical two-site parent interactions:
\[
  G_3(A)=\ker(q_2(A)_{AX})\cap\ker(q_2(A)_{XB}).
\]

This is the three-site specialization of the MPS intersection property, written
in the local-support notation of arXiv:1606.00608, Definition D.2.

Source: arXiv:1606.00608, Definition D.2, lines 2205--2218;
arXiv:2011.12127, Section IV.C, lines 2013--2078. -/
theorem groundSpace_three_eq_adjacent_twoSite_parent_kernels
    {A : MPSTensor d D} (hA : IsInjective A) :
    groundSpace A 3 =
      LinearMap.ker (leftPairLift (parentInteraction A 2)) ⊓
        LinearMap.ker (rightPairLift (parentInteraction A 2)) := by
  ext v
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
  rw [← localTerm_two_three_zero_eq_leftPairLift_parentInteraction]
  rw [← localTerm_two_three_one_eq_rightPairLift_parentInteraction]
  exact (adjacent_localTerm_eq_zero_iff_mem_groundSpace_succ
    hA (by omega : 1 < 2)).symm

private theorem extractWindow_two_replaceWindow_three_left
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N) (σ : Cfg d 3) :
    extractWindow 2 i (replaceWindow 3 hN i τ σ) = extractWindow 2 (0 : Fin 3) σ := by
  funext j
  have hfull := congrFun (extractWindow_replaceWindow 3 hN i τ σ)
    (Fin.castLE (by omega) j)
  rw [show extractWindow 2 i (replaceWindow 3 hN i τ σ) j =
      extractWindow 3 i (replaceWindow 3 hN i τ σ) (Fin.castLE (by omega) j) by
    rfl]
  rw [hfull]
  apply congrArg σ
  apply Fin.ext
  simpa only [Fin.val_castLE, Fin.val_mk, Fin.val_zero, Nat.zero_add] using
    (Nat.mod_eq_of_lt (by omega : j.val < 3)).symm

private theorem extractWindow_two_replaceWindow_three_right
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N) (σ : Cfg d 3) :
    extractWindow 2 (cyclicForwardSite i 1) (replaceWindow 3 hN i τ σ) =
      extractWindow 2 (1 : Fin 3) σ := by
  funext j
  let k : Fin 3 := ⟨j.val + 1, by omega⟩
  have hfull := congrFun (extractWindow_replaceWindow 3 hN i τ σ) k
  rw [show extractWindow 2 (cyclicForwardSite i 1) (replaceWindow 3 hN i τ σ) j =
      extractWindow 3 i (replaceWindow 3 hN i τ σ) k by
    apply congrArg (replaceWindow 3 hN i τ σ)
    apply Fin.ext
    change (cyclicForwardSite (cyclicForwardSite i 1) j.val).val =
      (cyclicForwardSite i k.val).val
    rw [cyclicForwardSite_forwardSite]
    congr 2
    simp [k, Nat.add_comm]]
  rw [hfull]
  apply congrArg σ
  apply Fin.ext
  change k.val = (1 + j.val) % 3
  rw [show k.val = 1 + j.val by simp [k, Nat.add_comm],
    Nat.mod_eq_of_lt (by omega)]

private theorem replaceWindow_three_replaceWindow_two_left
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N) (σ : Cfg d 3)
    (α : Cfg d 2) :
    replaceWindow 3 hN i τ (replaceWindow 2 (by omega) (0 : Fin 3) σ α) =
      replaceWindow 2 (by omega) i (replaceWindow 3 hN i τ σ) α := by
  funext k
  let off := (k.val + N - i.val) % N
  by_cases h3 : off < 3
  · have hoff : off = 0 ∨ off = 1 ∨ off = 2 := by omega
    rcases hoff with hoff | hoff | hoff
    · have hk : (k.val + N - i.val) % N = 0 := by simpa [off] using hoff
      simp [replaceWindow, hk]
    · have hk : (k.val + N - i.val) % N = 1 := by simpa [off] using hoff
      simp [replaceWindow, hk]
    · have hk : (k.val + N - i.val) % N = 2 := by simpa [off] using hoff
      simp [replaceWindow, hk]
  · have h2 : ¬off < 2 := by omega
    simp [replaceWindow, off, h3, h2]

private theorem replaceWindow_three_replaceWindow_two_right
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N) (σ : Cfg d 3)
    (β : Cfg d 2) :
    replaceWindow 3 hN i τ (replaceWindow 2 (by omega) (1 : Fin 3) σ β) =
      replaceWindow 2 (by omega) (cyclicForwardSite i 1)
        (replaceWindow 3 hN i τ σ) β := by
  funext k
  simp only [replaceWindow]
  by_cases hzero : (k.val + N - i.val) % N = 0
  · have hk : k = i := by
      have hk' := eq_cyclic_site_of_offset_eq (Fin.pos i) hzero
      simpa [Nat.mod_eq_of_lt i.isLt] using hk'
    subst k
    have hshift_eq :
        (i.val + N - (cyclicForwardSite i 1).val) % N = N - 1 :=
      cyclicForwardSite_one_offset i
    have hshift : ¬((i.val + N - (cyclicForwardSite i 1).val) % N < 2) := by
      rw [hshift_eq]
      omega
    rw [dite_eq_left (by omega : (i.val + N - i.val) % N < 3), dite_eq_right hshift]
    simp
  · let r := (k.val + N - i.val) % N
    have hrpos : 0 < r := Nat.pos_of_ne_zero hzero
    have hrN : r < N := Nat.mod_lt _ (Fin.pos i)
    have hk_site : k = cyclicForwardSite i r := by
      have hsite := eq_cyclic_site_of_offset_eq (Fin.pos i) (r := r) rfl
      simpa [cyclicForwardSite, r] using hsite
    have hshift_site : k = cyclicForwardSite (cyclicForwardSite i 1) (r - 1) := by
      rw [hk_site, cyclicForwardSite_forwardSite]
      congr 1
      omega
    have hshift_eq :
        (k.val + N - (cyclicForwardSite i 1).val) % N = r - 1 := by
      rw [hshift_site]
      change (((cyclicForwardSite i 1).val + (r - 1)) % N + N -
          (cyclicForwardSite i 1).val) % N = r - 1
      exact offset_mod_eq (cyclicForwardSite i 1).isLt (by omega)
    by_cases hsmall : (k.val + N - i.val) % N < 3
    · have hshiftSmall :
          (k.val + N - (cyclicForwardSite i 1).val) % N < 2 := by
        rw [hshift_eq]
        omega
      rw [dite_eq_left hsmall, dite_eq_left hshiftSmall]
      have hr : r = 1 ∨ r = 2 := by
        change r < 3 at hsmall
        omega
      rcases hr with hr | hr
      · have hout : (k.val + N - i.val) % N = 1 := by simpa [r] using hr
        have hright :
            (k.val + N - (cyclicForwardSite i 1).val) % N = 0 := by
          rw [hshift_eq, hr]
        simp [hout, hright]
      · have hout : (k.val + N - i.val) % N = 2 := by simpa [r] using hr
        have hright :
            (k.val + N - (cyclicForwardSite i 1).val) % N = 1 := by
          rw [hshift_eq, hr]
        simp [hout, hright]
    · have hshiftLarge :
          ¬((k.val + N - (cyclicForwardSite i 1).val) % N < 2) := by
        rw [hshift_eq]
        omega
      rw [dite_eq_right hsmall, dite_eq_right hshiftLarge]
      simp [hsmall]

/-! ### Restriction intertwiners -/

/-- Restriction to the three-site window beginning at (i) intertwines the
length-two term at (i) with the term at site (0) of the three-site chain.

This is the left-face transport for the local relation
\([\tau_1(P_2),P_2]=0\) in arXiv:1606.00608, Definition 3.9, source lines
517--524. -/
theorem cyclicRestrictₗ_three_localTerm_left
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (ψ : NSiteSpace d N) :
    cyclicRestrictₗ (by omega) 3 i τ (localTerm A 2 N i ψ) =
      localTerm A 2 3 (0 : Fin 3) (cyclicRestrictₗ (by omega) 3 i τ ψ) := by
  ext σ
  simp only [cyclicRestrictₗ_apply]
  rw [localTerm_apply_of_le A 2 N (by omega) i]
  rw [localTerm_apply_of_le A 2 3 (by omega) (0 : Fin 3)]
  change parentInteraction A 2
      (fun α => ψ (replaceWindow 2 (by omega) i
        (replaceWindow 3 hN i τ σ) α))
      (extractWindow 2 i (replaceWindow 3 hN i τ σ)) =
    parentInteraction A 2
      (fun α => ψ (replaceWindow 3 hN i τ
        (replaceWindow 2 (by omega) (0 : Fin 3) σ α)))
      (extractWindow 2 (0 : Fin 3) σ)
  rw [extractWindow_two_replaceWindow_three_left]
  have hfun :
      (fun α => ψ (replaceWindow 2 (by omega) i
        (replaceWindow 3 hN i τ σ) α)) =
      fun α => ψ (replaceWindow 3 hN i τ
        (replaceWindow 2 (by omega) (0 : Fin 3) σ α)) := by
    funext α
    rw [replaceWindow_three_replaceWindow_two_left]
  rw [hfun]

/-- Restriction to the three-site window beginning at (i) intertwines the
length-two term at (i+1) with the term at site (1) of the three-site chain.

This is the right-face transport for the local relation
\([\tau_1(P_2),P_2]=0\) in arXiv:1606.00608, Definition 3.9, source lines
517--524. -/
theorem cyclicRestrictₗ_three_localTerm_right
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (ψ : NSiteSpace d N) :
    cyclicRestrictₗ (by omega) 3 i τ
        (localTerm A 2 N (cyclicForwardSite i 1) ψ) =
      localTerm A 2 3 (1 : Fin 3) (cyclicRestrictₗ (by omega) 3 i τ ψ) := by
  ext σ
  simp only [cyclicRestrictₗ_apply]
  rw [localTerm_apply_of_le A 2 N (by omega) (cyclicForwardSite i 1)]
  rw [localTerm_apply_of_le A 2 3 (by omega) (1 : Fin 3)]
  change parentInteraction A 2
      (fun β => ψ (replaceWindow 2 (by omega) (cyclicForwardSite i 1)
        (replaceWindow 3 hN i τ σ) β))
      (extractWindow 2 (cyclicForwardSite i 1) (replaceWindow 3 hN i τ σ)) =
    parentInteraction A 2
      (fun β => ψ (replaceWindow 3 hN i τ
        (replaceWindow 2 (by omega) (1 : Fin 3) σ β)))
      (extractWindow 2 (1 : Fin 3) σ)
  rw [extractWindow_two_replaceWindow_three_right]
  have hfun :
      (fun β => ψ (replaceWindow 2 (by omega) (cyclicForwardSite i 1)
        (replaceWindow 3 hN i τ σ) β)) =
      fun β => ψ (replaceWindow 3 hN i τ
        (replaceWindow 2 (by omega) (1 : Fin 3) σ β)) := by
    funext β
    rw [replaceWindow_three_replaceWindow_two_right]
  rw [hfun]

private theorem cyclicRestrictₗ_three_extractWindow
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (σ : Cfg d N) (ψ : NSiteSpace d N) :
    cyclicRestrictₗ (by omega) 3 i σ ψ (extractWindow 3 i σ) = ψ σ := by
  change ψ (replaceWindow 3 hN i σ (extractWindow 3 i σ)) = ψ σ
  rw [replaceWindow_extractWindow]

/-! ### Transport of three-site quadratic forms -/

/-- Split an \(N\)-site configuration into the cyclic three-site window
starting at \(i\) and its ordered complement.  The first coordinates occur at
cyclic offsets \(0,1,2\) from \(i\); the complementary coordinates then occur
at offsets \(3,4,\ldots,N-1\), in that order. -/
private def cyclicWindowCfgEquiv {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    Cfg d 3 × Cfg d (N - 3) ≃ Cfg d N :=
  (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin (N - 3)) (Fin d)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d) (cyclicWindowIndexEquiv 3 N hN i))

@[simp] private theorem cyclicWindowCfgEquiv_apply_window {N : ℕ} (hN : 3 ≤ N)
    (i : Fin N) (σ : Cfg d 3) (τ : Cfg d (N - 3)) (r : Fin 3) :
    cyclicWindowCfgEquiv hN i (σ, τ) (cyclicForwardSite i r.val) = σ r := by
  change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d) (cyclicWindowIndexEquiv 3 N hN i)
    ((Equiv.sumArrowEquivProdArrow (Fin 3) (Fin (N - 3)) (Fin d)).symm (σ, τ))
    (cyclicWindowIndexEquiv 3 N hN i (Sum.inl r)) = σ r
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private theorem cyclicCfg_cyclicWindowCfgEquiv {N : ℕ} (hN : 3 ≤ N) [NeZero d]
    (i : Fin N) (σ : Cfg d 3) (τ : Cfg d (N - 3)) :
    cyclicCfg (by omega) 3 i σ (cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ)) =
      cyclicWindowCfgEquiv hN i (σ, τ) := by
  funext k
  simp only [cyclicCfg]
  by_cases hk : (k.val + N - i.val) % N < 3
  · rw [dite_eq_left hk]
    let r : Fin 3 := ⟨(k.val + N - i.val) % N, hk⟩
    have hki : k = cyclicForwardSite i r.val := by
      simpa [cyclicForwardSite, r] using
        eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k) (r := r.val) rfl
    have hleft : σ ⟨(k.val + N - i.val) % N, hk⟩ = σ r := rfl
    rw [hleft]
    rw [hki]
    exact cyclicWindowCfgEquiv_apply_window hN i σ τ r |>.symm
  · rw [dite_eq_right hk]
    let x := (cyclicWindowIndexEquiv 3 N hN i).symm k
    have hkx : cyclicWindowIndexEquiv 3 N hN i x = k := by simp [x]
    rcases x with r | r
    · exfalso
      apply hk
      rw [← hkx]
      change ((cyclicForwardSite i r.val).val + N - i.val) % N < 3
      rw [show ((cyclicForwardSite i r.val).val + N - i.val) % N = r.val by
        simpa [cyclicForwardSite] using
          offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hN)]
      exact r.isLt
    · change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
          (cyclicWindowIndexEquiv 3 N hN i)
          ((Equiv.sumArrowEquivProdArrow (Fin 3) (Fin (N - 3)) (Fin d)).symm
            (fun _ ↦ 0, τ)) k =
        Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
          (cyclicWindowIndexEquiv 3 N hN i)
          ((Equiv.sumArrowEquivProdArrow (Fin 3) (Fin (N - 3)) (Fin d)).symm
            (σ, τ)) k
      rw [← hkx, Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      rfl

private theorem re_inner_eq_sum_cyclicRestrict_three {N : ℕ} (hN : 3 ≤ N)
    [NeZero d] (i : Fin N) (u v : EuclideanSpace ℂ (Cfg d N)) :
    (⟪u, v⟫_ℂ).re =
      ∑ τ : Cfg d (N - 3),
        (⟪LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i
              (cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ))) u,
            LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i
              (cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ))) v⟫_ℂ).re := by
  rw [PiLp.inner_apply]
  trans (∑ p : Cfg d 3 × Cfg d (N - 3),
    inner ℂ (u.ofLp (cyclicWindowCfgEquiv hN i p))
      (v.ofLp (cyclicWindowCfgEquiv hN i p))).re
  · congr 1
    symm
    apply Fintype.sum_equiv (cyclicWindowCfgEquiv hN i)
    intro p
    rfl
  · simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    change Complex.reCLM (∑ y, ∑ x,
      inner ℂ (u.ofLp (cyclicWindowCfgEquiv hN i (x, y)))
        (v.ofLp (cyclicWindowCfgEquiv hN i (x, y)))) = _
    rw [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro τ _
    rw [PiLp.inner_apply]
    change Complex.reCLM (∑ x, _) = Complex.reCLM (∑ x, _)
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    apply congrArg₂ (inner ℂ)
    · change u.ofLp (cyclicWindowCfgEquiv hN i (σ, τ)) =
        u.ofLp (cyclicCfg (by omega) 3 i σ
          (cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ)))
      rw [cyclicCfg_cyclicWindowCfgEquiv]
    · change v.ofLp (cyclicWindowCfgEquiv hN i (σ, τ)) =
        v.ofLp (cyclicCfg (by omega) 3 i σ
          (cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ)))
      rw [cyclicCfg_cyclicWindowCfgEquiv]

private theorem cyclicRestrictES_three_localTerm_left
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i τ)
        (localTermES A 2 i v) =
      localTermES A 2 (0 : Fin 3)
        (LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i τ) v) := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  let e3 := WithLp.linearEquiv 2 ℂ (NSiteSpace d 3)
  apply e3.injective
  simpa [localTermES, eN, e3, LinearMap.withLpMap] using
    cyclicRestrictₗ_three_localTerm_left (A := A) hN i τ (eN v)

private theorem cyclicRestrictES_three_localTerm_right
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i τ)
        (localTermES A 2 (cyclicForwardSite i 1) v) =
      localTermES A 2 (1 : Fin 3)
        (LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i τ) v) := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  let e3 := WithLp.linearEquiv 2 ℂ (NSiteSpace d 3)
  apply e3.injective
  simpa [localTermES, eN, e3, LinearMap.withLpMap] using
    cyclicRestrictₗ_three_localTerm_right (A := A) hN i τ (eN v)

/-- A three-site anticommutator quadratic-form estimate for the adjacent
range-two terms transports to every forward adjacent pair on a periodic chain
with \(3 \leq N\), with the same coefficient.

The restriction begins at the arbitrary site \(i\), so it also covers the two
forward pairs whose three-site window crosses the periodic cut.  This is the
source form \(h_i h_j + h_j h_i \geq -c(h_i+h_j)\) from
arXiv:2011.12127, Section IV.C, lines 2170--2180. -/
theorem re_inner_localTermES_adjacent_twoSite_forward_ge_of_threeSite
    [NeZero d] {A : MPSTensor d D} {c : ℝ}
    (h₃ : ∀ w : EuclideanSpace ℂ (Cfg d 3),
      -c * ((⟪localTermES A 2 (0 : Fin 3) w, w⟫_ℂ).re +
          (⟪localTermES A 2 (1 : Fin 3) w, w⟫_ℂ).re) ≤
        (⟪localTermES A 2 (0 : Fin 3) w,
            localTermES A 2 (1 : Fin 3) w⟫_ℂ).re +
          (⟪localTermES A 2 (1 : Fin 3) w,
            localTermES A 2 (0 : Fin 3) w⟫_ℂ).re)
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    -c * ((⟪localTermES A 2 i v, v⟫_ℂ).re +
        (⟪localTermES A 2 (cyclicForwardSite i 1) v, v⟫_ℂ).re) ≤
      (⟪localTermES A 2 i v,
          localTermES A 2 (cyclicForwardSite i 1) v⟫_ℂ).re +
        (⟪localTermES A 2 (cyclicForwardSite i 1) v,
          localTermES A 2 i v⟫_ℂ).re := by
  simp_rw [re_inner_eq_sum_cyclicRestrict_three hN i]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change -c * (∑ τ, _) ≤ ∑ τ, _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  let outside := cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ)
  let w := LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) (by omega) 3 i outside) v
  have hleft := cyclicRestrictES_three_localTerm_left (A := A) hN i outside v
  have hright := cyclicRestrictES_three_localTerm_right (A := A) hN i outside v
  rw [hleft, hright]
  exact h₃ w

private theorem cyclicForwardSite_backwardSite_one {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    cyclicForwardSite (cyclicBackwardSite i 1) 1 = i := by
  apply Fin.ext
  simp only [cyclicForwardSite, cyclicBackwardSite, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (by omega : 1 < N)]
  by_cases hi : 0 < i.val
  · have hback : (i.val + N - 1) % N = i.val - 1 := by
      rw [show i.val + N - 1 = (i.val - 1) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hback, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
  · have hi0 : i.val = 0 := by omega
    rw [hi0]
    simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    rw [show N - 1 + 1 = N by omega, Nat.mod_self]

/-- The same three-site anticommutator estimate transports to every backward
adjacent pair on a periodic chain with \(3 \leq N\), with unchanged coefficient.

The proof starts the forward three-site window at the cyclic predecessor of
\(i\); when \(i = 0\), this is explicitly the wrapping pair between sites
\(0\) and \(N-1\). -/
theorem re_inner_localTermES_adjacent_twoSite_backward_ge_of_threeSite
    [NeZero d] {A : MPSTensor d D} {c : ℝ}
    (h₃ : ∀ w : EuclideanSpace ℂ (Cfg d 3),
      -c * ((⟪localTermES A 2 (0 : Fin 3) w, w⟫_ℂ).re +
          (⟪localTermES A 2 (1 : Fin 3) w, w⟫_ℂ).re) ≤
        (⟪localTermES A 2 (0 : Fin 3) w,
            localTermES A 2 (1 : Fin 3) w⟫_ℂ).re +
          (⟪localTermES A 2 (1 : Fin 3) w,
            localTermES A 2 (0 : Fin 3) w⟫_ℂ).re)
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    -c * ((⟪localTermES A 2 i v, v⟫_ℂ).re +
        (⟪localTermES A 2 (cyclicBackwardSite i 1) v, v⟫_ℂ).re) ≤
      (⟪localTermES A 2 i v,
          localTermES A 2 (cyclicBackwardSite i 1) v⟫_ℂ).re +
        (⟪localTermES A 2 (cyclicBackwardSite i 1) v,
          localTermES A 2 i v⟫_ℂ).re := by
  let j := cyclicBackwardSite i 1
  have hj : cyclicForwardSite j 1 = i := cyclicForwardSite_backwardSite_one (by omega) i
  have h := re_inner_localTermES_adjacent_twoSite_forward_ge_of_threeSite
    h₃ hN j v
  rw [hj] at h
  simpa [j, add_comm] using h


/-! ### Transport of the commutator -/

/-- Commutation of the two adjacent length-two parent interactions on the
three-site chain implies commutation of every adjacent translated pair on every
periodic chain of length (N>2).

This is the finite-chain transport of the source relation
\([\tau_1(P_2),P_2]=0\) from arXiv:1606.00608, Definition 3.9, source lines
517--524.  The bound (3\leq N) is exactly the (N>2) range in Theorem 3.10,
source lines 534--540.  No assertion is made for (N=2), where the two cyclic
windows traverse the same pair of sites in opposite orders. -/
theorem localTerm_adjacent_twoSite_commute_of_threeSite_zero_one_commute
    {A : MPSTensor d D}
    (h₃ :
      localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
        localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3))
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    localTerm A 2 N i * localTerm A 2 N (cyclicForwardSite i 1) =
      localTerm A 2 N (cyclicForwardSite i 1) * localTerm A 2 N i := by
  apply LinearMap.ext
  intro ψ
  funext σ
  have hcomm := LinearMap.congr_fun h₃ (cyclicRestrictₗ (by omega) 3 i σ ψ)
  simp only [Module.End.mul_apply] at hcomm
  rw [← cyclicRestrictₗ_three_localTerm_right hN i σ ψ,
    ← cyclicRestrictₗ_three_localTerm_left hN i σ
      (localTerm A 2 N (cyclicForwardSite i 1) ψ)] at hcomm
  rw [← cyclicRestrictₗ_three_localTerm_left hN i σ ψ,
    ← cyclicRestrictₗ_three_localTerm_right hN i σ (localTerm A 2 N i ψ)] at hcomm
  have hvalue := congrFun hcomm (extractWindow 3 i σ)
  rw [cyclicRestrictₗ_three_extractWindow hN i σ,
    cyclicRestrictₗ_three_extractWindow hN i σ] at hvalue
  simpa only [Module.End.mul_apply] using hvalue

end MPSTensor
