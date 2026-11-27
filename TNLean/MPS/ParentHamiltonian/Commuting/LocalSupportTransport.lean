/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.ParentHamiltonian.Commuting.LocalSupport
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CyclicRestrictionNorm
import TNLean.MPS.Tensor.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport

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

* `adjacent_parentRingInteraction_term_eq_zero_iff_mem_groundSpace_succ` characterizes the
  \((L+1)\)-site ground space by the two adjacent length-\(L\) kernels.
* `groundSpace_three_eq_adjacent_twoSite_parent_kernels` gives the three-site
  specialization for the canonical two-site parent interaction.
* `re_inner_parentRingInteraction_term_adjacent_twoSite_forward_ge_of_threeSite` and
  `re_inner_parentRingInteraction_term_adjacent_twoSite_backward_ge_of_threeSite` transport a
  three-site anticommutator quadratic-form estimate to every cyclic adjacent pair.
* `parentRingInteraction_term_adjacent_twoSite_commute_of_threeSite_zero_one_commute` transports
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
theorem adjacent_parentRingInteraction_term_eq_zero_iff_mem_groundSpace_succ
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : NSiteSpace d (L + 1)} :
    Matrix.toLin' ((parentRingInteraction A L (L + 1)).term (0 : Fin (L + 1))) v = 0 ∧
        Matrix.toLin' ((parentRingInteraction A L (L + 1)).term (1 : Fin (L + 1))) v = 0 ↔
      v ∈ groundSpace A (L + 1) := by
  have h := parentRingInteraction_term_zero_one_eq_zero_iff_mem_map_groundSpace_succ
    hA hL (v := WithLp.toLp 2 v)
  rw [mem_map_groundSpace_iff, Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    WithLp.toLp_eq_zero] at h
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h

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
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) :
    groundSpace A 3 =
      LinearMap.ker (leftPairLift (parentInteraction A 2)) ⊓
        LinearMap.ker (rightPairLift (parentInteraction A 2)) := by
  ext v
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
  rw [← term_two_three_zero_eq_leftPairLift_parentInteraction]
  rw [← term_two_three_one_eq_rightPairLift_parentInteraction]
  exact (adjacent_parentRingInteraction_term_eq_zero_iff_mem_groundSpace_succ
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
theorem cyclicRestrictₗ_three_parentRingInteraction_term_left
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (ψ : NSiteSpace d N) :
    haveI : NeZero N := ⟨by omega⟩;
    cyclicRestrictₗ (by omega) 3 i τ (Matrix.toLin' ((parentRingInteraction A 2 N).term i) ψ) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3))
        (cyclicRestrictₗ (by omega) 3 i τ ψ) := by
  have : NeZero N := ⟨by omega⟩
  ext σ
  simp only [cyclicRestrictₗ_apply]
  rw [Matrix.toLin'_apply, parentRingInteraction_term_mulVec_apply_of_le A 2 N (by omega) i]
  rw [Matrix.toLin'_apply,
    parentRingInteraction_term_mulVec_apply_of_le A 2 3 (by omega) (0 : Fin 3)]
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
theorem cyclicRestrictₗ_three_parentRingInteraction_term_right
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (ψ : NSiteSpace d N) :
    haveI : NeZero N := ⟨by omega⟩;
    cyclicRestrictₗ (by omega) 3 i τ
        (Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) ψ) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3))
        (cyclicRestrictₗ (by omega) 3 i τ ψ) := by
  have : NeZero N := ⟨by omega⟩
  ext σ
  simp only [cyclicRestrictₗ_apply]
  rw [Matrix.toLin'_apply,
    parentRingInteraction_term_mulVec_apply_of_le A 2 N (by omega) (cyclicForwardSite i 1)]
  rw [Matrix.toLin'_apply,
    parentRingInteraction_term_mulVec_apply_of_le A 2 3 (by omega) (1 : Fin 3)]
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

private theorem cyclicForwardSite_backwardSite_one {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    cyclicForwardSite (cyclicBackwardSite i 1) 1 = i := by
  apply Fin.ext
  simp only [cyclicForwardSite, cyclicBackwardSite, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (by omega : 1 < N), Nat.mod_add_mod,
    show i.val + N - 1 + 1 = i.val + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-! ### Transport of the commutator -/

/-- Commutation of the two adjacent length-two parent interactions on the
three-site chain implies commutation of every adjacent translated pair on every
periodic chain of length (N>2).

This is the finite-chain transport of the source relation
\([\tau_1(P_2),P_2]=0\) from arXiv:1606.00608, Definition 3.9, source lines
517--524.  The bound (3\leq N) is exactly the (N>2) range in Theorem 3.10,
source lines 534--540.  No assertion is made for (N=2), where the two cyclic
windows traverse the same pair of sites in opposite orders. -/
theorem parentRingInteraction_term_adjacent_twoSite_commute_of_threeSite_zero_one_commute
    {A : MPSTensor d D}
    (h₃ :
      Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
            Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)))
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toLin' ((parentRingInteraction A 2 N).term i) *
        Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) =
      Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) *
          Matrix.toLin' ((parentRingInteraction A 2 N).term i) := by
  have : NeZero N := ⟨by omega⟩
  apply LinearMap.ext
  intro ψ
  funext σ
  have hcomm := LinearMap.congr_fun h₃ (cyclicRestrictₗ (by omega) 3 i σ ψ)
  simp only [Module.End.mul_apply] at hcomm
  rw [← cyclicRestrictₗ_three_parentRingInteraction_term_right hN i σ ψ,
    ← cyclicRestrictₗ_three_parentRingInteraction_term_left hN i σ
      (Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) ψ)] at hcomm
  rw [← cyclicRestrictₗ_three_parentRingInteraction_term_left hN i σ ψ,
    ← cyclicRestrictₗ_three_parentRingInteraction_term_right hN i σ
      (Matrix.toLin' ((parentRingInteraction A 2 N).term i) ψ)] at hcomm
  have hvalue := congrFun hcomm (extractWindow 3 i σ)
  rw [cyclicRestrictₗ_three_extractWindow hN i σ,
    cyclicRestrictₗ_three_extractWindow hN i σ] at hvalue
  simpa only [Module.End.mul_apply] using hvalue

/-! ### The parent interaction on the ring -/

private theorem withLpMap_cyclicRestrictₗ_three_parentRingInteraction_term_left
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) 3 i τ)
        (Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v) =
      Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 0)
        (LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) 3 i τ) v) := by
  have : NeZero N := ⟨by omega⟩
  have h :=
    cyclicRestrictₗ_three_parentRingInteraction_term_left (A := A) hN i τ (WithLp.ofLp v)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  simpa [LinearMap.withLpMap, Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) h

private theorem withLpMap_cyclicRestrictₗ_three_parentRingInteraction_term_right
    {A : MPSTensor d D} {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) 3 i τ)
        (Matrix.toEuclideanLin
          ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) v) =
      Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 1)
        (LinearMap.withLpMap 2 (cyclicRestrictₗ (by omega) 3 i τ) v) := by
  have : NeZero N := ⟨by omega⟩
  have h :=
    cyclicRestrictₗ_three_parentRingInteraction_term_right (A := A) hN i τ (WithLp.ofLp v)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  simpa [LinearMap.withLpMap, Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) h

/-- A three-site anticommutator quadratic-form estimate for the adjacent range-two terms of the
parent interaction on the ring transports to every forward adjacent pair on a periodic chain
with \(3 \leq N\), with the same coefficient.

The restriction begins at the arbitrary site \(i\), so it also covers the two forward pairs
whose three-site window crosses the periodic cut. This is the source form
\(h_i h_j + h_j h_i \geq -c(h_i+h_j)\) from arXiv:2011.12127, Section IV.C,
lines 2170--2180. -/
theorem re_inner_parentRingInteraction_term_adjacent_twoSite_forward_ge_of_threeSite
    [NeZero d] {A : MPSTensor d D} {c : ℝ}
    (h₃ : ∀ w : EuclideanSpace ℂ (Cfg d 3),
      -c * ((⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 0) w,
            w⟫_ℂ).re +
          (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 1) w,
            w⟫_ℂ).re) ≤
        (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 0) w,
            Matrix.toEuclideanLin
              ((parentRingInteraction A 2 3).term 1) w⟫_ℂ).re +
          (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 1) w,
            Matrix.toEuclideanLin
              ((parentRingInteraction A 2 3).term 0) w⟫_ℂ).re)
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    -c * ((⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v,
          v⟫_ℂ).re +
        (⟪Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) v,
          v⟫_ℂ).re) ≤
      (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v,
          Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) v⟫_ℂ).re +
        (⟪Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) v,
          Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v⟫_ℂ).re := by
  have : NeZero N := ⟨by omega⟩
  simp_rw [re_inner_eq_sum_cyclicRestrict_three hN i]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change -c * (∑ τ, _) ≤ ∑ τ, _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  let outside := cyclicWindowCfgEquiv hN i ((fun _ ↦ 0), τ)
  rw [withLpMap_cyclicRestrictₗ_three_parentRingInteraction_term_left hN i outside v,
    withLpMap_cyclicRestrictₗ_three_parentRingInteraction_term_right hN i outside v]
  exact h₃ _

/-- The same three-site anticommutator estimate transports to every backward adjacent pair of
terms of the parent interaction on a periodic chain with \(3 \leq N\), with unchanged
coefficient. The proof starts the forward three-site window at the cyclic predecessor of
\(i\); when \(i = 0\), this is the wrapping pair between sites \(0\) and \(N-1\). Source:
arXiv:2011.12127, Section IV.C, lines 2170--2180. -/
theorem re_inner_parentRingInteraction_term_adjacent_twoSite_backward_ge_of_threeSite
    [NeZero d] {A : MPSTensor d D} {c : ℝ}
    (h₃ : ∀ w : EuclideanSpace ℂ (Cfg d 3),
      -c * ((⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 0) w,
            w⟫_ℂ).re +
          (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 1) w,
            w⟫_ℂ).re) ≤
        (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 0) w,
            Matrix.toEuclideanLin
              ((parentRingInteraction A 2 3).term 1) w⟫_ℂ).re +
          (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 3).term 1) w,
            Matrix.toEuclideanLin
              ((parentRingInteraction A 2 3).term 0) w⟫_ℂ).re)
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    -c * ((⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v,
          v⟫_ℂ).re +
        (⟪Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicBackwardSite i 1)) v,
          v⟫_ℂ).re) ≤
      (⟪Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v,
          Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicBackwardSite i 1)) v⟫_ℂ).re +
        (⟪Matrix.toEuclideanLin
            ((parentRingInteraction A 2 N).term (cyclicBackwardSite i 1)) v,
          Matrix.toEuclideanLin ((parentRingInteraction A 2 N).term i) v⟫_ℂ).re := by
  have : NeZero N := ⟨by omega⟩
  let j := cyclicBackwardSite i 1
  have hj : cyclicForwardSite j 1 = i := cyclicForwardSite_backwardSite_one (by omega) i
  have h := re_inner_parentRingInteraction_term_adjacent_twoSite_forward_ge_of_threeSite
    h₃ hN j v
  rw [hj] at h
  exact le_of_eq_of_le (by ring) (h.trans_eq (by ring))

end MPSTensor
