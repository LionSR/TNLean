/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.FiniteRangeKnabe
import TNLean.MPS.ParentHamiltonian.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Cyclic windows as open parent Hamiltonians

This file identifies a finite cyclic block of periodic parent-Hamiltonian terms
with the corresponding open-chain Hamiltonian on its active sites.  If the
periodic interaction range is \(R\) and the block contains \(m\) local terms, the
active interval has exactly \(W = m + R - 1\) sites.

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

/-- Reindexing periodic local terms by \(\mathbb Z/N\mathbb Z\) preserves their total sum. -/
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

/-- Addition in \(\mathbb Z/N\mathbb Z\) is cyclic forward motion on the
corresponding finite site. -/
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

/-- Two range-\(R\) cyclic windows are disjoint when their oriented start
separation \(e\) satisfies \(R \leq e\) and \(e + R \leq N\). -/
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

/-- Split a periodic configuration into a cyclic active block of length \(W\) and
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

/-- The cyclic active-block isometry evaluates by joining the active and
spectator configurations in cyclic order. -/
@[simp] theorem cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply {N W : ℕ}
    (hWN : W ≤ N) (s : Fin N) (v : EuclideanSpace ℂ (Cfg d N))
    (p : Cfg d W × Cfg d (N - W)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s v p =
      v ((cyclicActiveBlockConfigEquiv d W hWN s).symm p) := by
  rw [cyclicActiveBlockConfigLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- The inverse cyclic active-block isometry evaluates through the block split. -/
@[simp] theorem cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply
    {N W : ℕ} (hWN : W ≤ N) (s : Fin N)
    (v : EuclideanSpace ℂ (Cfg d W × Cfg d (N - W))) (σ : Cfg d N) :
    (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm v σ =
      v (cyclicActiveBlockConfigEquiv d W hWN s σ) := by
  rw [cyclicActiveBlockConfigLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- The complementary coordinates of the cyclic block occur after all active
coordinates in cyclic order. -/
@[simp] theorem cyclicActiveBlockConfigEquiv_symm_apply_spectator {N W : ℕ}
    (hWN : W ≤ N) (s : Fin N) (σ : Cfg d W) (τ : Cfg d (N - W))
    (r : Fin (N - W)) :
    (cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)
        (cyclicForwardSite s (W + r.val)) = τ r := by
  change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
      (cyclicWindowIndexEquiv W N hWN s)
      ((Equiv.sumArrowEquivProdArrow (Fin W) (Fin (N - W)) (Fin d)).symm
        (σ, τ))
      (cyclicWindowIndexEquiv W N hWN s (Sum.inr r)) = τ r
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private theorem cyclicCfg_join_cyclicActiveBlock {N W R : ℕ}
    (hWN : W ≤ N) (s : Fin N) (q : Fin W)
    (hqR : q.val + R ≤ W) (ω : Cfg d R) (σ : Cfg d W)
    (τ : Cfg d (N - W)) :
    cyclicCfg (Fin.pos s) R (cyclicForwardSite s q.val) ω
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) =
      (cyclicActiveBlockConfigEquiv d W hWN s).symm
        (cyclicCfg (Fin.pos q) R q ω σ, τ) := by
  funext k
  let x := (cyclicWindowIndexEquiv W N hWN s).symm k
  have hkx : cyclicWindowIndexEquiv W N hWN s x = k := by simp [x]
  rcases x with r | r
  · rw [← hkx, cyclicWindowIndexEquiv_inl]
    change cyclicCfg (Fin.pos s) R (cyclicForwardSite s q.val) ω
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))
          (cyclicForwardSite s r.val) =
      (cyclicActiveBlockConfigEquiv d W hWN s).symm
        (cyclicCfg (Fin.pos q) R q ω σ, τ) (cyclicForwardSite s r.val)
    rw [cyclicActiveBlockConfigEquiv_symm_apply_window]
    simp only [cyclicCfg]
    by_cases hr : q.val ≤ r.val ∧ r.val < q.val + R
    · have hglobalOffset :
          ((cyclicForwardSite s r.val).val + N -
            (cyclicForwardSite s q.val).val) % N = r.val - q.val := by
          rw [show cyclicForwardSite s r.val =
              cyclicForwardSite (cyclicForwardSite s q.val) (r.val - q.val) by
            rw [cyclicForwardSite_forwardSite]
            congr 1
            omega]
          simpa [cyclicForwardSite] using
            offset_mod_eq (cyclicForwardSite s q.val).isLt (by omega : r.val - q.val < N)
      have hactiveOffset : (r.val + W - q.val) % W = r.val - q.val := by
        have hsum : r.val + W - q.val = r.val - q.val + W := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r.val - q.val < W)]
      rw [dite_eq_left (by rw [hglobalOffset]; omega),
        dite_eq_left (by rw [hactiveOffset]; omega)]
      congr 1
      apply Fin.ext
      exact hglobalOffset.trans hactiveOffset.symm
    · have hglobalNot : ¬((cyclicForwardSite s r.val).val + N -
          (cyclicForwardSite s q.val).val) % N < R := by
        intro hoff
        by_cases hqr : q.val ≤ r.val
        · have hglobalOffset :
              ((cyclicForwardSite s r.val).val + N -
                (cyclicForwardSite s q.val).val) % N = r.val - q.val := by
              rw [show cyclicForwardSite s r.val =
                  cyclicForwardSite (cyclicForwardSite s q.val) (r.val - q.val) by
                rw [cyclicForwardSite_forwardSite]
                congr 1
                omega]
              simpa [cyclicForwardSite] using
                offset_mod_eq (cyclicForwardSite s q.val).isLt
                  (by omega : r.val - q.val < N)
          rw [hglobalOffset] at hoff
          exact hr ⟨hqr, by omega⟩
        · have hback : N - (q.val - r.val) < R := by
            have hEq : cyclicForwardSite s r.val =
                cyclicForwardSite (cyclicForwardSite s q.val)
                  (N - (q.val - r.val)) := by
              rw [cyclicForwardSite_forwardSite]
              apply Fin.ext
              simp only [cyclicForwardSite, Fin.val_mk]
              have hqN : q.val < N := by omega
              have hrN : r.val < N := by omega
              have hsum : q.val + (N - (q.val - r.val)) = r.val + N := by omega
              rw [hsum]
              simpa [Nat.add_assoc] using
                (Nat.add_mod_right (s.val + r.val) N).symm
            have hOffset :
                ((cyclicForwardSite s r.val).val + N -
                  (cyclicForwardSite s q.val).val) % N = N - (q.val - r.val) := by
              rw [hEq]
              simpa [cyclicForwardSite] using
                offset_mod_eq (cyclicForwardSite s q.val).isLt
                  (by omega : N - (q.val - r.val) < N)
            rwa [hOffset] at hoff
          omega
      have hactiveNot : ¬(r.val + W - q.val) % W < R := by
        intro hoff
        by_cases hqr : q.val ≤ r.val
        · have hsum : r.val + W - q.val = r.val - q.val + W := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r.val - q.val < W)] at hoff
          exact hr ⟨hqr, by omega⟩
        · have hlt : r.val + W - q.val < W := by omega
          rw [Nat.mod_eq_of_lt hlt] at hoff
          omega
      rw [dite_eq_right hglobalNot, dite_eq_right hactiveNot]
      exact cyclicActiveBlockConfigEquiv_symm_apply_window hWN s σ τ r
  · rw [← hkx, cyclicWindowIndexEquiv_inr]
    have hsite :
        (⟨(s.val + W + r.val) % N, Nat.mod_lt _ (Fin.pos s)⟩ : Fin N) =
          cyclicForwardSite s (W + r.val) := by
      apply Fin.ext
      simp only [cyclicForwardSite, Fin.val_mk]
      congr 1
      omega
    rw [hsite]
    change cyclicCfg (Fin.pos s) R (cyclicForwardSite s q.val) ω
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))
          (cyclicForwardSite s (W + r.val)) =
      (cyclicActiveBlockConfigEquiv d W hWN s).symm
        (cyclicCfg (Fin.pos q) R q ω σ, τ)
          (cyclicForwardSite s (W + r.val))
    rw [cyclicActiveBlockConfigEquiv_symm_apply_spectator]
    simp only [cyclicCfg]
    have hnot : ¬((cyclicForwardSite s (W + r.val)).val + N -
        (cyclicForwardSite s q.val).val) % N < R := by
      intro hoff
      have hdist : W + r.val - q.val < N := by omega
      have hEq : cyclicForwardSite s (W + r.val) =
          cyclicForwardSite (cyclicForwardSite s q.val) (W + r.val - q.val) := by
        rw [cyclicForwardSite_forwardSite]
        congr 1
        omega
      have hOffset :
          ((cyclicForwardSite s (W + r.val)).val + N -
            (cyclicForwardSite s q.val).val) % N = W + r.val - q.val := by
        rw [hEq]
        simpa [cyclicForwardSite] using
          offset_mod_eq (cyclicForwardSite s q.val).isLt hdist
      rw [hOffset] at hoff
      omega
    rw [dite_eq_right hnot]
    exact cyclicActiveBlockConfigEquiv_symm_apply_spectator hWN s σ τ r

private theorem extractWindow_join_cyclicActiveBlock {N W R : ℕ}
    (hWN : W ≤ N) (s : Fin N) (q : Fin W) (hqR : q.val + R ≤ W)
    (σ : Cfg d W) (τ : Cfg d (N - W)) :
    extractWindow R (cyclicForwardSite s q.val)
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) =
      extractWindow R q σ := by
  funext r
  have hqrW : q.val + r.val < W := by omega
  have hqrN : q.val + r.val < N := by omega
  have hsite :
      cyclicForwardSite (cyclicForwardSite s q.val) r.val =
        cyclicForwardSite s (q.val + r.val) :=
    cyclicForwardSite_forwardSite s q.val r.val
  change (cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)
      (cyclicForwardSite (cyclicForwardSite s q.val) r.val) =
    σ ⟨(q.val + r.val) % W, Nat.mod_lt _ (Fin.pos q)⟩
  rw [hsite, cyclicActiveBlockConfigEquiv_symm_apply_window hWN s σ τ
    ⟨q.val + r.val, hqrW⟩]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt hqrW]

/-- A periodic range-\(R\) local term inside a cyclic active block becomes the
corresponding nonwrapping local term on the active sites, independently on each
spectator configuration. -/
theorem localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv
    {N W R : ℕ} (A : MPSTensor d D) (hWN : W ≤ N) (s : Fin N)
    (q : Fin W) (hqR : q.val + R ≤ W) :
    (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).toLinearEquiv.toLinearMap.comp
        ((localTermES A R (cyclicForwardSite s q.val)).comp
          (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (localTermES A R q))).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  simp only [LinearMap.comp_apply]
  change localTermES A R (cyclicForwardSite s q.val)
      ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x)
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) =
    localTermES A R q (ContinuousLinearMap.rightFiber x τ) σ
  rw [localTermES_apply A R (cyclicForwardSite s q.val) (by omega),
    localTermES_apply A R q (by omega)]
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val)
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))
          ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x) =
        cyclicRestrictES (d := d) (Fin.pos q) R q σ
          (ContinuousLinearMap.rightFiber x τ) := by
    apply PiLp.ext
    intro ω
    change (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x
        (cyclicCfg (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val) ω
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))) =
      x (cyclicCfg (Fin.pos q) R q ω σ, τ)
    rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply,
      cyclicCfg_join_cyclicActiveBlock hWN s q hqR]
    simp
  rw [hrestrict,
    extractWindow_join_cyclicActiveBlock hWN s q hqR σ τ]

private def cyclicBlockStartEquiv {R m : ℕ} (hR : 1 ≤ R) :
    Fin m ≃ NonwrappingStart R (m + R - 1) where
  toFun q := by
    have hq := q.isLt
    let j : Fin (m + R - 1) := ⟨q.val, by omega⟩
    refine ⟨j, ?_⟩
    change q.val + R ≤ m + R - 1
    omega
  invFun i := ⟨i.1.val, by
    have hi := i.2
    omega⟩
  left_inv q := by
    apply Fin.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- A Knabe block of \(m\) consecutive range-\(R\) periodic terms is the
fiberwise open parent Hamiltonian on exactly \(m + R - 1\) active sites.

The assumptions \(1 \leq R\), \(R \leq m\), and \(2m \leq N\) ensure that the active
interval fits inside the periodic chain and contains every one of the \(m\)
nonwrapping interaction windows. -/
theorem cyclicWindowSum_zmodLocalTermES_conj_cyclicActiveBlock
    {N R m : ℕ} [NeZero N] (A : MPSTensor d D)
    (hR : 1 ≤ R) (hmR : R ≤ m) (hN : 2 * m ≤ N) (s : ZMod N) :
    let W := m + R - 1
    let i := (ZMod.finEquiv N).symm s
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega) i
    U.toLinearEquiv.toLinearMap.comp
        ((ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s).comp
          U.symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap
          (openParentHamiltonianES A R W))).toLinearMap := by
  classical
  dsimp only
  let i := (ZMod.finEquiv N).symm s
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d (m + R - 1) (by omega) i
  apply LinearMap.ext
  intro x
  simp only [ProjectionGeometry.cyclicWindowSum, openParentHamiltonianES,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    ContinuousLinearMap.rightFiberwiseMap_sum]
  calc
    (∑ q : Fin m,
        U (zmodLocalTermES A R (s + (q.val : ZMod N)) (U.symm x))) =
      ∑ q : Fin m,
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap
            (localTermES A R (cyclicBlockStartEquiv hR q).1)) x := by
        apply Finset.sum_congr rfl
        intro q _
        have hstart : (ZMod.finEquiv N).symm (s + (q.val : ZMod N)) =
            cyclicForwardSite i q.val := by
          simpa [i] using finEquiv_symm_add_eq_cyclicForwardSite s q.val
        change U (localTermES A R ((ZMod.finEquiv N).symm
            (s + (q.val : ZMod N))) (U.symm x)) = _
        rw [hstart]
        exact LinearMap.congr_fun
          (localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv A
            (by omega) i (cyclicBlockStartEquiv hR q).1
            (cyclicBlockStartEquiv hR q).2) x
    _ = ∑ q : NonwrappingStart R (m + R - 1),
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap (localTermES A R q.1)) x := by
      exact Fintype.sum_equiv (cyclicBlockStartEquiv hR) _ _ fun _ ↦ rfl
    _ = (∑ q : NonwrappingStart R (m + R - 1),
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap (localTermES A R q.1))) x := by
      simp

end MPSTensor
