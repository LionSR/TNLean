/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.FiniteRangeKnabe
import TNLean.MPS.ParentHamiltonian.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.CyclicWindowPermutation
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

/-- Replacing coordinates inside a subwindow of the active block leaves the spectator
configuration unchanged. This is the finite-interval geometry in Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem cyclicCfg_join_cyclicActiveBlock {N W R : ℕ}
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
    have hglobalOffset (hqr : q.val ≤ r.val) :
        ((cyclicForwardSite s r.val).val + N -
          (cyclicForwardSite s q.val).val) % N = r.val - q.val := by
      rw [show cyclicForwardSite s r.val =
          cyclicForwardSite (cyclicForwardSite s q.val) (r.val - q.val) by
        rw [cyclicForwardSite_forwardSite]
        congr 1
        omega]
      simpa [cyclicForwardSite] using
        offset_mod_eq (cyclicForwardSite s q.val).isLt (by omega : r.val - q.val < N)
    by_cases hr : q.val ≤ r.val ∧ r.val < q.val + R
    · have hactiveOffset : (r.val + W - q.val) % W = r.val - q.val := by
        have hsum : r.val + W - q.val = r.val - q.val + W := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r.val - q.val < W)]
      rw [dite_eq_left (by rw [hglobalOffset hr.1]; omega),
        dite_eq_left (by rw [hactiveOffset]; omega)]
      congr 1
      apply Fin.ext
      exact (hglobalOffset hr.1).trans hactiveOffset.symm
    · have hglobalNot : ¬((cyclicForwardSite s r.val).val + N -
          (cyclicForwardSite s q.val).val) % N < R := by
        intro hoff
        by_cases hqr : q.val ≤ r.val
        · rw [hglobalOffset hqr] at hoff
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

/-- Restricting a joined active-block configuration to a subwindow agrees with
restriction inside the active block. Source: Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem extractWindow_join_cyclicActiveBlock {N W R : ℕ}
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

/-! ### Blocks of consecutive terms on the ring

For a local matrix `h` on `R` sites, the terms of its translates on the ring
(`ManyBody.Interaction.translationInvariant`) with windows inside one window of `W` consecutive
sites add up to the translate of the open-chain Hamiltonian of `h` on `W` sites
(`ManyBody.Interaction.chainTranslates`); in the cyclic active-block coordinates of its window, a
term acts on the active block only. -/

section RingTerms

open Fin.CommRing

variable {R N : ℕ}

/-- A term of the translates of `h` on the ring acts at a configuration \(σ\) as `h` on the
cyclic restriction to its window, read at the window of \(σ\). -/
theorem toEuclideanLin_translationInvariant_term_apply (hRN : R ≤ N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N))
    (σ : Cfg d N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i) v σ =
      Matrix.toEuclideanLin h (cyclicRestrictES (Fin.pos i) R i σ v) (extractWindow R i σ) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [ManyBody.Interaction.translationInvariant_term_of_le _ hRN i, Matrix.toLpLin_apply,
    Matrix.toLpLin_apply]
  change Matrix.mulVec (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hRN i) h)
    (WithLp.ofLp v) σ = Matrix.mulVec h _ _
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ _ σ (replaceWindow R hRN i σ)
    (replaceWindow_ringWindow hRN i σ)
    (fun τ _ hv ↦ replaceWindow_of_forall_ringWindow_ne hRN i σ τ hv)]
  rfl

/-- A term of the translates of `h` on the ring is the cyclic average of the conjugates of `h`
by the restrictions to its window. -/
theorem toEuclideanLin_translationInvariant_term_eq_inv_smul_sum (hRN : R ≤ N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i) =
      (((d ^ R : ℕ) : ℂ)⁻¹) • ∑ τ : Cfg d N,
        (cyclicRestrictES (Fin.pos i) R i τ).adjoint ∘ₗ Matrix.toEuclideanLin h ∘ₗ
          cyclicRestrictES (Fin.pos i) R i τ := by
  have : NeZero N := NeZero.of_pos i.pos
  ext v σ
  rw [toEuclideanLin_translationInvariant_term_apply hRN,
    inv_smul_sum_adjoint_comp_cyclicRestrictES_apply hRN]

/-- In the cyclic active-block coordinates of its window, a term of the translates of `h` on the
ring is `h` on the active block, acting independently on every spectator configuration. Source:
PGVWC07, arXiv:quant-ph/0608197, Theorem 11 proof, lines 1418–1422. -/
theorem cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply
    (hRN : R ≤ N) (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N)
    (ψ : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
        (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i) ψ) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h))
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i ψ) := by
  have : NeZero N := NeZero.of_pos i.pos
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  apply U.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  ext σ
  rw [toEuclideanLin_translationInvariant_term_apply hRN,
    cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change Matrix.toEuclideanLin h _ (extractWindow R i σ) =
    Matrix.toEuclideanLin h (ContinuousLinearMap.rightFiber (U ψ) (e σ).2) (extractWindow R i σ)
  apply congrArg
    (fun w : EuclideanSpace ℂ (Cfg d R) => Matrix.toEuclideanLin h w (extractWindow R i σ))
  ext ω
  change ψ (cyclicCfg (Fin.pos i) R i ω σ) = ψ (e.symm (ω, (e σ).2))
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · have hω : ω = (e σ).1 := Subsingleton.elim _ _
    rw [hω, Prod.mk.eta, Equiv.symm_apply_apply]
    exact congrArg ψ (funext fun k ↦ by simp [cyclicCfg])
  · have hfull (ξ : Cfg d R) : cyclicCfg hR R (⟨0, hR⟩ : Fin R) ω ξ = ω := by
      funext j
      simp [cyclicCfg, Nat.mod_eq_of_lt j.isLt]
    have hj := cyclicCfg_join_cyclicActiveBlock hRN i (⟨0, hR⟩ : Fin R)
      (by simp) ω (e σ).1 (e σ).2
    simp only [cyclicForwardSite_zero, hfull, Prod.mk.eta] at hj
    rw [Equiv.symm_apply_apply] at hj
    exact congrArg ψ hj

end RingTerms

end MPSTensor

namespace ManyBody.Interaction

open Fin.CommRing

variable {α : Type*} [Fintype α] [DecidableEq α] {R N : ℕ} [NeZero N]

/-- **A window of terms.** On the ring of `N` sites, the translate to the window of `W ≤ N`
consecutive sites starting at `i` of the open-chain Hamiltonian of `h` on `W` sites is the sum of
the terms of the translates of `h` on the ring at the starts `i, i + 1, …, i + (W - R)`: the
windows of `R` consecutive sites inside that window. -/
theorem translationInvariant_term_hamiltonian_chainTranslates
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) {W : ℕ} (hWN : W ≤ N) (i : Fin N) :
    (translationInvariant N (chainTranslates R W h).hamiltonian).term i =
      ∑ j : Fin (W + 1 - R), (translationInvariant N h).term (i + (j.val : Fin N)) := by
  rw [translationInvariant_term_of_le _ hWN, hamiltonian, ManyBody.placeAlong_sum]
  refine Fintype.sum_congr _ _ fun j ↦ ?_
  rw [ofPlaceAlong_term, translationInvariant_term_of_le _ (show R ≤ N by have := j.isLt; omega),
    ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_ringWindow]

/-- **Separated windows.** Terms of translates on the ring whose windows of `R` consecutive
sites start `e` sites apart, with `R ≤ e` and `e + R ≤ N`, commute: the windows are disjoint. -/
theorem commute_translationInvariant_term_add_of_le
    (h h' : Matrix (Fin R → α) (Fin R → α) ℂ) {e : ℕ} (hR : R ≤ e) (he : e + R ≤ N)
    (i : Fin N) :
    Commute ((translationInvariant N h).term i)
      ((translationInvariant N h').term (i + (e : Fin N))) := by
  have hRN : R ≤ N := by omega
  rw [translationInvariant_term_of_le _ hRN, translationInvariant_term_of_le _ hRN]
  refine ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ α) _
    (Finset.disjoint_left.mpr fun k hki hkj ↦ ?_) _ _
  have hj : i + (e : Fin N) = MPSTensor.cyclicForwardSite i e :=
    Fin.ext (by simp [MPSTensor.cyclicForwardSite, Fin.val_add])
  rw [hj] at hkj
  exact MPSTensor.cyclicWindowsDisjoint_cyclicForwardSite_of_oriented_separation hR he i k
    ((MPSTensor.mem_map_ringWindow_iff hRN i k).mp hki)
    ((MPSTensor.mem_map_ringWindow_iff hRN _ k).mp hkj)

/-- Separated terms commute, for sites indexed by the cyclic group. -/
theorem commute_translationInvariant_term_finEquiv_symm_add_of_le
    (h h' : Matrix (Fin R → α) (Fin R → α) ℂ) {e : ℕ} (hR : R ≤ e) (he : e + R ≤ N)
    (s : ZMod N) :
    Commute ((translationInvariant N h).term ((ZMod.finEquiv N).symm s))
      ((translationInvariant N h').term ((ZMod.finEquiv N).symm (s + (e : ZMod N)))) := by
  rw [map_add, map_natCast]
  exact commute_translationInvariant_term_add_of_le h h' hR he _

/-- **A Knabe block.** For `1 ≤ R`, the sum of the operators of `m` consecutive terms of the
translates of `h` on the ring, starting at the site `s`, is the operator of the translate to the
window of `m + R - 1` consecutive sites starting at `s` of the open-chain Hamiltonian of `h` on
`m + R - 1` sites. The sites are indexed by the cyclic group, as in the finite-range Knabe
inequality. -/
theorem cyclicWindowSum_toEuclideanLin_translationInvariant_term
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) {m : ℕ} (hR : 1 ≤ R) (hW : m + R - 1 ≤ N)
    (s : ZMod N) :
    ProjectionGeometry.cyclicWindowSum (fun s : ZMod N ↦
        Matrix.toEuclideanLin ((translationInvariant N h).term ((ZMod.finEquiv N).symm s))) m s =
      Matrix.toEuclideanLin ((translationInvariant N
        (chainTranslates R (m + R - 1) h).hamiltonian).term ((ZMod.finEquiv N).symm s)) := by
  rw [translationInvariant_term_hamiltonian_chainTranslates h hW, map_sum,
    ProjectionGeometry.cyclicWindowSum]
  refine Fin.sum_eq_sum_of_val_eq _ _ (fun k _ _ ↦ ?_) (fun i hi ↦ absurd i.isLt (by omega))
    (fun i hi ↦ absurd i.isLt (by omega))
  rw [map_add, map_natCast]

/-- The operators of the terms of the translates on the ring, indexed by the cyclic group, add
up to the operator of the Hamiltonian. -/
theorem sum_toEuclideanLin_translationInvariant_term_finEquiv_symm
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) :
    ∑ s : ZMod N, Matrix.toEuclideanLin
        ((translationInvariant N h).term ((ZMod.finEquiv N).symm s)) =
      Matrix.toEuclideanLin (translationInvariant N h).hamiltonian := by
  rw [hamiltonian, map_sum]
  exact (ZMod.finEquiv N).symm.toEquiv.sum_comp fun i ↦
    Matrix.toEuclideanLin ((translationInvariant N h).term i)

end ManyBody.Interaction
