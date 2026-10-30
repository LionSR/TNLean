/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSPureWindowHamiltonian
import TNLean.MPS.ParentHamiltonian.CyclicTranslation
import TNLean.Algebra.FinCyclicInduction

/-!
# The pure particle projector at its matching periodic volume

At a root-of-unity weight, the existing PVBS one-particle line is invariant
under cyclic translation, with its actual vector phase retained. When the
periodic volume equals the interaction range, the actual pure-window
Hamiltonian has exactly this line as its kernel. A nontrivial phase excludes
nonzero translation-invariant vectors in that kernel.

This concerns one matching periodic volume. It supplies no all-volume model
or unrestricted counterexample to SPWC10, arXiv:0909.5347, Theorem 5.
The PVBS coefficients are those of arXiv:1112.4097, Section II, equations (1)--(8).
-/

namespace MPSTensor

private theorem cyclicCfg_full_eq_neg_translate {R : ℕ} (hR : 0 < R)
    (i : Fin R) (ω τ : Cfg 2 R) :
    cyclicCfg hR R i ω τ = cyclicTranslateCfg (-i) ω := by
  let _ : NeZero R := ⟨hR.ne'⟩
  funext k
  change (if h : (k.val + R - i.val) % R < R then
    ω ⟨(k.val + R - i.val) % R, h⟩ else τ k) = ω (k + -i)
  rw [dite_eq_left (Nat.mod_lt _ hR)]
  congr 1
  apply Fin.ext
  have hi := i.isLt
  rw [← sub_eq_add_neg, Fin.val_sub, Fin.val_mk]
  congr 1
  omega

/-- Every cyclic translate preserves the existing one-particle line when its
weight satisfies the matching root-of-unity equation. The vector itself need
not be invariant. Source: PVBS coefficients, arXiv:1112.4097, Section II. -/
theorem cyclicTranslateState_pvbsEdge_mem_span (q : ℂ) {R : ℕ} (hR : 0 < R)
    (hq : q ^ R = 1) (s : Fin R) :
    cyclicTranslateState s (pvbsEdge q R) ∈ Submodule.span ℂ {pvbsEdge q R} := by
  cases R with
  | zero => omega
  | succ N =>
    let _ : NeZero (N + 1) := ⟨by omega⟩
    have hqzero : q ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega)] at hq
      exact zero_ne_one hq
    have hphase : q • cyclicTranslateState (1 : Fin (N + 1)) (pvbsEdge q (N + 1)) =
        pvbsEdge q (N + 1) := by
      ext σ
      change q * pvbsEdge q (N + 1) (fun j ↦ σ (j + 1)) = pvbsEdge q (N + 1) σ
      simpa only [finRotate_apply] using pvbsEdge_cyclic_step q N hq σ
    have hone : cyclicTranslateState (1 : Fin (N + 1)) (pvbsEdge q (N + 1)) =
        q⁻¹ • pvbsEdge q (N + 1) := by
      have h := congrArg (fun f : NSiteSpace 2 (N + 1) ↦ q⁻¹ • f) hphase
      simpa only [smul_smul, inv_mul_cancel₀ hqzero, one_smul] using h
    apply Fin.cyclic_induction ?_ ?_ s
    · have h0 : cyclicTranslateState (0 : Fin (N + 1)) (pvbsEdge q (N + 1)) =
          pvbsEdge q (N + 1) := by
        ext σ
        change pvbsEdge q (N + 1) (fun k ↦ σ (k + 0)) = pvbsEdge q (N + 1) σ
        simp only [add_zero]
      rw [h0]
      exact Submodule.mem_span_singleton_self _
    · intro i hi
      rw [← cyclicTranslateState_add i 1 (pvbsEdge q (N + 1)), hone, map_smul]
      exact Submodule.smul_mem _ _ hi

/-- The actual matching-volume periodic Hamiltonian annihilates the existing
one-particle vector at a matching root of unity. Its local section equations
are proved, not supplied. Source: PVBS coefficients and cyclic line invariance,
arXiv:1112.4097, Section II. -/
theorem pvbsPureWindowHamiltonian_apply_pvbsEdge (q : ℂ) {R : ℕ} (hR : 0 < R)
    (hq : q ^ R = 1) :
    periodicInteractionHamiltonianES (pvbsPureWindowInteraction q R) R
      (WithLp.toLp 2 (pvbsEdge q R)) = 0 := by
  apply (periodicInteractionHamiltonianES_eq_zero_iff_sections
    (pvbsPureWindowInteraction q R) (pvbsPureWindowInteraction_isPositive q R)
    hR le_rfl _).mpr
  intro i τ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (cyclicTranslateState_pvbsEdge_mem_span q hR hq (-i))
  apply (pvbsPureWindowInteraction_apply_eq_zero_iff q R _).mpr
  refine ⟨c, fun σ ↦ ?_⟩
  change pvbsEdge q R (cyclicCfg (Fin.pos i) R i σ τ) = c * pvbsEdge q R σ
  rw [cyclicCfg_full_eq_neg_translate (Fin.pos i)]
  exact (congrFun hc σ).symm

/-- At its matching periodic volume, the actual pure-window Hamiltonian has
exactly the existing one-particle line as its kernel. No local-space or kernel
identity is assumed. Source: the PVBS cyclic line at a root of unity,
arXiv:1112.4097, Section II; finite-volume context SPWC10, Theorem 5. -/
theorem ker_pvbsPureWindowHamiltonian_matching_volume (q : ℂ) {R : ℕ} (hR : 0 < R)
    (hq : q ^ R = 1) :
    LinearMap.ker (periodicInteractionHamiltonianES (pvbsPureWindowInteraction q R) R) =
      Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)} := by
  let _ : NeZero R := ⟨hR.ne'⟩
  ext ψ
  constructor
  · intro hψ
    have hsections := (periodicInteractionHamiltonianES_eq_zero_iff_sections
      (pvbsPureWindowInteraction q R) (pvbsPureWindowInteraction_isPositive q R)
      hR le_rfl ψ).mp hψ
    let i : Fin R := ⟨0, hR⟩
    obtain ⟨c, hc⟩ := (pvbsPureWindowInteraction_apply_eq_zero_iff q R _).mp
      (hsections i 0)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    ext σ
    have hcfg : cyclicCfg (Fin.pos i) R i σ (0 : Cfg 2 R) = σ := by
      rw [cyclicCfg_full_eq_neg_translate (Fin.pos i)]
      ext k
      simp [cyclicTranslateCfg, i]
    have h := hc σ
    change ψ (cyclicCfg (Fin.pos i) R i σ 0) = c * pvbsEdge q R σ at h
    change c * pvbsEdge q R σ = ψ σ
    rw [hcfg] at h
    exact h.symm
  · intro hψ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    change periodicInteractionHamiltonianES (pvbsPureWindowInteraction q R) R
      (c • WithLp.toLp 2 (pvbsEdge q R)) = 0
    rw [map_smul, pvbsPureWindowHamiltonian_apply_pvbsEdge q hR hq, smul_zero]

/-- The matching-volume kernel contains the actual nonzero one-particle vector.
Nonvanishing is read from its unit first-excitation coefficient, rather than
supplied as a ground-state premise. Source: PVBS coefficients,
arXiv:1112.4097, Section II. -/
theorem pvbsPureWindowHamiltonian_matching_volume_nonzero_ground (q : ℂ)
    {R : ℕ} (hR : 0 < R) (hq : q ^ R = 1) :
    (WithLp.toLp 2 (pvbsEdge q R) : MPVSpace 2 R) ≠ 0 ∧
      periodicInteractionHamiltonianES (pvbsPureWindowInteraction q R) R
        (WithLp.toLp 2 (pvbsEdge q R)) = 0 := by
  refine ⟨?_, pvbsPureWindowHamiltonian_apply_pvbsEdge q hR hq⟩
  intro hzero
  cases R with
  | zero => omega
  | succ N =>
    have h := congrArg (fun v : MPVSpace 2 (N + 1) ↦ v (Fin.cons 1 0)) hzero
    have hentry : (1 : ℂ) = 0 := by
      simpa only [pvbsEdge_first, PiLp.zero_apply] using h
    exact one_ne_zero hentry

/-- A nontrivial cyclic phase excludes every nonzero translation-invariant
vector from the actual matching-volume ground kernel. Translation invariance
is stated on the original coefficient vector, not only its line.
Source: the PVBS cyclic phase, arXiv:1112.4097, Section II; finite-prefix
context SPWC10, arXiv:0909.5347, Theorem 5, lines 850–880. -/
theorem eq_zero_of_pvbsPureWindow_matching_volume_fixed (q : ℂ) {R : ℕ}
    (hR : 0 < R) (hq : q ^ R = 1) (hqone : q ≠ 1) (ψ : MPVSpace 2 R)
    (hzero : periodicInteractionHamiltonianES (pvbsPureWindowInteraction q R) R ψ = 0)
    (hfixed : ∀ s : Fin R, cyclicTranslateState s ψ.ofLp = ψ.ofLp) : ψ = 0 := by
  have hmem : ψ ∈ Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q R)} := by
    rw [← ker_pvbsPureWindowHamiltonian_matching_volume q hR hq]
    exact hzero
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  by_cases hc : c = 0
  · simp [hc]
  exfalso
  cases R with
  | zero => omega
  | succ N =>
    let _ : NeZero (N + 1) := ⟨by omega⟩
    apply pvbsEdge_not_cyclic_invariant q N hq hqone
    intro σ
    have h := congrFun (hfixed (1 : Fin (N + 1))) σ
    change c * pvbsEdge q (N + 1) (fun j ↦ σ (j + 1)) = c * pvbsEdge q (N + 1) σ at h
    have heq := mul_left_cancel₀ hc h
    simpa only [finRotate_apply] using heq

end MPSTensor
