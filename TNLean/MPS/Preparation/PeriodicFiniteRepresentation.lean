/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CutRank
import TNLean.MPS.Chain.SiteIndependent
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.MPS.Overlap.Basic

/-!
# Periodic MPS representations of finite cyclic-invariant vectors

Every nonzero vector of positive length which is fixed exactly by cyclic
translation has a periodic trace-MPS representation with matrix size
N times d to the power floor N/2. The existing actual OBC construction
supplies the open chain; the existing cyclic-block construction makes
its site matrices independent of the site.

Exact vector invariance is essential: invariance of the one-dimensional
line, or invariance of its rank-one density matrix, allows a nontrivial
translation eigenphase and does not assert this conclusion.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorems 1 and 3, lines 431--458
and 620--649; the finite-prefix issue in SPWC10, arXiv:0909.5347,
Theorem 5, lines 850--880.
-/

namespace MPSTensor

/-- A nonzero, exactly cyclic-invariant finite vector has an actual
periodic MPS representation of explicit finite size. The OBC representation
is constructed, not supplied. Source: PGVWC07, Theorems 1 and 3,
lines 431--458 and 620--649. -/
theorem exists_mpv_eq_of_cyclic_invariant {d N : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (hTI : ∀ (s : Fin N) (σ : Fin N → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ) :
    ∃ A : MPSTensor d (N * d ^ (N / 2)), ∀ σ, mpv A σ = ψ σ := by
  classical
  let : NeZero d := ⟨by
    intro hd
    subst d
    apply hψ
    funext σ
    exact Fin.elim0 (σ ⟨0, hN⟩)⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨B, hB, _, _, _⟩ := OBCChainTensor.exists_coeff_eq_of_cutRank_le hψ
    (fun k ↦ MPSPreparation.cutRank_le_pow_half ψ k.val)
  have hBTI : B.IsTranslationInvariantState := by
    intro s σ
    simp only [hB]
    exact hTI s σ
  obtain ⟨A, hA⟩ := OBCChainTensor.exists_pgvwc07_site_independent_tensor B hBTI
  exact ⟨A, fun σ ↦ (hA σ).trans (congrFun hB σ)⟩

/-- The same construction in the actual finite Hilbert space.
Source: PGVWC07, Theorems 1 and 3, positive-length normalized or
unnormalized vector convention. -/
theorem exists_mpvState_eq_of_cyclic_invariant {d N : ℕ} (hN : 0 < N)
    (ψ : MPVSpace d N) (hψ : ψ ≠ 0)
    (hTI : ∀ (s : Fin N) (σ : Fin N → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ) :
    ∃ A : MPSTensor d (N * d ^ (N / 2)), mpvState A N = ψ := by
  have hfun : (fun σ ↦ ψ σ) ≠ 0 := by
    intro hzero
    apply hψ
    apply PiLp.ext
    intro σ
    exact congrFun hzero σ
  obtain ⟨A, hA⟩ := exists_mpv_eq_of_cyclic_invariant hN (fun σ ↦ ψ σ) hfun hTI
  refine ⟨A, ?_⟩
  apply PiLp.ext
  intro σ
  exact hA σ

/-- Every periodic trace-MPS vector has exactly zero cyclic momentum.
Source: the periodic trace convention in PGVWC07, lines 400--429. -/
theorem mpvState_cyclic_invariant {d D N : ℕ} (A : MPSTensor d D)
    (s : Fin N) (σ : Fin N → Fin d) :
    mpvState A N (fun k ↦ σ (k + s)) = mpvState A N σ := by
  change mpv A (σ ∘ finCycle s) = mpv A σ
  rw [finCycle_eq_finRotate_iterate]
  exact mpv_comp_finRotate_pow A s.val σ

/-- At positive length, a nonzero vector has a periodic trace-MPS
representation exactly when cyclic translation fixes the vector itself.
An invariant line alone is insufficient for this equivalence.
Source: PGVWC07, Theorem 3 and its periodic trace convention,
lines 400--429 and 620--649. -/
theorem exists_mpvState_eq_iff_cyclic_invariant {d N : ℕ} (hN : 0 < N)
    (ψ : MPVSpace d N) (hψ : ψ ≠ 0) :
    (∃ (D : ℕ) (A : MPSTensor d D), mpvState A N = ψ) ↔
      ∀ (s : Fin N) (σ : Fin N → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ := by
  constructor
  · rintro ⟨D, A, rfl⟩
    exact mpvState_cyclic_invariant A
  · intro hTI
    obtain ⟨A, hA⟩ := exists_mpvState_eq_of_cyclic_invariant hN ψ hψ hTI
    exact ⟨_, A, hA⟩

end MPSTensor
