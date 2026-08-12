/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.CyclicBlockAverage
import TNLean.MPS.Chain.VaryingBondOBC

/-!
# Site-independent matrices for a fixed translation-invariant state

This file completes the construction in PGVWC07, Theorem 3. A varying-bond
open-boundary representation of a translation-invariant state on one positive
ring is first padded to a square site-dependent chain. Cyclic block averaging
then gives one site-independent tensor of bond dimension \(ND\) with the same
coefficient at that ring length.

The constructed tensor depends on \(N\). No equality at other lengths is
asserted.

Source: PGVWC07, arXiv:quant-ph/0608197, lines 620--649.
-/

open scoped BigOperators Matrix

namespace OBCChainTensor

variable {d D N : ℕ}

/-- Rotating the padded square chain by \(k\) sites is the same as translating
the physical configuration by \(-k\) in the original open-boundary
coefficient. The inverse is forced by restoring the rotated matrix product to
the distinguished open cut. -/
private theorem coeff_cyclicRotation_zeroPad_eq_coeff_cyclicTranslateConfig_neg
    (A : OBCChainTensor d D N) [NeZero N]
    (k : Fin N) (σ : Fin N → Fin d) :
    MPSChainTensor.coeff
        (MPSChainTensor.cyclicRotation A.zeroPad k) σ =
      A.coeff (cyclicTranslateConfig (-k) σ) := by
  classical
  rw [← A.coeff_zeroPad (cyclicTranslateConfig (-k) σ)]
  rw [MPSChainTensor.coeff_eq_sum_cyclic,
    MPSChainTensor.coeff_eq_sum_cyclic]
  let e : (Fin N → Fin D) ≃ (Fin N → Fin D) :=
    (finCycle k).arrowCongr (Equiv.refl (Fin D))
  refine Fintype.sum_equiv e _ _ fun g => ?_
  let F : Fin N → ℂ := fun m =>
    A.zeroPad m ((cyclicTranslateConfig (-k) σ) m)
      ((e g) m) ((e g) (m + 1))
  calc
    (∏ j : Fin N,
        (MPSChainTensor.cyclicRotation A.zeroPad k) j
          (σ j) (g j) (g (j + 1))) =
      ∏ j : Fin N, F (finCycle k j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp [F, e, MPSChainTensor.cyclicRotation_apply,
          cyclicTranslateConfig, finCycle, add_assoc]
        congr 4
        abel
    _ = ∏ m : Fin N, F m := Equiv.prod_comp (finCycle k) F

/-- **Conditional PGVWC07 Theorem 3 construction.** A supplied varying-bond
open-boundary representation of a translation-invariant state on one positive
ring of length \(N\) yields a
site-independent trace-MPS representation of bond dimension \(ND\) at that
same length.

The tensor is `MPSChainTensor.cyclicBlockTensor A.zeroPad` and depends on
\(N\). Purity is used upstream in PGVWC07 to supply the rectangular open-boundary
representation; the finite cyclic-block calculation itself needs only the OBC
chain tensor and the stated translation invariance.

**Scope restriction (supplied OBC representation):** the arbitrary-state OBC
existence input of PGVWC07 Theorem 3 is not included. This boundary is recorded
in `docs/paper-gaps/pgvwc07_site_independent_scope.tex`. -/
theorem pgvwc07_site_independent_matrices
    (A : OBCChainTensor d D N) [NeZero N]
    (hTI : A.IsTranslationInvariantState) (σ : Fin N → Fin d) :
    MPSTensor.mpv (MPSChainTensor.cyclicBlockTensor A.zeroPad) σ =
      A.coeff σ := by
  rw [MPSChainTensor.mpv_cyclicBlockTensor_eq_average]
  simp_rw [coeff_cyclicRotation_zeroPad_eq_coeff_cyclicTranslateConfig_neg A]
  have hTI' (k : Fin N) :
      A.coeff (cyclicTranslateConfig (-k) σ) = A.coeff σ :=
    hTI (-k) σ
  simp_rw [hTI']
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  simp [hN]

/-- Existence form of `pgvwc07_site_independent_matrices`. -/
theorem exists_pgvwc07_site_independent_tensor
    (A : OBCChainTensor d D N) [NeZero N]
    (hTI : A.IsTranslationInvariantState) :
    ∃ B : MPSTensor d (N * D),
      ∀ σ : Fin N → Fin d, MPSTensor.mpv B σ = A.coeff σ :=
  ⟨MPSChainTensor.cyclicBlockTensor A.zeroPad,
    pgvwc07_site_independent_matrices A hTI⟩

end OBCChainTensor
