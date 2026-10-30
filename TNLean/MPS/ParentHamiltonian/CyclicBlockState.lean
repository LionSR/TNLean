/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import TNLean.MPS.Overlap.Basic

/-!
# Periodic MPS vectors in cyclic active-block coordinates

Expose a consecutive active block and its ordered complement. The actual
periodic vector becomes the boundary map of the active tensor evaluated on
the complementary word. This is the tensor-coordinate identity used in
PGVWC07, arXiv:quant-ph/0608197, Theorem 11 (`2blocks.1`), proof lines
1418–1422 of `Papers/quant-ph_0608197/MPSarchive.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D N L : ℕ}

/-- Joining the two cyclic blocks factors the actual closed-word amplitude.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem mpv_cyclicActiveBlockConfigEquiv_symm
    (A : MPSTensor d D) (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d L) (τ : Cfg d (N - L)) :
    mpv A ((cyclicActiveBlockConfigEquiv d L hLN i).symm (σ, τ)) =
      groundSpaceMap A L (Kraus.evalWord A (List.ofFn τ)) σ := by
  let ω := (cyclicActiveBlockConfigEquiv d L hLN i).symm (σ, τ)
  have hrot : (List.ofFn ω).rotate i.val = List.ofFn σ ++ List.ofFn τ := by
    apply List.ext_getElem
    · simp only [List.length_rotate, List.length_append, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by simpa only [List.length_rotate, List.length_ofFn] using hk₁
      simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
      by_cases hkL : k < L
      · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hkL),
          List.getElem_ofFn]
        simpa only [ω, cyclicForwardSite, Nat.add_comm] using
          cyclicActiveBlockConfigEquiv_symm_apply_window hLN i σ τ ⟨k, hkL⟩
      · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega),
          List.getElem_ofFn]
        have hk : k - L < N - L := by omega
        simpa only [ω, cyclicForwardSite, List.length_ofFn,
          show L + (k - L) = k by omega, Nat.add_comm] using
          cyclicActiveBlockConfigEquiv_symm_apply_spectator hLN i σ τ ⟨k - L, hk⟩
  change Matrix.trace (Kraus.evalWord A (List.ofFn ω)) =
    Matrix.trace (Kraus.evalWord A (List.ofFn σ) * Kraus.evalWord A (List.ofFn τ))
  rw [← Kraus.evalWord_append, ← hrot,
    List.rotate_eq_drop_append_take (by simp only [List.length_ofFn]; exact i.isLt.le),
    Kraus.evalWord_append]
  conv_lhs => rw [← List.take_append_drop i.val (List.ofFn ω), Kraus.evalWord_append]
  exact Matrix.trace_mul_comm _ _

/-- The cyclic active-block coordinates of the actual periodic Hilbert vector
are the active boundary map with the complementary word as boundary matrix.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem cyclicActiveBlock_mpvState_apply
    (A : MPSTensor d D) (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d L) (τ : Cfg d (N - L)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d L hLN i (mpvState A N) (σ, τ) =
      groundSpaceMap A L (Kraus.evalWord A (List.ofFn τ)) σ := by
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply, mpvState_apply,
    mpv_cyclicActiveBlockConfigEquiv_symm]

end MPSTensor
