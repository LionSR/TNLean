/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationPadding
import TNLean.MPS.Overlap.Basic

/-!
# Unused bond coordinates in periodic MPS representations

Zero padding all site matrices to a larger common bond dimension preserves
every positive-length periodic vector. The empty word is excluded because
its trace is the bond dimension.

Source: the finite-size, size-independent dimension comparison in SPWC10,
arXiv:0909.5347, Theorem 5, lines 850--880; finite-dimensional trace-MPS
conventions in PGVWC07, arXiv:quant-ph/0608197, lines 400--429.
-/

open Matrix
open scoped BigOperators

namespace MPSTensor

/-- Adjoin unused virtual coordinates to every site matrix.
Source: the common matrix-size formulation of SPWC10, Theorem 5. -/
def padBond {d D : ℕ} (A : MPSTensor d D) (K : ℕ) : MPSTensor d K :=
  fun i ↦ Matrix.zeroPad K (A i)

private theorem evalWord_padBond_cons {d D K : ℕ} (A : MPSTensor d D) (hDK : D ≤ K)
    (a : Fin d) (w : List (Fin d)) :
    Kraus.evalWord (padBond A K) (a :: w) = Matrix.zeroPad K (Kraus.evalWord A (a :: w)) := by
  induction w generalizing a with
  | nil => simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, padBond]
  | cons b w ih =>
      calc
        _ = Matrix.zeroPad K (A a) * Kraus.evalWord (padBond A K) (b :: w) := rfl
        _ = Matrix.zeroPad K (A a) * Matrix.zeroPad K (Kraus.evalWord A (b :: w)) := by
          rw [ih b]
        _ = Matrix.zeroPad K (A a * Kraus.evalWord A (b :: w)) :=
          (Matrix.zeroPad_mul _ _ hDK).symm
        _ = _ := rfl

/-- Unused virtual coordinates change no periodic vector of positive
length. Source: SPWC10, Theorem 5, common matrix-size formulation. -/
theorem mpv_padBond {d D K N : ℕ} (A : MPSTensor d D) (hDK : D ≤ K) (hN : 0 < N)
    (σ : Fin N → Fin d) : mpv (padBond A K) σ = mpv A σ := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp only [mpv, coeff, List.ofFn_succ]
  rw [evalWord_padBond_cons A hDK]
  rw [Matrix.trace, Matrix.trace, Fin.sum_castLE_extend_zero _ hDK]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · exact Matrix.zeroPad_apply_of_lt _ ha ha
  · exact Matrix.zeroPad_apply_eq_zero _ (by omega)

/-- The Hilbert-space periodic vector is unchanged by bond padding at
positive length. Source: SPWC10, Theorem 5, common matrix-size formulation. -/
theorem mpvState_padBond {d D K N : ℕ} (A : MPSTensor d D) (hDK : D ≤ K) (hN : 0 < N) :
    mpvState (padBond A K) N = mpvState A N := by
  apply PiLp.ext
  intro σ
  exact mpv_padBond A hDK hN σ

end MPSTensor
