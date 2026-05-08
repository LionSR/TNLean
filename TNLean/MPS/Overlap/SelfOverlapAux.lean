/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Overlap.Basic

/-!
# Self-overlap convergence auxiliaries

This module collects small auxiliary lemmas about the convergence of MPV self-overlaps
used by both the BNT Permutation Rigidity argument and the Fundamental Theorem helpers.

## Main statements

* `tendsto_norm_selfOverlap_one`: normed form of a self-overlap tending to `1`.

## Tags

matrix product states, overlap, convergence
-/

open Filter

namespace MPSTensor

variable {d : ℕ}

/-- Norm-convergence form of normalized self-overlap convergence. -/
lemma tendsto_norm_selfOverlap_one
    {D : ℕ} (A : MPSTensor d D)
    (hA : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
  simpa [norm_one] using hA.norm

end MPSTensor
