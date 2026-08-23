/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Blocking

/-!
# Repeated words

`evalWord_replicate`, the elementary identity for evaluating a tensor on a
`List.replicate`-built word, now lives in `TNLean/Kraus/Blocking.lean`,
alongside the rest of the physical-blocking
word-evaluation layer. This file keeps the one matrix-product-vector
consequence, `mpv_const_eq_trace_pow`, which packages that identity as an
`mpv` statement.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The MPV of a constant configuration is the trace of a matrix power. -/
lemma mpv_const_eq_trace_pow (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    mpv A (fun _ : Fin L => i) = Matrix.trace ((A i) ^ L) := by
  simp only [mpv, coeff, List.ofFn_const, evalWord_replicate]

end MPSTensor
