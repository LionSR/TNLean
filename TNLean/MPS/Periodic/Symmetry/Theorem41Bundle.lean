/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Theorem 4.1, bundled statement

This module bundles the forward and reverse conditional statements of Theorem
4.1 into a single equivalence.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — bidirectional equivalence -/

section Theorem41Bundle

variable {d D : ℕ}

/-- **Theorem 4.1 (bidirectional, conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Under both the forward
canonicalization hypothesis `PRefinementCanonicalization` and the inverse canonicalization
hypothesis `PRefinementInverseCanonicalization`, `p`-refinability of `B` is equivalent to
`p`-divisibility of its transfer map. This bundles
`thm_4_1_p_refinement_forward` and `thm_4_1_p_refinement_reverse` into a single iff. -/
theorem thm_4_1_p_refinement
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ) (hp : 0 < p)
    (hCanonical : PRefinementCanonicalization d D p)
    (hInverse : PRefinementInverseCanonicalization d D p) :
    IsPRefinable B p ↔ IsPDivisibleChannel (transferMap B) p :=
  ⟨thm_4_1_p_refinement_forward B hB p hCanonical,
   thm_4_1_p_refinement_reverse B hB p hp hInverse⟩

end Theorem41Bundle

end MPSTensor
