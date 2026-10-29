# Follow-up to the Blueprint hypothesis audit

Baseline: main `55b8f9d56d909a1d32d58dad3a2b25ed967128c6`.
Issue: #7726.

## Specific defects already repaired on main

- The residual three-leg scalar reduction explicitly assumes nonzero virtual
  leg spaces and cites the convention note. Its current owner is
  `ch24_peps_ft_edge_kernel_gauges_absorption_scalar_comparison.tex`.
- The two nonscalar-fixed-point splitting statements and the irreducible
  scalar-fixed-point statement no longer require a nonempty bond index.
  Commit `f4c2d204a` (#9243) supplies the dimension-zero branches.
- `MPS/ParentHamiltonian/ProductPair.lean` was retired by `3ce26ade4`;
  its two cited markers are not live obligations.
- All three cited markers in `MPS/MPDO/PhysicalSectorProductTransport.lean`
  now name `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.
  The restored citations are in `0b09bf147` (#7956).

## The remaining concrete chain co-anchor

The overlap-window extraction node had also owned
`MPSChainTensor.eq_of_span_mul_left`, a generic matrix cancellation result.
The latter quantified over a separate finite index set absent from the
window statement. It now has a separate support lemma explicitly stating
both cancellation orientations, its index set, and its spanning hypothesis.
The window proof cites that support lemma. Every prior window label, statement,
readiness tag and primary declaration is retained.

The two cancellation proofs no longer expand a finite linear combination of
spanning matrices. Mathlib's `LinearMap.ext_on_range` equates the corresponding
multiplication maps, and evaluation at the identity equates the factors.
This removes the unnecessary finite-index premise and works for any `Sort`
of generators. Existing consumers retain the same conclusions.

The new support node remains `notready` while integration is pending. Exact
historical head `b930ce68ef139badc6010f56a307b527a3691f51` passed the
[hosted build](https://github.com/LionSR/TNLean/actions/runs/40919421992/job/123629836921):
the log records the matching `PR_HEAD_SHA`, a successful full build, and strict
`: ok` for the complete `TNLean/PEPS/CycleMPSChainArc.lean` module followed by
`All strict Lean checks passed`. Every reported applicable check succeeded.

The refreshed branch reconciles main
`c7d2992c89c16d85237e18557ff292979b3a67b4`, preserving the cancellation
module byte-for-byte and retaining main's chapter relocations. Fresh combined-head
hosted checks and integration remain open. No local Lean command was run,
following the user's instruction. This change does not close #7726 or claim
a complete signature audit of every multiple-anchor node.

## Remaining boundary

The dagger-inverse scalar node is not the same defect as the chain example:
its displayed statement expressly includes existence, the chosen gauge and
scalar, unit modulus, the inverse-pair identity, and the involutive sign.
Its multiple anchors therefore need an individual statement-to-signature
review, rather than deletion solely because there is more than one anchor.
Likewise, a global hypothesis checker is a separate unimplemented tooling
proposal; the existing synchronization check verifies references, not
mathematical equivalence of signatures and prose.

## Source checks

Mathlib source scouting confirmed `LinearMap.ext_on_range`, `mulLeft_apply`
and `mulRight_apply`. The neighboring trace-pairing proof already uses the
same extension theorem. Blueprint roles, reference synchronization, duplicate
reference ownership, pinned TeX formatting, ChkTeX, source width and diff
checks pass. No local Lean command or persistent proof fixture was used.
