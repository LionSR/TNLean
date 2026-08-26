# PEPS forwarder, mirror, and dead-definition retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for the PEPS subdirectories. Four
independent cleanups are covered: two forwarding lemmas with no independent
content, one theorem that was declared three times inside a single import
closure, two edge-incidence helpers that existed in three private copies, and
one definition with no consumer at all.

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.complementVertex_ne` (`TNLean/PEPS/VertexComplement/Basic.lean`) | `(mem_vertexComplementVertices_iff (V := V) v w).mp hw` — the `@[simp]` iff in the same file, carrying the same `omit [DecidableRel G.Adj]` |
| `TNLean.PEPS.gauge_sum_left_right` (private, `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean`) | inlined into `TNLean.PEPS.gauge_sum_left_right_matrix_inv`, its only consumer |
| `TNLean.PEPS.IsVertexInjective.localCoeff_eq_zero_of_contract_zero` (`TNLean/PEPS/EdgeMiddlePhysical/Basic.lean` and `TNLean/PEPS/VertexComplement/Basic.lean`) | the single declaration of the same name in `TNLean/PEPS/VirtualInsertion.lean`, the common ancestor of both files |
| `TNLean.PEPS.otherLeft_edge_ne'` and `TNLean.PEPS.otherRight_edge_ne'` (private, `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean` and `TNLean/PEPS/EdgeMiddlePhysical/KernelDescent.lean`) | `TNLean.PEPS.otherLeft_edge_ne` and `TNLean.PEPS.otherRight_edge_ne` in `TNLean/PEPS/Blocking.lean`, now public |
| `TNLean.PEPS.localTensorEval` (`TNLean/PEPS/FundamentalTheorem/LocalGaugeExtraction.lean`) | none — zero consumers; the local tensor map that the file actually uses is `localTensorMap` in `TNLean/PEPS/VirtualInsertion.lean` |

## What was checked

**Forwarding lemmas.** `complementVertex_ne` had zero references repository-wide
and its proof was the single term now written at any future use site. The
private `gauge_sum_left_right` had exactly one consumer,
`gauge_sum_left_right_matrix_inv`, which differed only in whether the inverse is
written on the group or on the matrix; the coercion rewrite that bridged them is
now the first line of the surviving proof, leaving the rest of the argument
untouched. The survivor keeps its name, statement, and docstring, so its four
consumers in `GaugeAction.lean`, `RegionBlock/GaugeInjectivity.lean`, and
`FundamentalTheorem/EdgeInsertion.lean` are unchanged.

**Triplicated coefficient lemma.** The statement and proof of
`IsVertexInjective.localCoeff_eq_zero_of_contract_zero` appeared in
`EdgeMiddlePhysical/Basic.lean` and `VertexComplement/Basic.lean`, which both
import `TNLean.PEPS.Blocking` and so both import `TNLean.PEPS.VirtualInsertion`.
The declaration moved to that common ancestor, immediately after
`IsVertexInjective.localTensorMap_injective`, which is the only fact its proof
uses; the fuller of the two docstrings survives. The fully qualified name is
unchanged, so the three uses in `FundamentalTheorem.lean`,
`RegionBlock/KernelDescent.lean`, and `EdgeMiddlePhysical/KernelDescent.lean`
resolve as before, and the `\lean{...}` tag at
`blueprint/src/chapter/ch24_peps_ft_foundations.tex` still names a declaration
that exists.

**Edge-incidence helpers.** `Blocking.lean` owned both facts but hid them behind
`private`, so two downstream modules restated them under primed names. The
`Blocking.lean` originals are now public and carry the docstrings that the
`GaugeAction.lean` copies had; the seventeen primed call sites in the two
downstream files were renamed to the unprimed spellings, which resolve without
qualification since both files open `namespace TNLean.PEPS`. No file outside
`TNLean/PEPS` referenced either name, and neither `blueprint/src` nor `docs`
mentions them.

**Dead definition.** `localTensorEval` had no Lean consumer: the only occurrence
of the name in `TNLean` was its own definition. Its blueprint node
`def:localTensorEval` was a leaf — no `\uses{def:localTensorEval}` exists
anywhere under `blueprint/src` — so the node is deleted rather than redirected,
and `\leanok` coverage for chapter 24 drops by one definition. The dated audit
snapshot `blueprint/comments/20260407/ch13_lean_audit.md` still names the
declaration; it is a historical record and was left alone.

## Transition declarations

Every removed name is either `private`, zero-referenced, or a byte-level mirror
of a surviving declaration with the same fully qualified name, and no surviving
blueprint `\lean{...}` tag cites a removed spelling. No deprecation alias is
warranted under the pass-through exception.

## Ledger

`complementVertex_ne` and `localTensorEval` are slices of ledger entry S2
(zero-reference declarations, issue #4564); an evidence line records them there.
