# PEPS forwarder, mirror, and dead-definition retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for the PEPS subdirectories. Seven
independent cleanups are covered: two forwarding lemmas with no independent
content, one theorem that was declared three times inside a single import
closure, three edge-incidence helpers that existed in private copies, one
definition with no consumer at all, two abbreviations of the same product type
declared in a single file, a private restatement of four helpers hidden behind
`private` in the file that owned them, and a wrapper around a Mathlib
definition.

| Audited declaration | Disposition / replacement |
|---|---|
| `TNLean.PEPS.complementVertex_ne` (`TNLean/PEPS/VertexComplement/Basic.lean`) | `(mem_vertexComplementVertices_iff (V := V) v w).mp hw` — the `@[simp]` iff in the same file, carrying the same `omit [DecidableRel G.Adj]` |
| `TNLean.PEPS.gauge_sum_left_right` (private, `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean`) | inlined into `TNLean.PEPS.gauge_sum_left_right_matrix_inv`, its only consumer |
| `TNLean.PEPS.IsVertexInjective.localCoeff_eq_zero_of_contract_zero` (`TNLean/PEPS/EdgeMiddlePhysical/Basic.lean` and `TNLean/PEPS/VertexComplement/Basic.lean`) | the single declaration of the same name in `TNLean/PEPS/VirtualInsertion.lean`, the common ancestor of both files |
| `TNLean.PEPS.otherLeft_edge_ne'` and `TNLean.PEPS.otherRight_edge_ne'` (private, `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean` and `TNLean/PEPS/EdgeMiddlePhysical/KernelDescent.lean`) | `TNLean.PEPS.otherLeft_edge_ne` and `TNLean.PEPS.otherRight_edge_ne` in `TNLean/PEPS/Blocking.lean`, now public |
| `TNLean.PEPS.localTensorEval` (`TNLean/PEPS/FundamentalTheorem/LocalGaugeExtraction.lean`) | none — zero consumers; the local tensor map that the file actually uses is `localTensorMap` in `TNLean/PEPS/VirtualInsertion.lean` |
| `TNLean.PEPS.edge_ne_of_middle_incident_for_physical` (`TNLean/PEPS/EdgeMiddlePhysical/Basic.lean`) and `TNLean.PEPS.incidentMiddle_ne` (`TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean`) | `TNLean.PEPS.edge_ne_of_middle_incident` in `TNLean/PEPS/Blocking.lean`, now public and carrying the `incidentMiddle_ne` docstring |
| `TNLean.PEPS.LocalConfig` (private, `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean`) | `TNLean.PEPS.OpenLocalConfig` in the same file — the two abbreviations unfolded to the same product type, and the public one keeps the fuller docstring |
| `TNLean.PEPS.edgeFinEqDelta` (private, `TNLean/PEPS/FundamentalTheorem/EdgeInsertion.lean`) | `TNLean.PEPS.finEqDelta (leftIncidentValue A ξ f) (rightIncidentValue A ξ f)`, the composition of three `GaugeAction.lean` helpers that are now public |
| `TNLean.PEPS.matrixUnit` (`TNLean/PEPS/TwoInjectiveComparison/Basic.lean`) | retained as a deprecated compatibility declaration; new code uses `Matrix.single i j (1 : ℂ)` from Mathlib directly |

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

A third private-hiding instance in the same closure was missed by that first
pass and is retired here. `Blocking.lean` also hid, behind `private`, the fact
that an edge incident to a middle vertex of `e` is not `e` itself; two
downstream modules restated it verbatim, one as
`edge_ne_of_middle_incident_for_physical` and one as `incidentMiddle_ne`. The
`Blocking.lean` original is now public and carries the docstring the
`CoarseThreeSite7.lean` copy had; the three call sites in
`EdgeMiddlePhysical/Basic.lean`, `EdgeMiddlePhysical/KernelDescent.lean`, and
`CoarseThreeSite7.lean` were renamed and resolve without qualification, all
three files having `TNLean.PEPS.Blocking` in their transitive import closure.
Neither retired spelling occurs under `blueprint/src` or `docs`, and
`_for_physical` was never referenced outside `TNLean/PEPS/EdgeMiddlePhysical/`.

**Dead definition.** `localTensorEval` had no Lean consumer: the only occurrence
of the name in `TNLean` was its own definition. Its blueprint node
`def:localTensorEval` was a leaf — no `\uses{def:localTensorEval}` exists
anywhere under `blueprint/src` — so the node is deleted rather than redirected,
and `\leanok` coverage for chapter 24 drops by one definition. The dated audit
snapshot `blueprint/comments/20260407/ch13_lean_audit.md` still names the
declaration; it is a historical record and was left alone.

**Edge-delta helpers.** This is the same shape as the `otherLeft_edge_ne'` row
above. `GaugeAction.lean` owned the endpoint readers of a local configuration
and the complex-valued Kronecker delta on a finite index type, but hid all four
declarations behind `private`, so `EdgeInsertion.lean` restated their
composition as a single private definition spelling out the `ite` and its
decidability instance by hand. The `GaugeAction.lean` originals —
`leftIncidentValue`, `rightIncidentValue`, `finEqDelta`, and `finEqDelta_eq` —
are now public and carry docstrings stating what each computes; the eight
`edgeFinEqDelta` call sites in `EdgeInsertion.lean` were rewritten to the
composition. One of those eight was a `have` restating `prod_off_delta_eq` only
to name the delta product in the private spelling; with the spellings unified it
collapses to the direct `rw [prod_off_delta_eq]` already used in
`OneVertexComparison.lean` and `GaugeBridge.lean`. The win is not the line count
but that a downstream file can now write the statement at all: with the
originals private, every open-edge delta statement outside `GaugeAction.lean`
had to be restated. Neither spelling occurs under `blueprint/src` or `docs`.

**Mathlib shadow.** `matrixUnit` is a two-line wrapper whose body is
`Matrix.single i j (1 : ℂ)`, and every one of its six former uses was accompanied by a
`simp` argument list that already named `Matrix.single` to unfold it. The uses
now name Mathlib's spelling directly, and the six argument lists shed the
redundant leading entry. Only `twoBlockInsertedCoeff_singletonBond_single`
needed the classical-instance opener that the wrapper had been supplying
implicitly. The old fully qualified name remains available as a deprecated
compatibility declaration for downstream users. The blueprint node
`def:peps_matrixUnit` is not a leaf — the one-shared-bond extraction theorem
cites it — so the label and the `\uses` edge stay and the tag is `\mathlibok`,
this repository's documented idiom for a statement discharged upstream. The
theorem name `twoBlockInsertedCoeff_matrixUnit` and the prose that describes
inserting matrix units are unchanged: they name the mathematics, not the
compatibility wrapper.

## Transition declarations

Every removed name is either `private`, zero-referenced, or a byte-level mirror
of a surviving declaration with the same fully qualified name. The distinct
public wrapper `matrixUnit` is instead retained under its exact former name and
signature with a deprecation pointing new code to `Matrix.single`. No surviving
blueprint `\lean{...}` tag cites a removed spelling; the compatibility retention
protects downstream Lean imports independently of the blueprint surface.

## Ledger

`complementVertex_ne` and `localTensorEval` are slices of ledger entry S2
(zero-reference declarations, issue #4564); an evidence line records them there.
