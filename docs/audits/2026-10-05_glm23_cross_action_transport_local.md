# Local GLM23 cross-endpoint action-tree transport

## Scope

This is an unpublished preparatory proof step for the actual mixed endpoint
operator construction in GLM23, `Papers/2203.12563/REsubmission.tex`,
lines 1667–1685, using the actual action-tree comparison at lines 491–552.
The source-aligned endpoint fusion and action maps are retained.

The new module is `TNLean/MPS/MPDO/BoundaryActionCrossTransport.lean`.
The isolated base is commit `e48a690228fd9ddca4251e9e49929753365f31ca`,
whose tree is `d6f434e01a5c16701fd4abf0b19514e70abc7c31`.
No import router, workflow, or blueprint is changed.

## Assumptions and derivation

- The general synthesis API assumes exact biorthogonal fusion and action
  decompositions, normal positive-dimensional target blocks, and a positive
  simultaneous target-word span. It derives `S_sequential L = S_fusion`
  from the third conjunct of `fullActionComparison_spec` and the existing
  block-diagonal description of the actual comparison matrix.
- The single-state specialization takes actual exact biorthogonal endpoint
  data, a positive-dimensional injective state, and common fusion/action
  multiplicities. `Fin 1` state labels and the existing simultaneous-span
  theorem supply the normality and span premises internally.
- The crossed theorem accepts two such endpoints, with independent physical
  dimensions and independent operator and state bond dimensions. It assumes
  equality of the actual raw L matrices for the chosen operator labels
  `(a,b)`. For every rectangular `X : Matrix (Fin D₀) (Fin D₁) ℂ`, it proves
  `Σ_p S_sequential,0(p) X H_sequential,1(p) =
   Σ_q S_fusion,0(q) X H_fusion,1(q)`.
- The proof inserts `H_sequential,1 = L₁ H_fusion,1`, transfers coefficients
  across the rectangular matrix using `L₀ = L₁`, interchanges finite sums,
  and uses `S_sequential,0 L₀ = S_fusion,0`. It never uses an inverse L.
- The coordinate corollary uses the four existing actual tree-entry
  formulas. The regression test swaps endpoints and transposes arbitrary
  rectangular `X`, checking the reverse cross sector.

No common F matrix, operator injectivity, equal endpoint dimensions,
entrywise nonzero L coefficients, tree-equality hypothesis, or new
abstract structure is introduced. Empty multiplicity spaces remain allowed.

## Remaining scope

This module does not prove that equality of gauge classes supplies the
chosen common raw L matrix. It does not yet construct or verify the actual
mixed operator's fusion tensors, establish their F symbols, or prove mixed
operator injectivity or whole-path symmetry. Those are distinct subsequent
steps; this local contraction must not be advertised as the full source
mixed-MPO construction.

## Validation

The complete module and reverse-sector test passed a strict no-artifact
combined-source probe on 2026-10-05, exit code 0 at 23:52:02 UTC. That run
checked all four public theorems, the private rectangular-sandwich lemma,
the reverse-sector example, and the first three standard-axiom guards.
The fourth theorem's printed dependency audit also contained exactly
`propext`, `Classical.choice`, and `Quot.sound`. Its matching guard was
added afterward. The final four-guard repeat passed with exit code 0 on
2026-10-06 at 00:24:15 UTC, with no Lean diagnostics. The complete source,
reverse-sector example, and all four guards are therefore checked together.

The final probe concatenates the exact complete proof source with the test
source after removing only its import of that proof module. This avoids
creating an `.olean` while still elaborating the complete new proof and
regression contents together. It is **full-source verification**, not a
prefix-only result. It is not a Lake package build or a check of the future
compiled import edge; routers, generated imports, and blueprint checks
were deliberately outside this local task.

The three earlier exit-1 runs are not counted as complete checks. The third
one did establish the core declarations with standard axioms, but still
failed at the optional coordinate corollary. The later exit-0 full run
superseded that partial evidence.

All runs used the canonical warmed dependency path, `LEAN_NUM_THREADS=1`,
and strict options `relaxedAutoImplicit=false`, `pp.unicode.fun=true`,
`weak.linter.mathlibStandardSet=true`, `maxSynthPendingDepth=3`, and
`warningAsError=true`. The first successful run additionally limited only
diagnostic pretty-print depth and steps; it did not alter proof heartbeat
or recursion limits. The final guard run uses only the listed strict
options. No Lake build, cache operation, artifact-output flag, installation,
or canonical source/build-cache write was performed. No `.olean`, `.ilean`,
or generated C file exists in this isolated worktree.

Static checks found no forbidden proof tokens or lines over 100 columns,
and the two-file tactic-pattern scan found no repeated tactic patterns at
its default thresholds. The directly relevant canonical action-tree,
comparison, entry, L-matrix, and reindexing sources match the base sources
byte-for-byte.

## Artifact identity

There are four public theorems, one private matrix-evaluation lemma, one
reverse-sector regression example, and four standard-axiom guards. There
are no new definitions, structures, or assumed coherence packages.

SHA-256:

- Proof module: `cd02c5f12494247cb1ca38eea66275c64a758c30885a41d1660710324b5dce47`
- Regression test: `4e86bd233bffc3651402a9a3c021abf67fb687b49c29a07dcda11d1c257a0210`
- Exact final concatenated probe: `5736e6d9172d889e95989f98da818a93e83e31953cb736bc96a7689b090b4bc6`

The persisted local evidence is
`/workspace/shared/glm23-cross-action-transport-probe4.log` with its `.exit`
file and `/workspace/shared/glm23-cross-action-transport-final-probe.log`
with its separately written `.exit` file. Both exit files contain `0`.
The isolated worktree is
`/workspace/shared/TNLean-glm23-cross-action-tree`, branch
`feat/glm23-cross-action-tree`. Publication is intentionally deferred until
this result is integrated with actual mixed-fusion assembly.
