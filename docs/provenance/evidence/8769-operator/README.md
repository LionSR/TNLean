# Distributed operator contraction evidence

This packet constructs an identity-bond tensor network on the actual tagged
distributed star/sample links and proves its exact weighted branch/sample
evaluation. It supports arbitrary supplied rectangular local operators, shared
complete ket/bra labels, once-root coefficients, singleton gates, empty alphabets
and empty link families. It supplies the algebraic operator representation step
of Theorem 5.2.

The actual circuit-to-local-operator identification, uniform polynomial label
families, source correction expansion, probabilistic error bounds and composition
into the full theorem remain open. Human maintainer mathematical review is pending.

## Immutable revisions

- Original reviewed proof: `ac065a663f42d97e160a223b868ce162fe0c7d7f`.
- Notice-bearing compiled proof: `a89886d64e31b363c8dde1411410af3cd9b5ef66`.
- Proof SHA-256: `5fcab299dd3f163a4a1d234a25a51b91ae49bcd6619202731d471a82d2046dab`.
- Original proof SHA-256: `ba76d9c18cdbc7ab07303d8a826e4fad0874e472323767e42863fd49f8242fd4`.
- Paper: September 24, 2026, `thm:compression`,
  [`04-compression.tex:565–588`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L565-L588).
- Provenance policy: PR #8789, `4e9d9c898a4401d51cf1eeeabcea8572242387fe`.

The 731-line module contains 49 compact original provenance notices. Removing
those notices reproduces the reviewed mathematical source byte for byte.
The later chapter-ending whitespace change at
`cb46263506014207a236393c306bf751e2e7500f` leaves the proof and audit files unchanged.
Final metadata records individual check revisions; verification rows retain the
exact notice-bearing proof revision above.

## Checked coverage

All 49 public declarations occur exactly once in the compiled kernel audit and
exactly once in the 34-entry blueprint chapter. The complete audit uses only
`propext`, `Classical.choice`, and `Quot.sound`.

The clean module and generated aggregate build completed 2654 jobs in 7.049 seconds
with zero warnings. The strict audit and eight regression examples use
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
`linter.mathlibStandardSet=true`, and `warningAsError=true`. The audit script
permits its intentional `#print axioms` commands with `linter.hashCommand=false`;
production modules have no additional linter exceptions.

The regressions cover an empty heterogeneous rectangular circuit, a singleton
gate with no branch labels, genuine zero-sample pair positions, singleton 2×3
ket/bra labels, complex bra conjugation with once-root weight 1/2, repeated gate
occurrences with parallel star/sample links, and exact star/sample dimensions.

The 20 final checks in [checks.json](checks.json) all exited zero with no warnings.
They include full text style, generated imports, module size/names, whole-blueprint
synchronization, whole-blueprint LaTeX formatting and standalone TeX/BibTeX.
After removing an extra final blank line from the new chapter, its formatting and
final branch whitespace checks were rerun. The final standalone chapter has no
undefined citations or references and no overfull boxes. Its source and PDF are
[smoke.tex](smoke.tex) and [smoke.pdf](smoke.pdf).

Each log records command, working directory, source revision, UTC start, elapsed
time, exit code and warning count. [proof-report.json](proof-report.json) records
the source hash, complete check manifest and remaining mathematical obligations.
[original-ac065a6/](original-ac065a6/) preserves the original owner report and all
five original checked log byte streams, including the complete 49-name audit.

## Provenance and reproduction

Every new declaration is an original formalization of the pinned paper; no
upstream OpenAI Lean proof text was reused. The new shard is
`docs/provenance/openai-math.d/8769-operator.json`. The historical 47-declaration
shard and historical proof sources are unchanged.

The pinned validator checks both issue-owned shards together: all 96 declarations
pass notice/schema, immutable proof-byte, log-hash and allowed-axiom validation.
[policy-snapshot.json](policy-snapshot.json) records the schema and validator hashes
and Git blob IDs, authenticated against the exact policy revision through GitHub's
contents API. No policy or schema files were installed or changed in this branch.

From a TNLean checkout with the recorded commits and Lean dependencies available:

```sh
lake build TNLean.PEPS.Approximation.DistributedOperatorContraction \
  TNLean.PEPS.Approximation
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true \
  scripts/distributed_operator_contraction_axioms.lean
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true \
  scripts/distributed_operator_contraction_regression.lean
python3 scripts/check_distributed_operator_blueprint.py --upstream-root /path/to/openai-math
python3 docs/provenance/evidence/8769-operator/check-proof-evidence.py
python3 docs/provenance/evidence/8769-operator/validate-provenance.py \
  --policy-root /path/to/policy-at-4e9d9c8 --upstream-root /path/to/openai-math
```

The official Mathlib import-closure preflights are preserved in
[cache-preflight/](cache-preflight/). Dependencies were reused from this worktree's
independent cache. The style executable links generated C objects after its
Mathlib Lean import preflight; no missing Mathlib Lean module was source-built.

Separate Codex agents reviewed the complete mathematical source and blueprint,
and directly inspected the notice-bearing build, all 49 compiled audit records
and all eight strict regressions. This automated review does not replace the
pending human maintainer review. Assisted-by: OpenAI Codex (GPT-6).
