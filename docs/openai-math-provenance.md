# Provenance of the OpenAI mathematics ports

This is the review gate for #8737 and the September 24, 2026 area-law and
polynomial-PEPS program. It establishes attribution and evidence requirements;
it proves no mathematical result. Definitions, restricted regressions and
conditional statements do not complete either manuscript's headline theorem.
MPU gauging remains outside this program. Generic mathematics belongs in
QICLean; tensor and lattice mathematics belongs in TNLean. Keep dependency pins
unless a reviewed companion integration explicitly coordinates a change.

## Source and license audit

The only source baseline is
[`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
The audit record is [source-audit.json](provenance/source-audit.json).
[The preserved license](../LICENSES/openai-math-Apache-2.0.txt) is the upstream
root license, byte for byte; `lean/LICENSE` has the same SHA-256:
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
No tracked `NOTICE` or `NOTICE.*` exists at that revision (case-insensitive basename search).
The selected `VectorColumn.lean` and `PEPSFilters/Basic.lean` have no copyright or author header. An empty
`notices` array describes that file only. Never invent an author list,
copyright holder, upstream model, or a claim that other source files lack notices.

[Apache-2.0 §4(a)–(d)](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE#L89-L115)
requires a license copy, prominent notices of modifications, retention of
applicable copyright/patent/trademark/attribution notices, and handling of any
applicable NOTICE contents. Attribution alone does not discharge these duties.
Keep existing TNLean headers and References sections. Before each port, inspect
the selected transitive import closure, including third-party notices. Preserve
those notices verbatim in the relevant downstream source or distribution; record
source paths and text in `notices`. The audit of one module is not a closure audit.

## Ledger ownership and kinds

[The JSON Schema](provenance/openai-math.schema.json) is Draft 2020-12.
[The main ledger](provenance/openai-math.json) contains one real-source **planned**
phase-minimizer example. Its proposed QICLean path/name is not an implemented
port or a claim on the companion worker's task.

Parallel workers add `docs/provenance/openai-math.d/8738.json`, `8740.json`, etc.,
using the same `schema_version`, `source`, `entries` envelope. Keep each other's
rows and stable `id` values. The validator reads all shards and rejects duplicate
IDs or downstream `(repository, declaration)` keys across files, regardless of path
(GitHub repository names compare case-insensitively; Lean declaration names
remain case-sensitive). Update
only your rows; coordinate a shared declaration before moving its ownership.
A declaration with multiple sources needs separate reviewed source treatment;
do not create duplicate downstream keys to bypass this gate (schema extension
requires review). One row currently maps one source declaration.

| Kind | Meaning and required information |
| --- | --- |
| `copied` | Entire source module byte-identical. Upstream immutable repository/commit/path/declaration/lines/URL, license and retained notices required. Use an adjacent `.lean.provenance` comment-format notice so the source stays unchanged. Distribute the sidecar with the module. |
| `adapted` | Any source text reused with changes, including import, namespace, naming or header changes. Same immutable mapping, plus concrete modifications and an in-module notice. |
| `original` | Independently written from manuscript mathematics. `upstream: null`, `no_upstream_proof_text_reused: true`, manuscript version/path/labels, and a visible independence notice. No fictitious upstream Lean declaration. |
| `existing_library` | Use a Mathlib/QICLean result instead of importing an upstream proof. `library` records the exact replacement repository/commit/path/declaration/lines/URL; `downstream` identifies that library declaration. `upstream` may identify the replaced source result or be null. No new copied-code attribution is implied. |

Every row has `status`, `reuse_kind`, `upstream`, `downstream`, `paper_sources`,
`license`, `notices`, `changes`, and `verification`. `paper_sources` records the
September 24 version, repository-relative TeX path, and statement/equation
labels, independently of Lean reuse. For original/replacement rows the license
is the actual downstream/library license. Source references use full 40-digit
commit hashes and exact GitHub blob URLs with `#Lstart-Lend` (including a repeated
line for a one-line range).

`planned` means `verification: {"result": "pending"}` and proposed names.
`ported` means an implemented declaration with exact build and axiom evidence.
`replaced` means a verified existing-library replacement. `excluded` records a
decision and reason in `changes`, with pending verification; it is not completion
evidence. Empty strings,
unknown fields, paths escaping a repository and abbreviated commits are errors.

## Notices and evidence

The validator's in-module adapted notice template is:

```lean
/-!
Adapted from OpenAI's openai/math repository (Apache-2.0).
Provenance-ID: 8740-example-declaration
Upstream commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream file: <path>
Upstream declaration: <qualified declaration>
Upstream URL: <immutable URL with lines>
Downstream declaration: <qualified declaration>
Changes for TNLean/QICLean: <each exact changes-array string>
-/
```

Retain applicable original notices alongside this block. A module block may
contain several `Provenance-ID:` lines if it includes all mapped declarations,
links and changes. Use a declaration block when the source or reuse kind differs.
For an unchanged copy use `Copied from` in its sidecar. An original declaration
uses `Source: September 24, 2026, <paper path>, <labels>; independently formalized;
no upstream Lean proof text reused.` with its `Provenance-ID:` and downstream
qualified name. The text fixture `scripts/fixtures/openai_provenance/Adapted.lean.txt`
is a real-source adaptation example for validator tests, not a production port.

Completed rows use this evidence structure (placeholders are not valid hashes):

```json
{"result": "passed", "repository": "LionSR/TNLean", "revision": "<40 hex digits>",
 "commands": [
   {"kind": "build", "command": "lake build <module>", "exit_code": 0,
    "log": "docs/provenance/evidence/<build>.log", "sha256": "<64 hex digits>"},
   {"kind": "axioms", "command": "lake env lean <audit file>", "exit_code": 0,
    "log": "docs/provenance/evidence/<axioms>.log", "sha256": "<64 hex digits>"}
 ]}
```

Commit source modules first, build/audit that exact revision, then add evidence
and update only the corresponding ledger rows in a follow-up commit. This avoids
a self-referential commit hash. The validator compares the current module bytes
with the recorded revision, checks log hashes and exact quoted declaration names
in axiom output. Every record for that declaration must parse, agree, and use
only allowed foundational axioms. Keep raw Lean output in logs; timestamped or
unquoted paraphrases are not axiom evidence. Logs
must state command, revision, elapsed time and warnings; record failures as
pending rather than inventing success. Build using package options and the
repository cache-first protocol; `lake env lean` alone is not a linter-bearing
build. Audit every exported theorem's dependencies. No `sorry`, `admit`, custom
axiom, `unsafeCast`, or `native_decide` is permitted. Standard foundational
axioms `propext`, `Classical.choice`, `Quot.sound` are distinct from proof holes.

For QICLean-owned rows keep the module, notice, license, ledger and logs in
QICLean. TNLean links the reviewed companion commit and checks an explicitly
supplied companion checkout. It never treats a companion path as a TNLean file.
A replacement row must use the library commit as its verified revision and
match the consuming TNLean dependency pin; changing that pin needs the coordinated
companion review.

## Validation and review boundary

Install the validator dependency with `python3 -m pip install jsonschema==4.26.0`.
Run:

```sh
python3 -m unittest discover -s scripts -p 'test_openai_provenance.py' -v
python3 scripts/check_openai_provenance.py
python3 scripts/check_openai_provenance.py --upstream-root /path/to/openai-math
# Add companion roots when completed rows reference them:
python3 scripts/check_openai_provenance.py --upstream-root /path/to/openai-math \
  --repository-root LionSR/QICLean=/path/to/QICLean
```

The default check validates the planned ledger without downloading upstream.
Supplying `--upstream-root` reads immutable Git objects, checks source declaration
line ranges, manuscript labels and the recorded source/NOTICE audit, and compares
both upstream licenses. Completed reuse/replacement
rows require the applicable source roots. Ledger commands are evidence text;
the validator never executes them. CI must supply pinned checkouts when completed
ports are added; missing roots fail closed.

The source declaration index is a conservative lexical check for ordinary named
Lean commands and namespaces. It rejects missing names, comments masquerading as
declarations and inconsistent ranges. It is **not** an elaborator, proof checker,
source-copy detector, license-closure scanner, or confirmation of log authenticity.
Macros, generated declarations and unusual Lean syntax require explicit review
and validator extension. Review the actual build/axiom logs and dependency pins,
confirm paper hypotheses and notice retention, and check the closure independently.
When selected source bytes are available, opening copyright, license, author,
patent, trademark and attribution comments must appear in the retained-notice
ledger. This conservative header check does not determine legal applicability
or find all notices elsewhere in a source/import closure. Every copied/adapted
declaration still needs a ledger row. Exhaustive declaration coverage, including
original bridge proofs and generated declarations, remains a review obligation
rather than an automatic whole-module check.

Newly discovered source/header notices must be added; a validator pass never
licenses dropping them. Complete manuscript results remain open until faithful
proofs exist, irrespective of provenance status.

## Assistance and accountability

Upstream attribution and assistance disclosure are separate. Each implementation
PR names the actual tool and known model, which changes it produced, and the
accountable human contributor/reviewer under
[the contribution policy](../.github/CONTRIBUTION_POLICY.md).
Use `Assisted-by:` as appropriate; agents are not authors of record. Do not invent
a human review, authorship, or assignment. This policy/schema/validator batch is
assisted by OpenAI Codex (GPT-6); maintainer source and policy review is pending.
