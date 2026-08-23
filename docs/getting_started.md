# Getting started

This page is the onboarding path for a mathematician or Lean user arriving at
TNLean for the first time. It gets the library building, orients you in the
source tree, and points to the conventions you need before opening a pull
request. It complements `CLAUDE.md`, which is written for AI coding agents;
this page is written for you.

Before writing code, read
[`.github/CONTRIBUTION_POLICY.md`](../.github/CONTRIBUTION_POLICY.md). Code
contributions are scoped to an assigned issue and require working knowledge of
quantum information theory and tensor networks. Issues and corrections are
welcome from anyone. Unsolicited agent-generated pull requests from accounts
with no prior contribution are closed without review; other unsolicited pull
requests are read, but their authors should expect to be asked to open an issue
first.

## 1. What you need

- **elan**, the Lean version manager. Once it is installed, running any Lean
  command inside the repository installs the toolchain pinned in
  `lean-toolchain` (`leanprover/lean4:v4.34.0-rc1`) automatically — you do not
  need to install Lean yourself or match a version by hand.
- **VS Code** with the Lean 4 extension. This is what the project is
  developed with; it gives you the interactive goal view, hover information,
  and jump-to-definition you need to read and write proofs. Other editors
  with an LSP client (Emacs, Neovim, Helix) can also work with Lean's
  language server, but the extension is the path most contributors use and
  the one these instructions assume.
- **git**.
- **Python 3** and **ripgrep** (`rg`), which are used by the local checks below.
- **About 10 GB of free disk**, mostly for the downloaded Mathlib build
  artifacts and the `.lake` directory; a full local build with cache is
  closer to 20 GB.

## 2. Build the library

Clone the repository and fetch the prebuilt Mathlib artifacts before doing
anything else:

```bash
git clone https://github.com/LionSR/TNLean.git
cd TNLean

# Download pre-built Mathlib artifacts. Do this before any build.
lake exe cache get
```

> **Why this order matters.** `lake exe cache get` downloads Mathlib's
> compiled `.olean` files instead of compiling Mathlib from source. If you
> skip it and run `lake build` directly, Lake will not find prebuilt
> Mathlib artifacts and will compile the entire Mathlib library locally —
> a build that takes hours instead of minutes. Always run `cache get`
> first, and again after any Lean/Mathlib toolchain update.

Then build:

```bash
lake build
```

What to expect: Mathlib itself comes from the cache and does not recompile.
TNLean's own several-hundred modules are not distributed as a cache and
compile locally; a full build takes a while the first time (subsequent
builds only recompile what you changed). `lake build` with no arguments
builds the default target, which is the whole `TNLean` library; you can also
build just the library with `lake build TNLean`. To verify one module with the
package's Lean options, including the Mathlib standard linter set, run:

```bash
lake build TNLean.MPS.FundamentalTheorem.Basic
```

For a faster elaboration check that does not apply those package options or
run the standard linter set, use:

```bash
lake env lean TNLean/MPS/FundamentalTheorem/Basic.lean
```

Once the build succeeds, open the repository folder in VS Code
(`code .`). The Lean 4 extension will start the language server; open any
`.lean` file, click into a proof, and the goal panel should show you the
proof state at the cursor. If it does not, check the extension's output panel
— a stale or partial build is the usual cause (see
[Troubleshooting](#6-troubleshooting)).

## 3. Find your way around

### The layer map

The source under `TNLean/` is organized into numbered conceptual layers, each
importable only from the ones before it. The quantum-channel foundations that
formerly occupied the lower layers (`Channel`, `Entropy`, `Kraus`, `QPF`, and
the supporting `Analysis` and `Topology` material) now live in the companion
[QICLean](https://github.com/LionSR/QICLean) library, which TNLean imports as
an ordinary Lake dependency. The full table, including the finer sublayers, is
in [`docs/import_structure.md`](import_structure.md); in outline:

| Layer | Directories | Content |
|---|---|---|
| 0 – 1 | `Algebra` | Matrix algebra: trace pairings, Gram matrices, block-triangular traces, cocycle cohomology. |
| 2 | `Spectral` | Transfer-operator spectral gaps and correlation/overlap decay. |
| 3 | `MPS/Core`, `MPS/Chain`, `MPS/Overlap` | Blocking, multi-block words, transfer-matrix analysis, and overlap matrices for matrix product tensors. |
| 3b | `MPS/MPDO` | Matrix-product density operator foundations. |
| 4 | `MPS/FundamentalTheorem`, `MPS/Symmetry` | The single-block fundamental theorem, gauge equivalence, on-site and virtual symmetries. |
| 5 | `MPS/BNT`, `MPS/CanonicalForm`, `MPS/Irreducible`, `MPS/Periodic`, `MPS/Structure` | Multi-block canonical forms and the general fundamental theorem. |
| 5b | `MPS/RFP` | Renormalization fixed points. |
| 6 | `Wielandt` | The quantum Wielandt inequality and primitivity. |

`PiAlgebra` carries algebraic variants of the fundamental theorem, `PEPS` the
two-dimensional generalization, `QCA` quantum cellular automata on spin
chains, and `MPS/ParentHamiltonian`, `MPS/Examples` the parent-Hamiltonian
and worked-example material. Everything lives under a single import surface,
`TNLean.lean`, which is generated by
`scripts/generate_import_aggregators.py` — never edit it or the directory
aggregators by hand.

### Key definitions

A handful of names recur throughout the library and are worth knowing before
you start reading. The finite-family definitions live in the companion QICLean
library under the `Kraus` namespace, while TNLean retains the
matrix-product-state vocabulary in `TNLean/MPS/Defs.lean`:

| Name | What it is | Defined in |
|---|---|---|
| `MPSTensor d D` | A `Fin d`-indexed family of `D × D` complex matrices — the tensor `A^i` of a matrix product state. | `QICLean/Kraus/Word.lean` |
| `Kraus.evalWord` | The matrix product `A_{i_1} A_{i_2} \cdots A_{i_n}` along a word of physical indices. | `QICLean/Kraus/Word.lean` |
| `Kraus.IsInjective` | The matrices of a tensor span the full matrix algebra. | `QICLean/Kraus/Injectivity.lean` |
| `Kraus.IsNormal` | The tensor becomes injective after blocking sites (eventual full Kraus rank). | `QICLean/Kraus/Injectivity.lean` |
| `Kraus.transferMap` | The completely positive map $E_A(X) = \sum_i A_i X A_i^\dagger$. | `QICLean/Kraus/Transfer.lean` |
| `MPSTensor.SameMPV` / `MPSTensor.GaugeEquiv` | Two tensors generate the same states at every system size / are related by conjugation `B i = X * A i * X⁻¹`. | `TNLean/MPS/Defs.lean` |
| `fundamentalTheorem_singleBlock` | The single-block fundamental theorem: injective + same states implies gauge equivalent. | `TNLean/MPS/FundamentalTheorem/Basic.lean` |

For anything not in this short list — what a predicate means, which source it
comes from, and which bridges between similarly named predicates are
sanctioned — check [`docs/glossary.md`](glossary.md) before assuming two
names are interchangeable; the library deliberately keeps several
source-faithful formulations of related ideas that are not aliases of one
another.

### The blueprint and the generated documentation

The [blueprint](https://sirui-lu.com/TNLean/blueprint/) is the
mathematical map of the library: it states every definition and theorem in
ordinary mathematical language and links each one to its Lean declaration.
Read it alongside the source rather than instead of it. It is also available
as a [full PDF](https://sirui-lu.com/TNLean/blueprint.pdf) and, for the
released fundamental-theorem material specifically, a
[separate PDF](https://sirui-lu.com/TNLean/blueprint-ch01-12.pdf). The
generated [API documentation](https://sirui-lu.com/TNLean/docs/) covers
every declaration in the Lean source with signatures and docstrings, and is
the fastest way to look up a lemma by name.

## 4. A first reading path

If your goal is to understand the fundamental theorem of matrix product
states, this is a concrete path through the source, in reading order,
alongside the corresponding blueprint chapters:

1. `QICLean/Kraus/Word.lean` (in the QICLean dependency) — `MPSTensor`,
   `Kraus.evalWord`. The basic objects: a tensor is a family of matrices,
   and a word evaluates to a matrix product.
2. `TNLean/MPS/Defs.lean` — `MPSTensor.mpv` (the matrix-product-vector
   coefficient), `MPSTensor.SameMPV`, `MPSTensor.GaugeEquiv`. What it means
   for two tensors to generate the same states, and what a gauge transformation
   is. Read alongside `blueprint/src/chapter/ch02_mps.tex`.
3. `QICLean/Kraus/Injectivity.lean` — `Kraus.IsInjective`, `Kraus.IsNormal`. The
   spanning condition the single-block theorem needs.
4. `TNLean/MPS/Structure/LinearExtension.lean` and
   `QICLean/Algebra/SkolemNoether.lean` — the two algebraic facts the proof
   assembles: the unique multiplicative linear extension taking `A` to `B`,
   and that every automorphism of a matrix algebra is inner.
5. `TNLean/MPS/FundamentalTheorem/Basic.lean` — `fundamentalTheorem_singleBlock`
   itself, built from the previous two files. Read alongside
   `blueprint/src/chapter/ch03_single.tex`, "The Single-Block Fundamental
   Theorem".

From there, `blueprint/src/chapter/ch09_canonical.tex` through
`ch11_fundamental_theorem_core.tex` and the corresponding
`TNLean/MPS/CanonicalForm/`, `TNLean/MPS/BNT/` source cover the general,
multi-block case.

## 5. Make your first change

Before opening a pull request, skim the conventions below; each links to the
document that spells it out in full.

**Naming.** Definitions are `camelCase`, predicates are named `IsFoo`,
theorems and lemmas are `snake_case`, and files are `CamelCase.lean`. The
full capitalization rules and the symbol-to-name dictionary (how to spell
`⊗`, `≤`, `⁻¹`, and so on in an identifier) are in the MATHLIB_naming
reference of the `lean-conventions` skill
([texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills)).

**Style.** Line length, variable-letter conventions (`A`, `B` for MPS
tensors, `E` for channels, `d`/`D` for physical/bond dimension), and tactic
formatting follow the skill's MATHLIB_style reference, with a small
number of project additions collected in
[`docs/CONTRIBUTING.md`](CONTRIBUTING.md#6-lean-code-style) and
[`docs/project_conventions.md`](project_conventions.md).

**Docstrings.** Every new `def`, `structure`, `class`, and significant
`theorem` needs a docstring, and every file needs a module header with a
`## Main definitions` list and a `## References` section citing the source
paper. The Markdown and LaTeX conventions for writing them are in the skill's
MATHLIB_doc reference.

**Proof integrity.** Finished work must not contain `sorry`, `admit`, or a
new `axiom`; a small set of other patterns (`native_decide`, unsafe casts,
disabled timeouts) are also blockers or warnings. The complete list, and what
counts as an acceptable exception, is in the skill's PROOF_INTEGRITY
reference (TNLean addenda: [`docs/project_conventions.md`](project_conventions.md)).

**Prose.** Docstrings, blueprint prose, issues, and pull request text should
read as mathematics, not software documentation: no Lean identifiers inside
blueprint prose, no software-engineering metaphors ("pipeline", "wrapper",
"boilerplate"), and none of the stock filler phrasing that AI writing tends
to reach for. The banned terms and their replacements are in the skill's prose_style
reference.

**Local checks.** Before pushing, run the checks relevant to the change:

```bash
# Elaborate one module with the package options and standard linter set.
lake build TNLean.Path.To.File

# Sorrys and axioms in the files you touched.
rg -n "sorry|axiom" TNLean/Path/To/File.lean || true

# Text-based style linter (whitespace, line endings, module naming).
lake exe lint_style

# Reader-facing prose patterns (tracker/label shorthand in docstrings, blueprint, etc.).
python3 scripts/check_reader_facing_prose.py --root . --diff-base origin/main

# If you touched the blueprint, after a successful `lake build`:
cd blueprint && leanblueprint checkdecls
```

**PR title.** `type(scope): short description`, where `type` is one of
`feat`, `fix`, `refactor`, `doc`, `style`, `ci`, `chore`, and `scope` is a
shortened module path with the `TNLean/` prefix dropped (`MPS/Symmetry`,
`Wielandt`, `blueprint+docgen`, …). The full convention, including the
required PR body sections (Motivation / Description / Testing), is in
[`docs/CONTRIBUTING.md`](CONTRIBUTING.md#1-pull-request-conventions).

**What CI runs.** Opening a pull request against a Lean or blueprint file
triggers a build with the Mathlib cache, the text-based style linter, and a
check that every `\lean{}` tag in the blueprint resolves
(`leanblueprint checkdecls`); touching blueprint sources additionally runs
the reader-facing prose check and a LaTeX lint. A separate automated review
pass then checks the diff against the Mathlib style guide and the proof
integrity rules above. The full list of workflows and what each one checks
is in [`docs/CONTRIBUTING.md`](CONTRIBUTING.md#7-ci--automation).

## 6. Troubleshooting

**A `lake build` that looks like it is compiling all of Mathlib.** You
skipped `lake exe cache get`, or ran it before a toolchain/Mathlib bump
invalidated the cache. Stop the build, run `lake exe cache get`, and build
again.

**Lean version mismatch.** elan reads `lean-toolchain` in the repository
root and switches automatically; you should not need to install or select a
Lean version by hand. If VS Code reports the wrong version, restart the Lean
server (`Lean 4: Restart Server` in the command palette) after confirming
`lean --version` at the command line matches the pinned toolchain.

**Stale build products after switching branches or pulling.** Lake usually
recompiles what changed, but a corrupted or half-written `.lake/build` can
produce confusing errors. `lake clean` removes local build output (Mathlib's
cached artifacts are untouched); rerun `lake build` afterward.

**Something else.** Open an issue on the
[GitHub issue tracker](https://github.com/LionSR/TNLean/issues).
