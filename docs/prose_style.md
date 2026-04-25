# Prose Style Guide

This document specifies the prose conventions for **all reader-facing text in TNLean**.
It is the authoritative source for:

1. The "no Lean jargon in the leanblueprint" rule.
2. The banned software-engineering vocabulary.
3. The banned LLM writing patterns.

It extends — and does not replace — the general mathlib-pasted documentation
guidance in [`doc.md`](doc.md) §"Doc strings" ("Doc strings should convey the
mathematical meaning of the definition") and [`style.md`](style.md) §"Comments".
Those files are upstream mathlib material and remain unmodified; the project-specific
extensions below are layered on top of them.

The dedicated `Blueprint Sync & Prose Review` CI workflow
(`.github/workflows/blueprint-prose-review.yml`) enforces this guide on every PR.

## Scope

**In scope** (these files are reviewed):

- Blueprint `.tex` files: section titles, theorem/definition/lemma names, proof
  sketches, remarks, chapter preambles, `references.bib` annotations.
- Lean source: `/-- ... -/` docstrings, `/-! ... -/` module/sectioning docs,
  `/- ... -/` block comments, `--` line comments, and `section`/`namespace` names.

**Out of scope** (do not flag):

- Developer-facing markdown in `docs/` and `README.md`.
- Workflow YAML, `lakefile.toml`, `lean-toolchain`.
- `Papers/`, `Notes/` (LaTeX sources of the underlying papers, not project prose).
- `Archive/` (legacy code, kept for reference).

---

## 1. No Lean jargon in the leanblueprint

The blueprint links the mathematics to its Lean formalization, but its prose must
read as standard mathematics. The `\lean{Namespace.Name}` tag is the
machine-readable link to the formalization; the surrounding prose must not mention
Lean identifiers, namespaces, or syntax. If a reader cannot follow the blueprint
without opening the `.lean` files, the prose has failed.

### Banned in blueprint prose

- **Lean identifier names.** Do not write "the `evalWord` of $A$", "the `mpvState`
  function", or `$\mathrm{evalWord}(A, w)$`. Write "the word evaluation $A^w$" and
  let `\lean{MPSTensor.evalWord}` carry the link.
- **Lean namespace prefixes.** Do not write "the `MPSTensor.transferMap`" or "we
  apply `Channel.Choi.toKraus`". Write "the transfer map $\mathcal{E}_A$" or "the
  Choi matrix yields a Kraus decomposition" and rely on the `\lean{...}` tag.
- **Tactic syntax in prose.** Do not write `rintro ⟨X, hX⟩`, `simp only [...]`,
  `apply?`, or `exact?`. Describe the proof step mathematically ("by induction on
  the word $w$", "rearranging the trace").
- **Implementation language.** Do not write "bundled as an element of the Euclidean
  space", "using `EuclideanSpace.equiv`", "stored as an extra field", or "via the
  `FunLike` API". Describe the mathematical object.
- **Function-call syntax with Lean naming.** Do not write `$\mathrm{mpv}(A^{[L]},
  \sigma)$`. Use established mathematical notation (e.g. `$V^{(N)}(A^{[L]})_\sigma$`).
- **Mathlib type names as prose.** Do not write "as a `MeasurableSpace`" or "by
  `Fintype` instance". Describe the structure mathematically.
- **Ad-hoc Lean-derived notation.** Do not invent superscripts like
  `$\langle \cdot, \cdot \rangle^{\mathrm{ip}}$` to disambiguate from another
  Lean-defined inner product. Use standard mathematical conventions; introduce new
  notation explicitly only when truly needed.
- **"Condition C1" / "Condition (1)" naming.** If Lean calls it `IsInjective`, the
  blueprint says "injective", not "Condition C1".

### Allowed in the blueprint

- `\lean{Namespace.Name}`, `\leanok`, `\uses{...}`, `\mathlibok`, `\notready` —
  these are blueprint markup, not prose. They do not count as "Lean jargon".
- Verbatim Lean snippets inside `\begin{verbatim}` or `lstlisting` environments,
  used sparingly when explicitly demonstrating the formalization. Prefer narrative.

### Allowed in Lean docstrings

- Mathematical descriptions of what the declaration means.
- Backticks around genuine Lean references (e.g. ``` `Fin d` ```, ``` `evalWord` ```)
  when explaining how to use the API of *this* declaration. Use sparingly — prefer
  mathematical phrasing.
- The other software/LLM bans in §2 and §3 still apply.

---

## 2. Banned software-engineering terms → replacements

Mathematical writing does not borrow framing from software documentation. Replace
the left column with the right when it appears in blueprint prose, Lean docstrings,
or section/namespace names.

| Banned | Use instead |
|--------|------------|
| "Assembly" (as section/chapter title) | "Proof of [theorem]", "Construction", "Composition" |
| "Pipeline" | "reduction", "construction", "proof chain" |
| "Bridge" (as noun for a connection) | "connection", name by mathematical content |
| "Handoff" / "hand off" | "transition", "continuation", or drop entirely |
| "In this blueprint" / "Within this blueprint" | "here", "in what follows", or omit |
| "Honest" (as adjective for rigorous) | "exact", "faithful", "unconditional", "complete" |
| "Glue layer" / "glue code" | "intermediate construction", "connecting results" |
| "Re-export" / "reexport" | "provides", "re-states" |
| "Wiring" / "wire up" | "connecting", "composing", "combining" |
| "Package" (as noun for a data bundle) | "form", "data", "structure" |
| "Stored as an extra field" | "appears as a separate assumption" |
| "Sorry-free" | acceptable only in Lean-specific technical context |
| "Physics-oriented" | describe the mathematical property instead |
| "[X] respects [Y]" (for equivariance) | "Multiplicativity of [X]", "[X] is equivariant under [Y]" |
| "Boilerplate" | "routine setup", "standard prelude", or drop |
| "Orchestrate" / "orchestration" | "combine", "compose", "arrange" |
| "Workflow" (for a proof procedure) | "procedure", "construction", or omit |
| "Plumbing" | "connecting results", "intermediate construction" |
| "Scaffolding" (for a proof skeleton) | name by mathematical content, "preliminary framework" |
| "Refactor" / "refactoring" (in prose) | "reorganize", "restate", "reformulate" |
| "Deploy" / "deployed" (a lemma) | "apply", "use", "invoke" |
| "Backend" / "frontend" | avoid entirely; name the mathematical object |
| "API" (in blueprint prose) | avoid; describe the interface mathematically |
| "Endpoint" (as software term) | avoid in blueprint prose |
| "Wrapper" / "thin wrapper" | "equivalent formulation", "reformulation" |
| "Hook" (as extension point) | "point of extension", or drop |
| "Toolchain" | never in blueprint prose |
| "Deprecate" / "deprecated" (in prose) | "supersede", "replace"; `@[deprecated]` tag is fine |
| "First-class" / "first-class citizen" | "directly representable", or drop |
| "Plug-and-play" / "drop-in" | "substitute", "replacement" |
| "Out of the box" | "directly", "immediately" |
| "Off-the-shelf" | drop or name the specific lemma |
| "Stack" (as in tech stack) | avoid; name the specific structure |
| "Harness" (as software harness) | "framework", or name by mathematical content |
| "Utility" (as noun) | "auxiliary lemma", "supporting result" |
| "Helper" (as noun) | "auxiliary lemma" |
| "Stub" / "stubbed out" | "placeholder", or remove |
| "Fixture" | never in blueprint prose |
| "Dependency injection" | avoid; describe the mathematical dependency |
| "Under the hood" | "internally", or drop |
| "End-to-end" (as software metaphor) | describe the mathematical chain |

---

## 3. Banned LLM writing patterns → replacements

These are overused phrases typical of LLM output; they add no mathematical content
and must not appear in the blueprint, Lean docstrings, or commit/PR prose.

| Banned | Use instead |
|--------|------------|
| "Leverage" / "leverages" | "use", "apply" |
| "Delve" / "delve into" | "examine", "study" |
| "Dive into" / "dive deep" | "examine", "analyze" |
| "Crucial" / "pivotal" / "vital" | "essential" or state the specific role |
| "Seamlessly" | drop |
| "Robust" (as vague adjective) | specify the property (e.g., "uniformly bounded") |
| "Comprehensive" / "thorough" (vague) | drop or be specific |
| "Navigate" (as metaphor) | use a plain verb |
| "Underscore" / "underscores the importance" | "emphasize", "highlight", or drop |
| "Tapestry" / "landscape" (as metaphor) | drop |
| "Journey" / "embark on" | drop |
| "Foster" (as metaphor) | "produce", "yield" |
| "Elevate" (as metaphor) | "generalize", "lift" |
| "Empower" | drop |
| "Game-changer" / "revolutionize" | drop |
| "Holistic" | drop or be specific |
| "Streamline" | "simplify" |
| "Synergy" / "synergies" | drop |
| "Actionable" / "actionable insights" | drop |
| "Meticulous" / "meticulously" | drop |
| "In the realm of" | "in", or name the field |
| "At the heart of" | "central to", "underlying" |
| "It's important to note that" | drop (pure filler) |
| "It is worth noting" / "worth mentioning" | drop |
| "Moreover" / "furthermore" (as filler) | "also", or drop |
| "In essence" / "essentially" (as filler) | drop |
| "Ultimately" (as filler) | drop |
| "Testament to" / "stands as a testament" | drop |
| "Rich" (as vague adjective) | specify the structure |
| "Powerful" (as vague adjective) | specify what it proves |
| "Elegant" / "beautiful" / "profound" | drop; let the math speak |
| "Insightful" / "provides insight" | drop |
| "Shed light on" | "explain", "clarify" |
| "Showcase" | "show", "present", "demonstrate" |
| "Unveil" / "reveal" (as narration) | "show", "prove" |
| "In summary" / "To conclude" / "In conclusion" (opening filler) | drop |
| "Cutting-edge" / "state-of-the-art" | drop |
| "Paradigm" / "paradigm shift" | drop |
| "This document" / "this note" (self-reference) | drop, or replace with the mathematical context |
| "We will see that" / "as we shall see" | drop; state the result directly |
| "Let us" / "let's" (as hortative filler) | drop or use imperative |

Several entries are **context-sensitive** and banned only as vague filler, not
categorically: "crucial", "pivotal", "vital", "moreover", "furthermore",
"essentially", "in essence", "ultimately", "meticulous", "let us". All have
legitimate mathematical uses. Apply judgment: flag the empty-calorie occurrences,
leave the genuine ones alone.

---

## 4. Additional rules

- **"Assembly" in Lean identifiers**: acceptable ONLY for `wielandt_blocked_assembly`
  and similar mathematical theorem names where "assembly" describes the mathematical
  step (assembling rank-one elements). NOT acceptable for file-organizational names.
- **"Assembly" in file names**: `Assembly.lean` and `QPF/Assembly.lean` are
  grandfathered (renaming cascades through too many imports). New files should use
  mathematical names.
- **Section names in Lean**: use mathematical terms (`section PerronFrobenius`,
  `section GaugeConstruction`, `section FinalConstruction`), not organizational
  terms (`section Assembly`, `section Pipeline`).
- **Internal LaTeX labels** (e.g. `\label{ch:assembly}`, `\label{thm:pipeline_handoff}`)
  are not reader-facing and need not be renamed if doing so would break
  cross-references. But NEW labels should follow the standard.
- **Definitions that are actually theorems**: if a statement asserts a mathematical
  fact (e.g. "X is a subalgebra"), it must be `\begin{theorem}`, not
  `\begin{definition}`. Definitions introduce new objects; theorems prove properties.

See `CLAUDE.md` for the full docs index.
