# Blueprint Style Guide & Lessons Learned

## Core Philosophy
The blueprint is a **bridge between the mathematics and the Lean formalization**. A reader should be able to read a blueprint entry and immediately understand the corresponding Lean declaration. Conversely, someone reading the Lean code should find the blueprint proof sketch faithful to what the code actually does.

## General Principles
1. **Blueprint ↔ Lean must match.** Every `\lean{X}` tag must correspond to an actual Lean declaration. Every proof sketch must match what the Lean proof actually does — not a hand-wavy version of it.
2. **Standalone.** `blueprint/` and `slides/` are independent — no cross-references, no shared files. Each has its own macros, its own `references.bib`.
3. **Mathematical language only — zero Lean jargon.** No Lean identifiers in prose (no `evalWord_gauge`, no `mpvState(A, N)`, no `rintro ⟨X, hX⟩`). The `\lean{...}` tag is the link; the body text is standard mathematics. If you can't say it in math, rewrite it.
4. **No filler prose.** Only precise definitions, theorem statements, and proof sketches. No "this is important because..." or "the transfer map governs the spectral theory...".
5. **Cite non-trivial things.** Basic definitions (MPS tensor, MPV) don't need citations. Important results and non-obvious definitions should cite the source paper.
6. **Don't invent terminology or notation.** Don't create ad-hoc notation like `⟨·,·⟩^ip` when standard notation exists. Don't name things that the literature doesn't name. If Lean calls it `IsInjective`, the blueprint says "injective" — not "Condition C1".
7. **Match Lean's theorem/lemma/def exactly.** If Lean says `theorem X`, use `\begin{theorem}`. If Lean says `lemma X`, use `\begin{lemma}`. Never use `\begin{proposition}` (Lean has no `proposition` keyword). Label prefix: `thm:` for theorem, `lem:` for lemma, `def:` for definition.

## Proof Sketches Must Match Lean
This is the most important rule. Every proof in the blueprint must faithfully describe what the Lean proof does:

- **Reference the actual lemmas used.** If the Lean proof calls `evalWord_gauge`, the blueprint proof should say "By Lemma X.Y (word evaluation under conjugation)..." and list it in `\uses`.
- **Describe the actual proof structure.** If Lean does induction on `w`, say "By induction on the word $w$." If Lean uses a specific decomposition, name it.
- **Don't hand-wave where Lean is specific.** "Standard argument" is not acceptable if Lean uses three specific lemmas. Name them.
- **Don't be more specific than Lean.** If Lean uses `simp` to close a goal, a one-line sketch is fine.
- **`\uses` in proofs must be accurate.** Only list what the proof actually uses, not what the statement mentions. If the proof uses `lem:eval_word_gauge` but the statement mentions `def:gauge_equiv`, the proof's `\uses` should list the lemma, not the definition (unless the proof also directly unfolds the definition).

## Notation Consistency
Notation must be **internally consistent** across the entire blueprint and **close to what the Lean code expresses**:

- **Indices**: 0 to d−1 (matching `Fin d` in Lean), not 1 to d
- **Word evaluation**: $A^w$ for a word $w = (i_1, \ldots, i_L)$. The result is $A^{i_1} \cdots A^{i_L} \in \MN{D}$.
- **Word length**: $|w|$, never $L$ unless $L$ is a fixed blocking length in context.
- **MPV vector**: $\ket{V^{(N)}(A)}$ for the full ket vector.
- **MPV component**: $V^{(N)}(A)_\sigma = \tr(A^{i_1} \cdots A^{i_N})$ for a single coefficient.
- **Overlap**: $O_{AB}(N) = \sum_\sigma V^{(N)}(A)_\sigma \, \overline{V^{(N)}(B)_\sigma}$.
- **Inner product**: $\braket{V^{(N)}(A)}{V^{(N)}(B)}$ using the standard braket macro (conjugate-linear in first argument).
- **Transfer map**: $\E_A(X) = \sum_i A^i X (A^i)^\dagger$.
- **Blocked tensor**: $A^{[L]}$ with $(A^{[L]})^{(i_1,\ldots,i_L)} = A^{i_1} \cdots A^{i_L}$.
- **Flattened word**: $\widetilde{w}$ for a word in the original alphabet obtained by decoding blocked indices.
- **Canonical form scaling**: $\mu_k$ for the scaling factors, $A^i = \bigoplus_k \mu_k A_k^i$.
- **System size**: $N$ (reserved). **Blocking length**: $L$ or $L_0$.
- **Collections**: curly brackets `\{A^i\}_{i=0}^{d-1}`, not parentheses.
- **DeclareMathOperator subscripts**: always use braces: `\spn_{\C}` not `\spn_\C`.
- **Macros** (in `macros/common.tex`): `\C`, `\R`, `\N`, `\Z`, `\E`, `\Id`, `\MD`, `\MN{D}`, `\GL`, `\tr`, `\spn`, `\ket{·}`, `\bra{·}`, `\braket{·}{·}`, `\ketbra{·}{·}`, `\mc{·}`

## What NOT to Put in the Blueprint
- **Lean identifier names in math text.** Write "the word evaluation $A^w$", never "the `evalWord` of $A$" or "$\mathrm{evalWord}(A, w)$". The `\lean{MPSTensor.evalWord}` tag handles the linking.
- **Implementation details.** Don't say "bundled as an element of the Euclidean space" or "using `EuclideanSpace.equiv`". Describe the mathematical object.
- **Ad-hoc notation.** Don't invent superscripts like $\langle \cdot, \cdot \rangle^{\mathrm{ip}}$ to distinguish from existing notation. Use standard conventions or define new notation explicitly if truly needed.
- **Function-call syntax.** Don't write $\mathrm{mpv}(A^{[L]}, \sigma)$. Write $V^{(N)}(A^{[L]})_\sigma$ using the established component notation.
- **Redundant definitions.** If two blueprint definitions describe the same mathematical object (e.g., MPV as a ket vector vs MPV as a Hilbert-space element), make one a remark or consolidate them. Each definition should introduce genuinely new mathematical content.
- **Lean namespace prefixes in prose.** Don't write "the `MPSTensor.transferMap`" — write "the transfer map $\E_A$".

## Banned AI/Software Language (enforced in both blueprint AND Lean code)
The blueprint reads as a **mathematical document**, not software documentation. The following patterns are banned in ALL reader-facing text (section titles, theorem names, proof sketches, remarks, chapter preambles) and in ALL Lean docstrings, comments, and section names:

### Banned software-engineering terms → replacements:
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

### Banned LLM writing patterns → replacements:
These are overused phrases typical of LLM output; they add no mathematical content and must not appear in the blueprint, Lean docstrings, or commit/PR prose:

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

### Additional rules:
- **"Assembly" in Lean identifiers**: acceptable ONLY for `wielandt_blocked_assembly` and similar mathematical theorem names where "assembly" describes the mathematical step (assembling rank-one elements). NOT acceptable for file-organizational names.
- **"Assembly" in file names**: `Assembly.lean` and `QPF/Assembly.lean` are grandfathered (renaming cascades through too many imports). New files should use mathematical names.
- **Section names in Lean**: use mathematical terms (`section PerronFrobenius`, `section GaugeConstruction`, `section FinalConstruction`), not organizational terms (`section Assembly`, `section Pipeline`).
- **Internal LaTeX labels** (e.g., `\label{ch:assembly}`, `\label{thm:pipeline_handoff}`) are not reader-facing and need not be renamed if doing so would break cross-references. But NEW labels should follow the standard.
- **Definitions that are actually theorems**: if a statement asserts a mathematical fact (e.g., "X is a subalgebra"), it must be `\begin{theorem}`, not `\begin{definition}`. Definitions introduce new objects; theorems prove properties.

## `\uses` Dependency Guidelines
- **Statement `\uses`**: list only what's needed to *state* the result (typically definitions of the objects involved). Keep minimal — transitive deps are automatic.
- **Proof `\uses`**: list only what the proof *actually calls*. If the Lean proof uses `lem:eval_word_gauge`, list it. Don't list `def:gauge_equiv` unless the proof unfolds that definition.
- **Never self-reference**: a proof's `\uses` must NOT include the label of the theorem it proves.
- **Hypotheses vs definitions**: If a Lean lemma takes a pointwise hypothesis (like `∀ i, B i = X * A i * X⁻¹`) rather than a bundled structure (like `GaugeEquiv A B`), the blueprint statement's `\uses` should NOT list the bundled definition — the lemma is more general than that.

## Blueprint Structure
- `content.tex` is a router: `\input{chapter/ch01_intro}` etc.
- Each chapter is a separate file in `chapter/`
- Definitions/theorems numbered within chapters: `\newtheorem{theorem}{Theorem}[chapter]`

## Lean Blueprint Macros
- `\lean{Namespace.DeclName}` — links to Lean declaration
- `\leanok` — marks definition/theorem/proof as fully formalized
- `\uses{label1, label2}` — declares dependency edges for the graph
- `\notready` — marks as not ready for formalization (orange in graph)
- `\mathlibok` — already in Mathlib (dark green in graph)

## Dependency Graph Colors (web)
- **Light green box**: definition with `\lean` + `\leanok` (defined in Lean)
- **Green**: theorem stated + `\lean` + `\leanok` (stated in Lean)
- **Dark green**: theorem with proof also `\leanok` (fully proved)
- **Blue**: ready to state/prove (all deps are done)
- **Orange**: `\notready` (needs more blueprint work)

## Bibliography Workflow
1. Edit `blueprint/src/references.bib` (standalone, AuthorYYYYKeyword keys)
2. Run `cd blueprint/src && latexmk -lualatex -interaction=nonstopmode print.tex` (generates `print.bbl`)
3. Copy `blueprint/src/print.bbl` → `blueprint/src/web.bbl`  ← **must do this every time bib changes**
4. Run `leanblueprint web` (plasTeX reads `web.bbl`)
5. Citation key format: e.g., `Cirac2021Matrix`, `PerezGarcia2007Matrix`

## Stale/Corrupt Aux File Recovery
If LaTeX reports `! File ended while scanning use of \@newl@bel` on startup:
- The `.aux` file was truncated by a previous killed/timed-out run
- Fix: `rm -f blueprint/src/print.aux blueprint/print/print.aux blueprint/print.aux`
- Then rerun latexmk — it rebuilds the aux from scratch cleanly
- After rebuild, copy fresh `print.bbl` → `web.bbl`

## Build Commands
```bash
leanblueprint pdf     # PDF → blueprint/print/print.pdf
leanblueprint web     # HTML → blueprint/web/
leanblueprint serve   # local server at http://0.0.0.0:8000/
leanblueprint all     # pdf + web + checkdecls
```

## Fact-Check Lessons
- **Ch 2**: `mpv` in Lean returns a scalar (the σ-component), NOT a ket vector. The ket is `mpvState`. Blueprint presents the ket form (standard physics) but `\lean{MPSTensor.mpv}` points to the component function — this is acceptable as long as it's clear.
- **Ch 2**: Overlap and inner product differ by conjugation. Lean: `mpvOverlap A B N = star (mpvInner A B N)`. The overlap sums $V_\sigma \overline{W_\sigma}$; the inner product sums $\overline{V_\sigma} W_\sigma$.
- **Ch 4**: KS inequality is for UNITAL maps, not TP. HS contraction requires BOTH.
- **Ch 4**: `kraus_commute_of_ks_equality` proves $X K_i^\dagger = K_i^\dagger E(X)$, not Kraus commutation with a unitary.
- **Ch 4**: Wolf citations: Eq (5.2) for KS; Prop 6.1 spectral radius; Prop 6.2 trivial Jordan; Thm 6.6 irreducibility; Prop 6.8 Hermitian FP; Thm 6.11 primitive; Thm 6.13 Cesàro.
