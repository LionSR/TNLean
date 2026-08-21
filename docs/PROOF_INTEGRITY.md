<!-- Canonical source: https://github.com/texra-ai/texra-lean-skills/blob/main/docs/PROOF_INTEGRITY.md
     This file is a stamped mirror: the body below this header is the shared
     canonical text; project-specific material lives only in the "Project
     addendum" section at the end. Edit the canonical file upstream and
     re-copy; edit only the addendum here. -->

# Lean Proof Integrity Rules

This file is the **single source of truth** for proof integrity checks in this
repository. All CI workflows and review prompts should reference this file
rather than duplicating the rules inline.

> **Lean version**: 4.x (Lean 3 keywords like `constant` do not apply)

> **Paper-realignment exception**: When the formalization is being realigned
> to a cited source (replacing wrong hypotheses, restating divergent theorems
> to match the paper), the `sorry` blocker below is temporarily relaxed for
> the *specific* theorems whose old proof depended on the deviating
> hypotheses. The protocol — including the required `**Unfaithful:**` marker
> on every such theorem and a paper-gap note documenting the deviation — is
> in `CLAUDE.md` §"Paper-realignment mode". Reviewers should evaluate
> paper-realignment PRs against the gap note and the planned follow-up, not
> against the `sorry` count alone.

---

## Blockers

These patterns **must** be resolved before merging.

### Direct proof holes

| Pattern | Risk |
|---------|------|
| `sorry` | Axiomatically closes any goal — the proof is incomplete |
| `admit` | Tactic alias for `sorry` |

### Kernel / type system bypasses

| Pattern | Risk |
|---------|------|
| `native_decide` | Relies on trusted native evaluation / compiler; banned in Mathlib for soundness and process reasons |
| `unsafeCast`, `unsafeCoerce` | Type system bypass — can fabricate any proof term |
| `lcProof` | Low-level proof fabrication primitive — can prove `False` |
| `ofReduceBool`, `ofReduceNat` | Kernel reduction primitives exploitable for unsound proofs |

### Axiom smuggling

| Pattern | Risk |
|---------|------|
| `axiom` declarations | Introduces unproven assumptions that could be inconsistent; every new declaration is a blocker |

#### Sanctioned axioms

There are no sanctioned axiom declarations in this repository. Any new
`axiom` declaration is a blocker.

Historically, `hayashi_ssa_equality_characterization_forward` in
Any historically sanctioned axiom, and the theorem that later discharged
it, is project fact rather than policy: record that history in the
project's own conventions addendum (CLAUDE.md or a local docs page), not
here.

## Warnings

These should be flagged for review but may be acceptable with justification.

### Placeholder tactics

| Pattern | Risk |
|---------|------|
| `exact?`, `apply?`, `library_search`, `suggest` | Search tactics left as placeholders — replace with the concrete result |

### Safety / termination bypasses

| Pattern | Risk |
|---------|------|
| `unsafe def` | Bypasses Lean safety checks; should not appear in proof-relevant code |
| `partial def` | No termination proof required; unsound if used to build proof terms |
| `implemented_by` / `implementedBy` | Decouples runtime behavior from proven specification |

### Suspicious options

| Pattern | Risk |
|---------|------|
| `set_option maxHeartbeats 0` | Disables timeout — can hide non-terminating proofs |
| `set_option maxHeartbeats` with values >= 4,000,000 | 20x the default (200,000) — likely indicates an inefficient proof |
| `set_option maxRecDepth` with values >= 10,000 | May hide structural issues in proofs |

### Debug artifacts

| Pattern | Risk |
|---------|------|
| `dbg_trace` | Debug trace left in code |
| `stop` | Halts elaboration — development aid only |
| `#check`, `#eval`, `#print` in proof files | Debug commands that should be removed |

---

## How to use this file

**In CI review prompts**: Reference this file instead of inlining the rules:
```
Read `docs/PROOF_INTEGRITY.md` for the complete list of proof integrity
rules. Flag blockers as must-fix issues that should block merge.
Flag warnings as advisory — note them but acknowledge they may be
acceptable with justification.
```

**For manual review**: Use this as a checklist when reviewing Lean PRs.

**Updating rules**: Edit this file and all referencing workflows will
automatically pick up the changes.


## Project addendum (TNLean)

### Sanctioned-axiom history

There are no sanctioned axiom declarations in this repository; any new
`axiom` declaration is a blocker. The one historically sanctioned axiom
(`hayashi_ssa_equality_characterization_forward`, issue #632 / gate #236)
was discharged as a theorem and its modules moved to the
[QICLean](https://github.com/LionSR/QICLean) companion library in the
quantum-channel extraction; QICLean's copy of this document records that
history in its own addendum.
