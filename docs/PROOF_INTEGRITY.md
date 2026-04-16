# Lean Proof Integrity Rules

This file is the **single source of truth** for proof integrity checks in this
repository. All CI workflows and review prompts should reference this file
rather than duplicating the rules inline.

> **Lean version**: 4.x (Lean 3 keywords like `constant` do not apply)

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
| `axiom` declarations | Introduces unproven assumptions that could be inconsistent; must be explicitly justified |

#### Sanctioned axioms

The following axioms are explicitly sanctioned in this repository. Each is
isolated in a dedicated module under `TNLean/Axioms/` with a citation to its
primary source and a formalization TODO. New axioms outside this list are
treated as blockers.

| Axiom | Module | Citation |
|-------|--------|----------|
| `strong_subadditivity` | `TNLean/Axioms/Entropy.lean` | Lieb–Ruskai, JMP 14, 1938 (1973) |
| `Axioms.beigi_shor_whalen` | `TNLean/Axioms/BeigiShorWhalen.lean` | Beigi, Shor, Whalen, CMP 312 (2012) 435–460 — ground-space characterization of 1D commuting nearest-neighbor Hamiltonians; consumed by `MPSTensor.rfp_implies_nncph` and `MPSTensor.nncph_implies_rfp` in `TNLean/MPS/ParentHamiltonian/Commuting.lean` (arXiv:1606.00608 §3.3 Thm 3.10) |
| Operator-convexity axioms | `TNLean/Axioms/OperatorConvexity.lean` | Pending upstream Mathlib |

### Circular reasoning

Lean's kernel forbids literal declaration cycles, so focus on **mathematical
circularity**:

- Proofs that assume (or trivially reintroduce) the statement being proved as a
  local hypothesis, then immediately close the goal from that hypothesis
- Helper lemmas in the same file that essentially restate the main goal and are
  only used to prove that goal
- Local `have`/`let` bindings that are just the goal rephrased, used to solve
  the goal without any real argument
- Newly introduced `axiom` that makes a difficult statement trivially provable
  without connecting to existing Mathlib / core theorems
- Abuse of `unsafe` features to fabricate proofs instead of giving a genuine
  derivation
- `by exact h` where `h` came from an unjustified assumption identical to the
  goal

### Castle-in-the-air (ungrounded proofs)

Proofs that avoid grounding in Mathlib:

- Custom re-declarations of standard Mathlib lemmas (e.g., re-proving
  `add_comm` instead of importing it)
- `axiom` or `sorry`-based helper lemmas for facts that already exist in
  Mathlib
- Chains of custom lemmas that never bottom out in Mathlib or Lean core
- `private` helper lemmas that duplicate Mathlib API (e.g., custom matrix
  transpose lemmas when `Matrix.transpose_*` exists)
- Overly long proof chains replaceable by a single Mathlib lemma

When flagging, perform an actual lookup (grep, `#find?`, `exact?`,
`library_search`). If an equivalent exists, cite the Mathlib lemma and module
path. If not, state "no equivalent found" with search evidence.

---

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
