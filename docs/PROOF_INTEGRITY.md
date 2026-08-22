<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Lean Proof Integrity Rules

Canonical text: the `lean-conventions` skill —
[PROOF_INTEGRITY.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/PROOF_INTEGRITY.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (TNLean)

### Sanctioned-axiom history

There are no sanctioned axiom declarations in this repository; any new
`axiom` declaration is a blocker. The one historically sanctioned axiom
(`hayashi_ssa_equality_characterization_forward`, issue #632 / gate #236)
was discharged as a theorem and its modules moved to the
[QICLean](https://github.com/LionSR/QICLean) companion library in the
quantum-channel extraction; QICLean's copy of this document records that
history in its own addendum.
