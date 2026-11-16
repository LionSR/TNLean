# Shared positive preparation rate

Tactic-pattern ledger addendum for the preparation item in the comprehensive audit (#10637), based on main `eb588dc15332a3798431015e6c27ecbaf329b2d1`. The central ledger is already modified in active drafts and is left untouched.

- **Pattern:** specialize the unequal-block error bound at half exponent, choose the positive rate minus the logarithm of the real spectral cutoff, and rewrite the exponential.
- **Seen:** three copies in `LogDepthPreparation`, `LogLogDepthEveryLength`, and `UnequalTreeMERA`. This meets the rule of three across distinct files.
- **Promoted:** `MPSTensor.exists_blockApproximationError_le_exp` in `BlockApproximationError`; all three consumers use the lemma. No tactic is introduced. The same constants work for every partition with the existing injectivity assumptions.
- **Scope:** all nine existing public declaration headers and all imports are unchanged. Lean source decreases by four lines; the new mathematical Blueprint entry documents the shared corollary. Static checks passed; local Lean and Blueprint compilation are unavailable, so hosted acceptance is required.
- **Deferred:** Hamiltonian-constructor sharing remains subject to ownership reconciliation in #10609. A future zero-extension constructor must allow a default norm bound conditional on an unused support: the square constructor derives nonnegativity from that support's nonemptiness, whereas an empty admissible-support family imposes no global sign condition. Adding an unconditional nonnegative interaction-bound premise would change the public statement.
