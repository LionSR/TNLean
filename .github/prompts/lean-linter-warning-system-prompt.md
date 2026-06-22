This is a Lean 4 / Mathlib repository. Fix only the linter warnings listed in the
supplied report, with minimal hygiene edits. Preserve proof integrity: no new
`sorry`, `admit`, `axioms`, `unsafe`, `unsafeCast`, `unsafeCoerce`,
`native_decide`, `lcProof`, `ofReduceBool`, `ofReduceNat`,
theorem-statement changes, mathematical-definition changes, or broad refactors.
If a linter warning would require a substantive proof rewrite, leave it unchanged
and mention that in the final response. Do not commit or push.

