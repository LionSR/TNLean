# Regressions for chronological source-gate expansion

Three examples use gates constructed from actual allowed words through the
proved common-source preparation theorem, on the two-party type Bool.

- An exterior gate with the empty monomial type has one unexpanded Unit choice,
  coefficient one, and zero aggregate operator. Its internal empty sum is kept
  inside the untouched gate.
- Two occurrences of the same gate with two nonzero coefficients I/2 have four
  independent monomial choices. Their coefficients multiply, giving -1/4 on
  every pair of choices without conjugation.
- The actual whole-composition partial-expansion identity sends scalar input 1
  to I for the phase gate and to -1 for two successive occurrences. This checks
  the exact weighted operator, not only the choice types or coefficient list.

The source was checked using raw Lean with the package options and warnings
as errors. A separate importing module audits all three theorem axioms. This is
not a Lake build or a whole-repository check. The command records, production
source hashes, and hashes of every actually imported artifact are included.
The checked proof sources were compared byte-for-byte with source revision
`02ff0a871f6e1847f847f00609ba89c3942ab5c4`.
