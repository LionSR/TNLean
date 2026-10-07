# Genuine-source chronological regressions

The gate is obtained by the proved common-source construction from two actual
allowed pair-source words on the party type Bool. Their one-dimensional source
vectors are 1 ⊗ 1 and I times that vector. Both scalar coefficients are 1/2; the
aggregate contraction bound follows from the triangle inequality. Pair completeness
proves that the constructed gate has a nonempty source inventory.

Two occurrences of this same gate are composed, with the second acting beside
the first output registers. Three assertions are checked:

- The selected local labels at the two occurrences are explicitly false and true.
- The common retained-slot enumeration keeps these occurrences distinct, and each
  canonical source vector is the original gate vector for its own selected label.
  The equalities account for the dependent coordinate-space identification.
- Applying the proved canonical preparation gives a nonempty literal source
  inventory of the actual partial monomial.

The common-source construction may choose new finite coordinates, so the tests
compare its actual gate vectors instead of assuming that its coordinate vectors
are the displayed one-dimensional tensors. Local labels are checked separately;
that check remains meaningful even if some coordinate vectors happen to agree.
No gate preparation identity or nonempty source inventory is supplied as a premise.

Raw Lean compilation uses the package options and warnings as errors. A separate
importing module audits all three theorem axioms. Exact commands, logs, committed
production source bytes, artifact hashes and every actually imported artifact are
recorded. The evidence is pinned to source commit
6246647741ce41a55a3897329336055330dd7e6f. No Lake cache is changed.
