# Referee audit of the area-law and polynomial-PEPS manuscripts

This note records an independent, paper-level referee audit of the two
September 24, 2026 manuscripts formalized by the campaign tracked in #8733:
*A two-dimensional area law from a global spectral gap* and *Polynomial PEPS
approximation of gapped square-grid ground states*, both at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The audit ran in two rounds, on 2026-10-13 and 2026-10-21. The first round
targeted the steps that were then unformalized and judged most likely to hide a
gap. The second round covered the remaining sections and the six load-bearing
points listed in the tracker. Each candidate gap was traced to a precise
location and then subjected to an attempt at refutation. Only candidates that
survived refutation are reported as findings.

Both headline theorems have since been proved in Lean:
`TNLean.PEPS.AreaLaw.uniformAreaLaw` and
`TNLean.PEPS.Approximation.polynomialPEPSApproximation`. The audit is therefore
a cross-check of the source arguments and of the faithfulness of the Lean
statements, not a precondition for the proofs.

## Result

No genuine mathematical gap was found in either manuscript. The only findings
are prose slips and loose constants, listed below; none changes a statement.

## Coverage

| Area | Source results | Verdict |
|---|---|---|
| Area law, preliminaries and initial bounds | Lemmas 2.1–2.3, 3.1, 3.2, Proposition 3.3 | Sound |
| Area law, quasi-locality | Lemmas 4.1, 4.2, 4.4, Propositions 4.3, 4.5 | Sound |
| Area law, conditional estimates | Lemmas 5.1–5.3 | Sound |
| Area law, replicas | Lemmas 6.1–6.4 | Sound |
| Area law, transport | Lemmas 7.1–7.3, Proposition 7.4 | Sound |
| Area law, comparators | Proposition 8.1 | Sound |
| Area law, scanner and bootstrap | Lemma 9.1, Definition 9.3, Lemma 9.4, Propositions 9.2, 9.5, 9.6 | Sound |
| Area law, amplification | Lemma 10.1, Proposition 10.2 | Sound |
| Area law, geometry and assembly | Lemmas 11.1, 11.3–11.5, Proposition 11.2, Theorem 1.1, Corollary 1.2, degenerate cases | Sound |
| PEPS, information estimates | Propositions 3.1, 3.4, Lemmas 3.2, 3.3 | Sound |
| PEPS, adaptive patches | Proposition 4.1, including descending stationarity | Sound |
| PEPS, compression | Lemma 5.1, Theorem 5.2 | Sound |
| PEPS, dyadic protocol | Proposition 7.1, Lemma 7.2 | Sound |
| PEPS, assembly | Section 8.1 ledger, Lemmas 8.1, 8.2, small sizes, Appendix | Sound |

## Load-bearing points of the tracker

1. *Constants precede the domain, cut and Hamiltonian.* Every constant in the
   area-law argument depends only on `q`, `R`, `J`, `Δ` and fixed exponents.
   The PEPS threshold `L₀` and the compression constants depend only on
   `q`, `J`, `Δ`, the fixed exponents and the templates.
2. *No smaller region is given its own gap.* All fifteen sites where a gap is
   used rely on the gap of the full Hamiltonian, or on a gap derived from it:
   the positive replacement, the finite-set truncation (gap at least `g/2` by
   min–max), and the doubled Hamiltonians of the information reset.
3. *Conditional information comes from the cell argument.* PEPS Lemma 3.2 is a
   chain rule over two tile families, using purity duality for the second
   family. Each tile cost is an unconditional bound at a fixed clearance. Its
   only consumer, Proposition 3.4, conditions on unions of whole cells of the
   same grid, as the lemma requires.
4. *Patch complexity is a sum of cylinder ranks.* Proposition 4.1 bounds
   `Σ_j d_j ≤ C L^c`. Section 6.1 and Lemma 6.3 consume exactly this sum; no
   global rank is used.
5. *Compression uses lifetime participation.* Theorem 5.2 needs a bound `b` on
   the nonprivate gates in which each party takes part over the whole
   construction. Proposition 7.1 supplies it with `b` independent of `L` and
   the Hamiltonian: a party of side `m` acts only at levels `m` and `m/2`,
   exchanges create no linked gate, and frozen sheets and placeholders are
   never reused.
6. *The contraction is nonzero before normalization.* Lemma 8.1 selects a
   product column with nonzero coefficient from a trace-norm error `η < 1`,
   using neither positivity nor Hermiticity of the compressed operator.
   Routing and folding in Lemma 8.2 preserve the contraction exactly.

## Findings

None of these affects a statement.

- PEPS Lemma 8.2, final paragraph: the congestion "increases by at most four"
  should read "is multiplied by at most four". The bound in
  `docs/paper-gaps/polypeps_routing_network_bounds.tex` already uses the
  multiplicative factor.
- PEPS Section 8.1: the displayed density bound `CL⁻¹⁷ + CL⁻⁵⁷` suppresses
  factors of two, which the convention that `C` may change between
  occurrences covers.
- Area-law Lemma 6.1(6): the constant `2^q` can be `2^{q−1}`.
- Area-law Lemma 3.1 bounds `z_u²` by `u²`, and Lemma 3.2 uses the margin `D`
  where `r + D` is available. Both are loose but correct.
- `TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean`: the module docstring says the
  constants work for every admissible safety parameter. The theorem is stated
  for natural-number parameters; the real-parameter case is the transfer
  recorded in `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

## Lean statement faithfulness

The definitions behind the two headline targets were compared with the printed
statements: `UniformAreaLaw`, `LocalHamiltonian`, `IsAdmissibleSupport`,
`regionalEntropy`, `edgeBoundary`, `PolynomialPEPSApproximation`,
`SquareHamiltonian`, `HasPEPSApproximation` and `Matrix.IsGappedGroundState`.
They carry the source hypotheses and quantifier order, and they are unchanged
since 2026-10-12 apart from moving into `TNLean/Lattice`.
The labelled intermediate results of area-law Sections 2–7 in TNLean and
QICLean carry no hypothesis absent from the source. Where they differ, the Lean
statement is more general (Lemma 3.1 for every real `w`; Lemma 6.4 for
disjoint `P`, `Y`, `F` and all `0 < t < 1/2`) or the narrowing is already
recorded in `docs/paper-gaps/`.

The patch-stationarity step of Proposition 4.1, flagged in the first round as
the most delicate open step, was proved in QICLean #818 and resolved
`oai26_peps_patch_stationarity_gap.tex`.

## Formalization notes

- Theorem 5.2 relies on fourth moments of circular complex Gaussians and on a
  Schatten `(4, 2, 4)` Hölder inequality; random phases are not a drop-in
  replacement for the Gaussians.
- Lemma 10.1 uses Poisson-clock processes; a discrete event-count expansion is
  the simpler route for a formal proof.
- Lemma 8.2 needs the padded side `N` to satisfy `L ≤ N < 2L`, and its
  congestion count must include the repeated traversals at the fold.
