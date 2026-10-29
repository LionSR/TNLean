# The physical soft residual on the actual soft window

This contribution derives an exponentially small truncation residual on the actual soft Hamiltonian's low-energy space. It complements the original-window residual without assuming a moment, a spectral comparison, a gap, or a ground-space dimension.

For a prescribed interval of a positive-contraction nearest-neighbour chain, the construction retains the attained original regional minima and their common minimizing vector. Their sum centers the original Hamiltonian at an attained ground energy between zero and two. These choices precede the approximate regional energy and truncation order. The literal soft Hamiltonian replaces only the internal interval sum; all crossing bonds remain in the unchanged complementary Hamiltonian.

The order and scale are the same positive integer. Put

\[
\alpha=(m/2)2^{-m},\qquad \tau=m/2-10.
\]

For nonnegative hard threshold, the shifted soft/hard comparison derives positivity after the single scalar correction, and domination of the selected original high-energy projection. The actual soft ground energy is then constructed before the bandwidth, with

\[
-\alpha\le E_s\le E_0.
\]

The lower bound uses positivity of the crossing terms. The upper bound uses the original unit ground vector and the actual matrix inequality between the soft and original Hamiltonians.

For a bandwidth satisfying

\[
\eta\ge0,\qquad m/2\ge17+\eta+\alpha,
\]

the cutoff \(u=E_s+\alpha+\eta+C+1\), where \(C\le4\) is twice the actual crossing count, lies below the hard threshold and gives the weighted-map denominator exactly one. Commutation with the selected original regional sum is derived from disjoint supports and its own soft functional calculus. The actual soft eigenbasis diagonalizes the scalar-shifted Hamiltonian with eigenvalues shifted by the same scalar; the two definitions of its low spectral space are proved equal.

The resulting exponential moment and the same-operator functional-calculus remainder give

\[
\left\|(H-\widetilde H_{m,m})|_{\widetilde G_\eta}\right\|
\le80\exp\!\left(\frac{17+\eta+\alpha}{8}-\frac m{16}\right).
\]

The scalar correction enters the coercivity and the exponential constant. The residual remains the actual difference of Hamiltonians; no additional scalar residual is silently omitted.

## Source and scope

The source is ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1178–1255. This is a corrected auxiliary for one interval, with equal scale and order and the explicit scale condition above. The soft ground-energy construction initially assumes the weaker condition \(m/2\ge10\); the later scale condition implies it. Empty and endpoint intervals are included. Degenerate ground spaces are allowed, and no gap cap is used.

The false first uniform energy estimate remains false-source/open in the accompanying paper-gap note. The new result does not establish its printed bound. The quantitative order choice, ground-energy-shift accuracy and directed spectral-subspace comparisons remain separate steps, as do efficient representations, corrected cluster approximation and the low-density/tree construction.

## Ownership and reuse

All seven generic proof bodies formerly private in the regional-moment and original soft-residual modules are transferred verbatim to QICLean analysis, apart from namespace, declaration names and documentation. This byte-preservation check was performed independently. The public physical signatures already present in TNLean are unchanged; their proofs now use the shared matrix estimates. No generic public theorem or compatibility alias is left in TNLean.

The required companion sources are QICLean commits `0f223f2d` (coercivity) and `cd1cc858` (exponential restrictions and functional-calculus remainder), based on `15a60a1bebe726ee6536ae75570e8243b9f310c4`. They must be incorporated into the common dependency before an ordinary build of this TNLean contribution. The source-only TNLean branch intentionally leaves the dependency manifest to coordinated integration.

## Verification

Private separate-module checks used selected fixed imports from TNLean `f5e011c2e551b318e6df7f7d6e5e81725dedea7a`, its package revision `4175de302e6b580d1bbb4a022f57424ab9f05e73`, and the read-only ordinary QICLean provider at that exact revision. The three new companion objects were imported from privately checked temporary outputs. Guards covered the actually selected source and object files before and after elaboration; no provider source or artifact was changed.

- `RegionalExponentialMoment`: 28.266 seconds; SHA-256 `5cfa4c31d190a1d3452c7c38804b8b7134ac3889971262d2bd602b76f97adce1`.
- `PhysicalSoftTruncationResidual`: 38.977 seconds; SHA-256 `336dffc181c0efeaa9f830714410134eb6394e611d433ad40a4acb3fc7d86be5`.
- `PhysicalSoftTruncationReverse`: 33.917 seconds; SHA-256 `b9d8889a9762459709144208ca2749ff8d852faf8916993624c455ab34e2c1f0`.

All three modules passed strict package-equivalent Lean options, including warnings as errors. An imported-object foundation audit checked the new reverse theorem and both refactored physical theorems; each uses only `propext`, `Classical.choice`, and `Quot.sound`. The check and foundation records are `/tmp/tnlean-alvv-soft-reverse-checks.json` and `/tmp/tnlean-alvv-soft-reverse-foundations.json`.

The source worktree has no local Lake environment. Dependency artifacts were read without copying them; every new object was written under a temporary directory. No Mathlib source was compiled. Aggregator, reader-facing prose, proof-integrity and tactic-pattern checks were run locally. Common ordinary build and compiled blueprint checks remain integration gates.

The updated standalone paper-gap note rendered to three pages under `/tmp/tnlean-alvv-soft-reverse-note-render-20261029/`. All three final page images were visually inspected: text, equations, links and bibliography are unclipped, and the bibliography remains on the third page. Its final LaTeX log has no warnings.

## Combined verification

The coordinated TNLean revision `8ace1dccea` and QICLean revision
`34cb0c3a` passed the full builds, strict checks, imported foundation
audits and compiled blueprint checks. The complete phase records and
remaining scope are recorded in
[the integration audit](2026-10-29_verified_soft_residual_refinement_range.md).
