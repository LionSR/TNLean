# Required labels in the existing cluster expansion

Two auxiliary results connect the checked normalized exponential estimate
to the existing cluster operators. No new cluster definition is introduced.

For a finite required-label set U, the existing empty-boundary cluster
part is

\[
R_U^H(\beta)=\sum_{D\subseteq U}(-1)^{|D|}
 e^{-\beta(H-\sum_{i\in D}h_i)}.
\]

If H and the selected h_i are Hermitian, ||h_i|| ≤ 1, H ≥ λI, and β ≥ 0,
the first theorem proves

\[
e^{\beta\lambda}\|R_U^H(\beta)\|\le(e^\beta-1)^{|U|}.
\]

The lower energy λ is supplied; it need not be the exact minimum. This
result does not require H to be the full sum of the selected terms, a
finite ambient label type, or a nonempty matrix index type. It applies
the checked QICLean normalized finite-sum theorem to the exact existing
definition `clusterPart H h ∅ U β`. No successful approximation, external
norm estimate, or new family of local operators is assumed.

The second theorem assumes a finite full label type K and constructs
H = Σ_(i∈K) h_i. For every finite U in K and every real β, it proves

\[
R_U^H(\beta)=\sum_{A\subseteq K,\ U\subseteq A}E_A,
\qquad E_A=\operatorname{clusterOp}(h,A,\beta).
\]

No Hermiticity, norm, positivity, or commutation hypothesis is needed for
this finite identity. Its proof uses the existing convergent word-series
formulas for `clusterPart` and `clusterOp`. At each word length, the words
containing U are partitioned by their exact letter set A. Mathlib's
`Finset.sum_fiberwise_of_maps_to` gives this finite partition, and a finite
sum of convergent series gives the equality. Word order and multiplicity
are preserved. This is a finite sum over the existing exact-support
operators; a second Möbius-transform construction is unnecessary.

The empty required set, empty full label type, empty matrix index type,
and β = 0 are included. No coefficient or scalar exponential is divided
out of the word-series equality, so vanishing coefficients cause no issue.

## Source and remaining scope

The existing cluster definitions and word-series interpretations follow
Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177 and 1268–1269.
The normalized bound is a corrected auxiliary ingredient for the
interaction-label argument related to ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`, lines 1270–1291 and 1935–1968. It is not the false
printed spatial approximation estimate; the obstructions to that claim
remain in `docs/paper-gaps/alvv16_cluster_approximation.tex` and at
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.

Finite inclusion–exclusion over the actual bad intervals, the normalized
spatial tail bound, the crossing-interval factorization, operator Schmidt
rank estimates and an MPO construction remain subsequent work. In
particular, the finite identity does not construct the interval family or
identify the interaction-label component cutoff with a geometric event.
The separate generic coefficient contribution remains independently frozen.

## Declarations and verification

The public declarations in
`TNLean/Lattice/ClusterExpansion/MandatoryLabels.lean` are:

- `TNLean.Lattice.ClusterExpansion.norm_clusterPart_empty_boundary_le_of_lower_bound`;
- `TNLean.Lattice.ClusterExpansion.clusterPart_empty_boundary_eq_sum_clusterOp`.

The actual module passed the strict package checks against the frozen
TNLean source `f5e011c2e551b318e6df7f7d6e5e81725dedea7a` and its QICLean
package `4175de302e6b580d1bbb4a022f57424ab9f05e73`. The final measured time
was 29.29 seconds while unrelated common-library jobs were running.
Thirty-four selected TNLean and QICLean source/object pairs, together
with the build inputs and Mathlib cache sentinel, were hashed before and
after checks and remained unchanged. No unrelated changing build output
was used as an audit dependency.

A separate module imported the final compiled object and audited both
public declarations. Their only foundations were `propext`,
`Classical.choice`, and `Quot.sound`. The reader-facing prose and repeated
tactic checks passed. The new mathematical section compiled twice as a
standalone page and was visually inspected, with resolved local references
and no overfull boxes; earlier chapter references used explicit stand-ins
in that temporary rendering.

The expected import aggregator was computed by the repository's generator
with the new source added to its source inventory. Only the expected
cluster-expansion aggregator changed. No generated provider file was
edited. All new objects and temporary audit files are under `/tmp`; no
provider source, package pin, dependency, object or cache was changed and
no Mathlib source was rebuilt.

Ordinary common-library compilation and the compiled blueprint declaration
check remain integration checks. No temporary audit command or per-theorem
fixture is included in the source patch.
