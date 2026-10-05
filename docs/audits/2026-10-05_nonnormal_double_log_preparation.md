# Canonical non-normal preparation in double-logarithmic depth

## Result and source scope

`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_repeatedBlockSum_le_log_log_of_inequivalent`
combines the supported polar-tree compiler and constant-depth sparse GHZ preparation with the
amplitude-uniform overlapping-sector estimate. It covers the supplied canonical repeated-block
class, with normal inequivalent left-canonical blocks and positive definite trace-one fixed points.
The constant precedes the length and accuracy. Every `N ≥ 2` with nonzero periodic vector and
`0 < ε ≤ 1` has a unit approximant of error at most `ε` in depth
`C log(1 + log(N/ε))`.

This extends the constructions in arXiv:2307.01696, “Tree-RG circuit with measurements” and
“Long-range MPS using measurements”. It does not claim that the paper already states this exact
all-length canonical theorem, or prove original-to-canonical transport and periodicity for an
arbitrary tensor. Existing `CopyWeights` conventions are unchanged: zero padding is omitted;
complex phases, multiplicities and vanishing aggregate sector coefficients are allowed.

The stronger reusable state-identity endpoint accepts arbitrary length-dependent complex
coefficients in a supplied identity `φ_N(A) = ∑_j β_j(N) φ_N(A_j)`. Its analytic bound does not
contain an inverse minimum-sector amplitude.

## Proof and resource accounting

1. Inequivalence gives a strict mixed-map eigenvalue bound, including rectangular mixed maps
   between different bond dimensions. The existing common-rate theorem then covers all diagonal
   and off-diagonal transfer maps.
2. Work with the unweighted direct sum of normal blocks. Its eventual diagonal sector-pair
   support is the domain of genuine isometric polar trees. This retains the inherited correction
   to the source's weighted repeated-block positive-part formula.
3. Prepare the sparse GHZ labels in constant quantum depth. A single bounded-window unitary
   takes all labels to their orthonormal pairs, so arbitrary complex superpositions remain coherent.
4. Encode each bond leg with a final zero site. `blockInputCfg_eq_placeCfg` is an equality of full
   physical configurations, including the odd trailing site. It aligns the actual-end label/pair
   windows with the even tree-root cutoff. No coordinate identification or uncounted gate is used.
5. The pair layer leaves tree-interior scratch zero. Compose the actual measurement rounds with
   the supported tree compiler to obtain depth `C(h+1)`.
6. Choose `q = ceil(a log(N/ε) + b)`. When `q ≤ N`, use unequal blocks between `q` and `2q` and
   the amplitude-uniform error `K M exp(-r q)`. When `q > N ≥ 4s`, use a whole-ring supported
   tree, with exact pair support required only at `M = 1`. Only the fixed finite range `N < 4s`
   uses bounded exact synthesis.

Only nearest-neighbor unitary layers are counted. Measurement, classical communication and
on-site corrections are free; the number of rounds may grow with tree height. Every
nonzero-probability history yields the target up to a scalar, with no postselection. The existing
fixed-history scalar theorems for sparse shifts and supported trees are uniform on their logical
input subspaces. All endpoint equalities include every physical site, with no discarded environment.

## Reuse and compatibility

- `PreparedComposition` adds prepared-state/implementation composition with additive depth.
- `GHZSeedCircuit` exposes one simultaneous pair unitary and actual-ring localization. Its genuine
  unitary compiler now has an actual-`M` interface. The previous all-`M` signature is preserved
  verbatim as a wrapper for existing consumers.
- `CoherentBlockTreePreparation` chooses support enumeration, encodings and constants once for
  a fixed maximum number of labels. One choice covers both the canonical family and the exact
  one-label whole-ring pair.
- `SupportedLogLogPreparation` separates physical compilation/scale arithmetic from the
  canonical analytic estimates.
- `LogLogDepthBound` moves the existing two numeric lemmas verbatim out of
  `LogLogDepthEveryLength`; the normal endpoint statement and proof after those lemmas are unchanged.

## Validation contract

The algebraic composition, encoding, tree/scale modules and actual-ring regressions are checked
with production imports using source-matched Lean 4.35.0-rc3 artifacts and QIC pin
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. No Mathlib, Gametheory or broad QIC rebuild was used.

The local cache lacks the broad analytic prerequisite
`QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral`. The new analytic specialization and spectral
bridge therefore also have strict, scope-isolated exact-source-body checks: algebraic definitions
are copied exactly and existing prerequisite theorems are explicit parameters with their actual
signatures. These checks introduce no axioms, but do not certify the production import graph.
Full exact-head repository CI must validate that graph before merge.

`TNLeanTest/CoherentBlockTreePreparation.lean` checks actual-`M=1` support, a concrete pair whose
one-block support fails at two blocks, and even/odd root placement.
`TNLeanTest/NonNormalLogLogPreparation.lean` exposes the final quantifier order, the rectangular
mixed-gap case, and complex phases cancelling one sector while the total vector remains nonzero.
Both are explicitly included in PR CI. Existing coherent-branch, supported-tree and sparse-GHZ
regressions remain included.

The new whole-ring tenkzequation diagram has the same physical output boundary on both sides,
no input boundary, and one supported virtual contraction. Its tree box denotes the entire
bounded-leaf tree. The pinned tenkz rendering was inspected, and the diagram-boundary/numerical
Python suite checks it together with the earlier nonsquare-support merge diagram.
