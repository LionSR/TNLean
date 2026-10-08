# String Order finite-size estimates and periodic examples

## Source and scope

This batch continues arXiv:0802.0447 on the periodic-string source snapshot
corresponding to draft PR 8730, with QICLean pinned at
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

- Source lines 241–243: exponential decay of a contracting physical string.
  Every prescribed rate strictly above the twisted spectral radius bounds
  the string, including middle length zero. Decay follows when the rate is
  below one. The prefactor can depend on the endpoints and prescribed rate.
- Source lines 249–255: the product of the two actual physical endpoint
  coefficients has a geometric remainder after removing the phase `μ^N`.
  The canonical tensor supplies one rate independent of the fixed endpoints.
  Positive middle length is explicit because the zeroth complementary power
  is not the transfer power minus its stationary projection.
- Source `MPS`/`SOPMP`, lines 137–181: canonical purity supplies a common
  geometric rate for the periodic normalization and each fixed-support
  expectation. On a common eventual tail the vector is nonzero and the
  normalization denominator has norm at least `1/2`.
- Source `RL`, lines 381–388: a prescribed-rate geometric bound for the
  actual full-ring normalized expectation in the contracting branch.
- Source Examples 1–2, lines 392–411: exact AKLT normalization and actual
  normalized AKLT/cluster whole-ring overlaps. AKLT has a zero vector at
  length one; the cluster short rings use the already-established circuit
  convention. Empty-ring normalization is retained explicitly.

The estimates assume neither diagonalizability nor the desired error bound.
They make no uniform-prefactor claim for growing supports, no exchange of
ambient-ring and string-length limits, and no Hamiltonian-gap implication.
The source's existential physical-state theorem remains separately scoped.

## Proof structure and simplification review

1. The existing adjoint-family FNW complementary remainder proves the
   canonical operator estimate. Its norm is the endomorphism norm induced
   by the row-sum matrix norm, rather than the rho-weighted FNW norm. The
   older canonical convergence theorem now follows from this bound.
2. QICLean's `geometric_apply_bound_of_spectralRadius_lt` supplies contraction
   at a prescribed rate; its existing `geometric_bound_of_spectralRadius_lt_one`
   supplies a canonical rate. No spectral theory is copied into TNLean.
3. The periodic trace functional acts on the same operator-norm remainder.
   This replaces the old pointwise-to-operator convergence proof and removes
   the unused `OperatorNormConvergence` import.
4. The normalized error follows from
   `|a/b - s| ≤ 2 (|a-s| + |s| |b-1|)` on `|b| ≥ 1/2`, together with
   `r^(k+n) ≤ r^n`. The common rate is outside the observable quantifiers;
   its prefactor remains inside.
5. The cluster example's Pauli matrix is reused from QICLean `SpinCover.pauli`.
   Its old `TimeReversalIndex` import supplied only an identical matrix
   definition. The heavy unrelated import is removed, no new Pauli matrix
   is defined, and the existing theorem names and mathematical matrices
   are preserved. The upper time-reversal module remains unchanged.

Three one-use AKLT proof steps remain private: the physical-rephasing
transfer equality, the length-at-least-two nonvanishing proof, and the
nonvanishing-length overlap cancellation. The public statements retain the
exact all-length normalization, admissible lengths, and piecewise overlap.

The find-simplification review found no additional necessary public wrapper
or local structure. Existing FNW projection and phased-iterate identities
are reused directly. The two old convergence theorems remain meaningful
consumers of the stronger estimates rather than independent proof routes.

## Validation

The companion validation record lists actual source hashes, commands,
runtimes, and results. Each changed production target is checked with the
package options and warnings as errors, serially, within 90 seconds per
module. Unchanged dependencies use their exact package options. New tests
exercise a nonreal symmetry phase, arbitrary fixed physical observables,
AKLT lengths zero through three, and cluster short-ring normalization.
Axiom inspections allow only `propext`, `Classical.choice`, and `Quot.sound`.

These are focused direct elaborations against source-matched private
artifacts. They are not a claim that the complete Lake/root target or the
full blueprint book was built locally. No cache trace is synthesized.

## Checked periodic blueprint nodes

The accepted periodic predecessor merged as
`a293dcf380592f7269eb14b37a53ab7ebb466332`, whose Git tree
`b27ca4322dcedb4a3171abde4c0d66803332b62a` is identical to this batch's
local source-snapshot parent. Its exact-head CI run
[37504592665](https://github.com/LionSR/TNLean/actions/runs/37504592665)
passed before the merge.

The five derived periodic theorem entries and their proof blocks now carry
checked markers: the finite trace ratio, eventual normalization, the
fixed-support limit, exact symmetry phase, and phase-qualified spectral
alternatives. Their hypotheses match the proved statements. The scalar-phase
example already carried a checked marker. The literal source-overlap node
without a direct declaration tag, the false printed physical criterion, and
the unresolved physical-state symmetry theorem remain unmarked.
