# Zero-gap Interaction migration acceptance

Prepared from complete reads of the five fixtures at
`fa9a40e22fa6384ba4a723e8bf675bb2cd20c5e7`, the external migration at
`592a46e4e442f87205c407720acbb487db0d2fcf`, and the shared contract at
`b2c72008326f3166d3bcdc9e79013443142b0aa8`, with QICLean
`729428582b78ab7529b3796099193649f947354a`.
This is an acceptance checklist, not evidence that migrated fixtures compile.
No fixture or production source is changed by the documentation lane.

## Common signature

Write `H = Φ.hamiltonian` and `PΩ = Matrix.vecMulVec Ω (star Ω)`, using
configuration coordinates for the Euclidean vector. The broad state data are

- `‖Ω‖ = 1`;
- `(H - (E₀ : ℂ) • 1 - (Δ : ℂ) • (1 - PΩ)).PosSemidef`;
- `Ω ∈ ManyBody.groundSpace H E₀`.

Retain every real `Δ`, including zero and negative values. Do not replace these
with `IsGapped` plus `groundSpace = span {Ω}`. At positive Δ, the existing
canonical bridge may derive uniqueness when required by a positive-gap theorem.
No second gap predicate, bundled Hamiltonian, compatibility constructor or
operator alias is needed.

`ChainInteraction L q R` and `PlaneInteraction Λ q R` contain only `term` and
`mem`. Construct a zero interaction with these canonical fields. Pass
`∀ X, (Φ.term X).IsHermitian` and `∀ X, ‖Φ.term X‖ ≤ J` explicitly where the
old bundle supplied them. Keep real J unrestricted unless that specific result
already assumed its sign. In particular, empty support-index types can make
norm bounds vacuous; one cannot infer J ≥ 0 without an actual term. The
shared domain-to-chain norm lemma's existing J ≥ 0 premise for inserted zeros
is not a license to impose it on the conversion or unrelated results.

## Five fixtures and exact acceptance boundaries

### `scripts/ground_state_gap_scope_regression.lean` (MPS lane)

Retain the two-dimensional zero-matrix proof of normalization, zero projector
inequality, membership and `groundSpace 0 0 ≠ span {Ω}`. Retain the real
one-site q=2 zero-chain calls:

- `ManyBody.ChainInteraction.re_inner_sub_le_of_overlap_of_range_one` uses
  norm-one Ω and membership, without singleton; its energy error remains
  `8 * L * δ`.
- `ManyBody.ChainInteraction.gap_le_four_mul_of_range_one` takes the existing
  `0 < L`, `2 ≤ q`, term Hermiticity/norm budget and broad state data, and
  concludes `Δ ≤ 4 * J`. Do not add `0 < Δ`.
- The actual `IsSquareGroundState 2 0 0 1 squareOmega` witness still supplies
  total Hermiticity, term bound, energy zero and the broad state triple.

### `scripts/generic_gap_boundary_regression.lean` (PEPS lane)

Replace the old local bundle with `PlaneInteraction {(0,0)} 2 1`. Keep the
nonempty physical site and explicit independent basis vector proving that the
zero-H ground space is not a line. Supply Hermiticity and norm bounds separately.
Actually specialize all four production definitions `SublinearCollarBound`,
`SublinearCollarBoundAt`, `AmplificationBound`, `AmplificationBoundAt` at Δ=0.
Preserve their quantifier order, constants and geometric conditions; do not
assert the corresponding bound unconditionally. The empty A,T specialization
must remain admissible. These are generic conditional definitions, not a
nonpositive-gap area-law theorem.

### `scripts/zero_gap_tn_wrappers_regression.lean` (shared lane)

- Rectangle: call `projectorGap_toAreaLawHamiltonian` for all natural widths
  and heights, including 1×2 and either side zero. The shared signature is
  `Φ → total-Hermitian → norm → PSD → membership`, with the transported triple
  for `Φ.toAreaLawHamiltonian.hamiltonian`. The conversion takes no norm-bound
  argument. Do not strengthen total Hermiticity to termwise Hermiticity: its
  construction uses Hermitian parts. The separate term-norm lemma keeps every
  real J. Keep the explicit one-site q=2 non-singleton proof; an empty lattice
  has one configuration and does not establish that non-singleton boundary.
- ThreeWay: migrate the zero-chain owner and actual
  `isGapped_groundCentered_parts_sum` call, preserving all natural j,m,
  including cuts beyond the endpoint. Its explicitly typed conclusion is
  normalization, centered-sum PSD and membership at energy zero, not a line
  ground space. Do not gratuitously add termwise Hermiticity to a purely
  algebraic transport that did not require it.
- Canonical and pinned zero-floor: preserve actual optimizer calls for every
  m, empty nested regions and weights one, including m=0 and m=1. Explicit
  targets retain maximality, positive output norm, normalized output, energy
  error and **Δ-weighted** fidelity. At Δ=0 the fidelity inequality is vacuous;
  it must not become an unweighted overlap claim. Preserve total Hermiticity
  and the original norm-bound hypotheses, with no new sign premise on J.

### `scripts/range_square_zero_gap_regression.lean` (PEPS lane)

Keep the actual one-site q=2 zero-square witness and the explicit target
`IsRangeSquareGroundState 2 1 0 0 1 omega`, proved by the production
`IsSquareGroundState.isRangeSquareGroundState` conversion. The existential
PlaneInteraction now carries explicit term Hermiticity/norm bounds, followed
by energy and the broad state triple. Use rectangle projector transport and
its separate term estimates; no singleton or positive-gap premise is permitted.

### `scripts/box_supremum_zero_gap_regression.lean` (PEPS lane)

Retain the singleton physical domain, normalized q=2 zero-H state, and actual
membership in `boxEntropyValues 2 1 0 0 0 1`, supplying the new explicit term
hypotheses. Preserve the actual `regionalEntropy_le_boxEntropy` call and its
explicit target. The integer rectangle has **size one**; its intersection with
the physical cut is empty. At r=0 there are no admissible rectangles, because
`Q.one_le_size`; retain both the empty-value-set and zero-supremum assertions.

The explicit target of `regionalEntropy_le_of_boxEntropy_power` must remain
`regionalEntropy ... ≤ C * (rectangle.size : ℝ) ^ (1 + e)`, with both
`he : 0 < 1 + e` and
`hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy ... r ≤ C * (r : ℝ) ^ (1 + e)`.
This is a conditional bridge, not an unconditional zero-gap entropy theorem.

## CI and review gates

The fa9 selector uses each regression's transitive repository import closure,
not just whether the fixture itself changed. An independent source traversal
confirmed the following owner reachability at fa9:

| Fixture | Owners in its actual import closure |
|---|---|
| ground_state_gap_scope | MPS/AreaLaw/Hamiltonian |
| generic_gap_boundary | Lattice/LocalHamiltonian; PEPS/AreaLaw/BoundaryTheorem |
| zero_gap_tn_wrappers | both Hamiltonian owners; RectangularHamiltonian; SquareZeroFloorOptimizer; PinnedZeroFloorOptimizer; Hastings/ThreeWaySplitting |
| range_square_zero_gap | LocalHamiltonian; RectangularHamiltonian; RangeSquareGroundState |
| box_supremum_zero_gap | LocalHamiltonian; InitialBoxEstimate |

Re-run the actual selector on the final integrated source tree for changes to
each owner as well as to each fixture. A deleted fixture cannot be selected:
the external branch's apparent deletions must not be accepted in integration.
Explicit conclusion types must remain, so a weaker theorem cannot silently
satisfy an inferred example. Source inspection and closure reachability do not
replace exact-source, exact-pin elaboration of all five complete fixtures.
The five fixture classes are not exhaustive coverage of all possible q, J,
Δ and domain dimensions; the corresponding theorem signatures require review.
