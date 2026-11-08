# Quantified asymptotic ground-state bond-dimension dichotomy

Source: SPWC10, `Papers/0909.5347/main.tex`, Theorem 5, lines 850–880.
Issue: #10280. Parent draft: #10366.

## Actual implementation

`exists_normal_blocks_of_no_small_divisor` extracts the canonical, periodic
and phase-grouping proof from the existing W-state bound and generalizes the
physical alphabet. It outputs the actual length-N expansion, at most D
positive-dimensional blocks of dimension at most D, nonzero coefficients,
unital normalization, faithful dual fixed points, irreducibility, common
injectivity at q(D)=(D²+1)² and gauge-phase separation. No decomposition,
period, source selector or injectivity estimate is a premise. The W-state
proof now calls this general result rather than retaining another copy.

For one positive L-site interaction h whose actual zero-energy kernel has
dimension one for every M≥L, the quantitative capstone is:

- if one nonzero prime-length MPS ground-state representation has
  N≥L+max(q(D),3(D−1)(q(D)+1)), derive one fixed tensor B of positive bond
  dimension at most D which generates the entire nonzero ground-state line
  for every M≥max(L,q(D)+1);
- otherwise every prime N and every nonzero bond-D MPS ground-state
  representation satisfies the strict reverse inequality, for the same h,L.

The proof derives D<N from that numerical threshold, removes the
nonprimitive blocks by primality, and uses phase grouping to derive the
separation input rather than assume it. The retained expansion is nonempty
because the original vector is nonzero. Complementary simultaneous spanning
and #10366's actual finite-volume result put every block's whole active MPS
space in ker h. Any retained block then gives zero energy on all permitted
volumes. Existing block-injectivity nonvanishing and the dimension-one
hypothesis identify the future ground-state line. An argument that first
forces the block count to equal one is unnecessary for this conclusion.

## Quantifiers and source boundary

The obstruction is for every prime and every actual nonzero representation,
not only the W state or one selected family. The local term, interaction
range and threshold formula precede those quantifiers. All canonical,
periodic, separation, local-kernel and future-volume properties are derived.

The fixed tensor is eventual. The source's literal all-volume
uniform-dimension formulation needs a separate finite-prefix representation
argument. This boundary is explicit in the module marker, the separately
scoped Blueprint theorem, and
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.
There is no claim that the same tensor represents every short ground state,
and the unrestricted source label is not marked ready. #10280 remains open.

## Verification

Independent read-only review checked the generic extraction, phase filtering,
prime/no-divisor implication, exact complementary threshold, local-kernel
propagation, nonvanishing cutoff, and all quantifier orders. No concrete
mismatch was identified. Native import generation, roles, reference sync and
duplicate ownership, width, source integrity, committed prose, pinned TeX
formatting, ChkTeX and diff checks pass. The tactic ledger records the proof
extraction and its two applications.

All three new Blueprint entries/proofs are `notready`. No local Lean build,
elaboration or declaration checker was run, following the user's instruction.
Hosted proof acceptance and integration remain pending. No placeholder,
proof bypass, source conclusion supplied as a premise, or persistent Lean
fixture was added.
