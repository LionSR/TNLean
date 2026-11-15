# Intrinsic time-reversal quantization and deformation

Source: `Papers/1703.09188/paper_v2.tex:1595–1631`,
`eq:sigma-from-trace` and `prop:sigma-well-defined`.
Issue: #9880; the separate local characterization is #7020.

## Status and ownership checked on 2026-11-15

The GitHub main head is `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
#10311 merged on 2026-10-30, with merge commit
`3b2d2512ef79e134742b3009e5021b6ad40f7c84`. #10360 merged on
2026-10-31, with merge commit `948626749ede3be59159c86ce617b02192eceee7`.
Their intrinsic-trace identity and canonical supplied-gate local criterion
are existing results. #10392's intrinsic blocking-parity development is
also existing main infrastructure.

#9880 and #7020 remain open and have no GitHub assignee. #6024 remains
open without an assignee; #6140 remains open with assignee `LionSR`.
No ownership, assignment, or issue state is changed here. The existing
implementation owners retain their results. No continuous-standard-form
or continuous-source-data module is changed.

The local snapshot is older (`cbf482955`). The current main versions of
the touched source, blueprint, and gap-note files were read through the
GitHub connector. The published change must preserve the current-main QICLean
import, the supplied-action imports and chapter input, and the corrected
symmetry discussion reference. No dependency pin is changed. The current
main QICLean revision is `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`.

## New mathematical step

The existing canonical twisted-transfer proof obtains

    T = η G† E G,   η² = 1,   FT = TF,

where `F` exchanges the two bond factors and `E` is the actual normalized
transfer. Its stabilized power is `P = E^J = |r)(l|`, with
`(l|r) = 1`. The commuting-weighted-trace theorem already removes the
nilpotent transient and gives

    tr(F T^k) = η^k C,   C = tr(B P),   B = G F G†,   k > 0.

The missing observation is that `F² = 1`. Thus `B² = 1`, `BP = PB`, and
`(BP)² = P`. Since `BP` has an actual outer-product factorization,

    tr(BP)² = tr((BP)²) = tr(P) = 1.

Consequently **both** `η` and `C` are signs. The existing public phase
formula is strengthened by adding the conclusion `C = 1 ∨ C = -1`;
its hypotheses and all existing parity conclusions are preserved. The
virtual sign `η` is still not identified with the first intrinsic trace.
The proof reuses the existing comparison and stabilization; it does not
assume the desired sign quantization or infer ambient normality from cut ranks.

For any positive-dimensional MPU `W`, choose its existing reduced canonical
representative `V`. Positive-length periodic equality transfers actual
even-family adjoint symmetry to `V`, and equality at length two transfers
the intrinsic trace back to `W`. Thus

    intrinsicTimeReversalSign W ^ 2 = 1

holds with no canonical, simplicity, standard-form, factor, local-certificate,
or stabilization premise on `W`.

The intrinsic trace is already known to be continuous in the actual tensor.
On a continuous path of MPUs satisfying adjoint symmetry at every even
length greater than one, it therefore stays in `{1,-1}` and is constant.
Canonical representatives need not vary continuously: they are used only
inside the pointwise quantization proof.

For a supplied square standard form, the existing gate-to-intrinsic identity
gives sign quantization. Two supplied square forms at two points of the
path have equal gate traces. No forms are needed at intermediate points.

## Exact remaining boundary

This removes canonical scope and pointwise local-certificate hypotheses
from **intrinsic numerical deformation invariance**. It does not construct
the local unitary `x` or prove the literal four-spin equation for arbitrary
ambient supplied presentations. It also does not derive square intermediate
dimensions for every arbitrary supplied form. Those are still separate
parts of #7020. No transposition theorem is claimed.

The source-labelled and admissible umbrella entries remain `notready`.
The strengthened phase formula and new auxiliary entries also remain
`notready` pending kernel acceptance. No printed source statement is weakened,
no new assumption is hidden in a structure, and neither issue is closed.

## Validation

- Exact pinned Mathlib matrix outer-product and trace APIs, and current-main
  QICLean stabilization and exchange APIs, were inspected.
- Exact rational calculations verify 176 signed weighted-power identities
  in dimensions two through five, with nonzero nilpotent transients, both
  independent signs and orthogonal changes of coordinates. Negative controls
  show that dropping commutation or rank-one normalization invalidates the
  sign conclusion. These are supporting algebra checks, not Lean verification.
- Generated imports, mathematical-role classification, source declaration
  coverage, line width, placeholder scans and whitespace are checked separately.
  The full blueprint source scan cannot resolve dependency declarations when
  the QICLean and Mathlib checkouts are absent.
- Local Lean/Lake and `.lake` are absent. `lake exe cache get` exits 127;
  shell GitHub access fails with proxy HTTP 403. No Mathlib source build or
  dependency-pin change was attempted. Hosted acceptance remains required.

Assistance: OpenAI Codex (GPT-6) investigated the current status and wrote
the proofs, documentation and supporting algebra checks. No merge is requested.
