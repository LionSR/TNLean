# Continuous support foundation for #6024 and #6140

This is auxiliary work on the two coordinated issues, not their completion.
The new Lean proof bodies await pinned-toolchain elaboration. The ten new
public declarations have separate blueprint entries marked `notready`.
Neither `coruvSF` nor the admissible continuous-standard-form statement is
marked proved, and no issue is closed.

Ownership and existing work were checked on 2026-11-15. Issue #6140 is assigned
to LionSR; #6024 is unassigned. Open-PR searches for `6024 OR 6140`, continuous
support, and standard form returned no competing PR. Existing projection-frame,
polar-normalization, reduced-operator, and simplicity proofs are reused.
No assignee is removed or changed.

The local checkout starts at `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.
Current main was checked at `eb588dc15332a3798431015e6c27ecbaf329b2d1`,
257 commits ahead. The edited blueprint and gap note and the reused
`GeneralIndexContinuity`, `SimpleSupportCompression`,
`ContinuousProjectionFrame`, and `IdempotentRankContinuity` modules are
byte-identical there. A current-main publication must preserve its added
imports and dependency pins; the old checkout's aggregator must not replace
the current one wholesale.

Lean and Mathlib remain v4.36.0-rc1, with Mathlib commit
`625d8914199bc567cca9b91f90e8e5afafa5ae51`. Current main pins QICLean at
`603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`; the checkout's older pin is
`c457682404aa548b4acd16ac27be5d3835e68892`. The used QICLean orthogonal
projection and reduced-projection modules are byte-identical at these pins.
No toolchain or dependency file is changed by this work.

`ContinuousSupportFrames.lean` constructs local full frames by projecting a
fixed base frame and using the existing continuous polar normalization.
Idempotence supplies local rank constancy. Applying the construction to the
projection and its complement gives an actual local unitary orbit lift with
identity at the base. Full frames on overlaps have continuous unitary changes
of coordinates `Jᴴ K`.

`ContinuousReducedSupport.lean` gives continuous rectangular tensor
compression. Under the actual support absorptions and continuity of the
actual reduced projection, it constructs local continuous reduced MPU tensors
with identical operators at every positive length. It also supplies the exact
unitary covariance on overlaps, positivity and continuity of compressed
ambient matrices, and simplicity under the existing rank-one-transfer
hypothesis. Equality at length zero is deliberately excluded.

The following hypotheses are retained explicitly:

- The reduced projection is continuous. Continuity of positive semidefinite
  matrices alone does not imply continuity of their supports, and constant
  source ranks do not automatically give this hypothesis.
- The two support absorptions hold for the actual tensor letters.
- Positivity on the reduced range uses the actual support projections of the
  supplied positive semidefinite matrices.
- The simplicity result uses the stated rank-one normalized transfer identity.

No continuous SVD, diagonalizing basis, canonical representative, gate family,
or sign supplier is assumed. The gap note includes an explicit positive
definite constant-rank matrix family with no continuous spectral basis at
zero; this rules out that proposed general matrix shortcut. It is not claimed
to be an MPU counterexample.

Remaining mathematical dependencies are as follows:

| Consumer | Remaining obligation |
| --- | --- |
| #6024 | Lift the actual tensor-product **gate** orbit, derive its continuity from the finite-chain operators, and join local lifts on the interval with compatible endpoints and the common blocking bound. A bond-support lift is a different result. |
| #6140 | Derive suitable continuous reduced support data from the source hypotheses, or bypass changes of minimal support; construct the required source data without a continuous spectral-basis assumption; transport through blocking, ancillas and symmetry comparison paths. Local reduced tensors are not continuous diagonal CFII data. |
| #7016 | Forward extraction of continuous standard-form gates with the specified endpoints still depends on #6024/#6140. Reverse reconstruction and the distinction between strict and stabilized equivalence remain separate. |
| #9880 | The merged intrinsic periodic-trace route already avoids continuous gate choices. Pointwise actual standard forms and local time-reversal certificates remain the relevant availability obligations; do not reintroduce a continuous-supplier dependency. |

Validation completed locally:

- Import aggregator generation/check: 94 generated aggregators, 5,045 production
  modules. All ten new public declarations have blueprint coverage.
- Source synchronization against an untouched snapshot: the same 563 unresolved
  references and 562 associated `leanok` references occur on both sides because
  dependency sources are absent. No new unresolved references or duplicate
  ownership tags are introduced. This is not a green full sync check.
- Blueprint role check and paper-gap declaration extraction pass.
- Numerical identities for local unitaries, frames, and coordinate covariance:
  220 checks, maximum Frobenius error `1.72e-14`, including zero/full ranks.
- Exact rational word traces: 340 positive-length words through length four,
  with noncommuting support projections. The zero-length exclusion and the
  oscillating spectral-projection example were also checked.
- New TeX sections compile independently with a minimal standard preamble.
  Full gap-note compilation is blocked by the existing `dsfont.sty` dependency
  under pdfLaTeX; LuaLaTeX stops at the existing `DeclareUnicodeCharacter` use.
- Tactic-pattern scan, changed-file integrity scan, and whitespace checks run.

These computations and source checks do not verify Lean proofs. Lean/Lake and
the dependency cache are absent; direct Git and Lean release downloads return
proxy HTTP 403. No local Lean build, strict elaboration, kernel axiom audit,
or full blueprint declaration check has run. Hosted acceptance, if obtained,
must be recorded against the exact published head separately.
