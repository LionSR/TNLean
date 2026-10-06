# Periodic String Order thermodynamic limits

## Scope

For faithful pure canonical MPS data, the actual normalized expectation of a fixed physical block on a growing periodic ring converges to its stationary transfer value. Periodic squared norms tend to one, so eventual nonvanishing is derived. The block and middle string length are fixed before the ambient-ring limit.

The full-ring observable has growing support and a different closure. Its exact normalized expectation is the twisted/ordinary transfer-trace ratio and equals the intertwiner phase to the ring length at nonzero lengths. The phase is retained in the spectral alternatives and nonconvergence statement. No limit exchange, uniform rate, Hamiltonian-gap implication, or mixed-state decomposition theorem is asserted.

The existing paper-gap note is extended with this closure distinction and the full-ring phase qualification. Its overall status remains open. The literal source criterion and the earlier projective correction are unchanged.

## Ownership and regressions

- Reuse the accepted QICLean pointwise-convergence theorem; no generic trace-convergence theorem is added to TNLean.
- Relocate `inner_mpvState_self_eq_trace` unchanged from `WindowClustering` to `WindowCorrelator`, preserving its public name/signature and replacing three repeated proofs.
- Reuse the existing canonical four-letter tensor for the exact nonreal phase and nonconvergence examples.
- Register `TNLeanTest/PeriodicStringExpectations.lean` in PR CI with strict options and eleven durable `#guard_msgs` proof-dependency checks.
- Cover zero middle length, actual normalization, and a non-Hermitian fixed matrix unit without extra hypotheses.

## Actual validation

Exact source hashes, commands, artifact hashes, and elapsed times are recorded in `2026-10-06_periodic_string_validation.json`. The final strict logs are empty. Every invocation used one Lean thread and a 90-second bound. The shared baseline artifacts were not overwritten after relocating the lower owner; the final checks used a private unified import overlay.

- `TNLean.MPS.Preparation.WindowCorrelator`: passed in 8.014s; source SHA-256 `b9f75bb238c54497fd1d4a5dc9a07e7375cda3b3874463a89ac04dfc3b26b831`
- `TNLean.MPS.Symmetry.PeriodicPhysicalString`: passed in 8.014s; source SHA-256 `b31fabb7bddb167b10c099e020233b2f24f46bffe19eecc7f69689951d4aa781`
- `TNLean.MPS.Symmetry.PeriodicFullRingString`: passed in 8.016s; source SHA-256 `910869cc18db1554649ebb081856e67e87ebbda6a7cb733dcdfe095d2ea8223e`
- `TNLean.MPS.Examples.PeriodicFullRingPhase`: passed in 6.011s; source SHA-256 `d973edac7a28706c200a665773d391d496b78d750dbfbdeb900452ddd948a523`
- `TNLeanTest.PeriodicStringExpectations`: passed in 6.011s; source SHA-256 `603453835aa1be7f9d03d9e0fbe6193aac70438f9a60b9b9c29c06bb28a6700e`

All eleven guarded theorem inspections have exactly `propext`, `Classical.choice`, and `Quot.sound`. Thirty-nine previously missing unchanged prerequisites were restored with their package options, without adding warning-as-error requirements to unchanged code and without rebuilding Mathlib.

Actual diagnostics led only to explicit section-variable/dimension annotations, `Matrix.of` for singleton observable typing, pointwise quotient reductions, and removal of unused simplification arguments. No hypotheses or conclusions were weakened.

## Blueprint and native diagram

- Canonical source synchronization passes with the accepted dependency source snapshot. All eighteen new public theorems have blueprint references; the private source-specific trace consumer is intentionally not registered.
- The periodic-ring picture uses the pinned native tenkz kernel in the existing String Order owner. It has two separately closed virtual rows, physical twist insertions, and no stationary-density cup.
- The picture compiled and was visually inspected. The event audit reports one picture, zero hard findings, and zero advisories.
- New theorem readiness markers remain unadvanced pending the remaining integration gates.

Pinned latexindent 3.24.7 was applied to all four changed TeX sources. The
full blueprint formatting check passes. The docbuild manifest agrees with the
root project on all twelve packages; no dependency pin was changed.

## Remaining gates

`WindowClustering` is changed only by deleting the relocated lemma. Source review confirms its unchanged transitive import of `WindowCorrelator`, but its direct local closure requires 390 additional uncached project modules. That owner and the full aggregate/root build remain remote-CI gates; no cold closure was started merely to claim a pass.

Direct strict checks are not a normal Lake/root build. Full `checkdecls`, web rendering, and complete blueprint/paper-gap PDF checks remain pending. The local image lacks `dsfont.sty`, a pdfLaTeX format for the paper-gap note, and the leanblueprint/plasTeX toolchain. The clean native diagram render is the only complete local typesetting claim. Ordinary source sync and scoped public-declaration coverage are distinct checks; no reverse-diff coverage pass is claimed.

The batch retains the accepted QICLean pin `8d5389d23c8e675a0117442e1a0d2c683a4bad41` and does not depend on the separate continuous-symmetry changes. No publication is recorded by this audit.
