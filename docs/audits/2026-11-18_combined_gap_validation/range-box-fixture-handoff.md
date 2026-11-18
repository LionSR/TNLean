# Range-square and box-supremum regression handoff

Base: e05d7f8907e0a4ebbcf4ad960f48958664eb7d3f.
This branch changes test fixtures and this handoff only, with no production edits.

## Fixtures and intended assertions

- `scripts/range_square_zero_gap_regression.lean`: an actual invocation of
  `IsSquareGroundState.isRangeSquareGroundState` on a one-site q=2 zero
  Hamiltonian at Delta=0, with a concrete normalized coordinate vector.
- `scripts/box_supremum_zero_gap_regression.lean`: a zero Hamiltonian on a
  singleton physical domain with q=2, Delta=0; its concrete normalized state
  contributes an actual value to `boxEntropyValues` and is bounded by
  `regionalEntropy_le_boxEntropy`. The rectangle has size one and the physical
  cut is empty. At r=0, `IntRect.one_le_size` rules out every witness, making
  the value set empty and its real supremum zero. The final call to
  `regionalEntropy_le_of_boxEntropy_power` retains the uniform box-power
  premise explicitly. No unconditional nonpositive-gap area law is asserted.

## Validation boundary

The full fixtures are **not yet Lean-validated**: the two owner oleans are
absent in the author environment. No dependency build was run. The zero
interaction/state, PSD, ground-space and safety helper proofs were checked
separately with the repository strict flags using already available imports;
those passes do not validate the final wrapper/supremum calls.

The existing CI selector was tested with each fixture changed, each direct
owner changed, and InitialBoxEstimate changed; it selects the correct fixture.
No selector policy or production source was modified.

## Consumer targets for the production-validation worker

- TNLean.PEPS.Approximation.RangeSquareGroundState
- TNLean.PEPS.AreaLaw.Scan.BoxEntropySupremum

The latter currently lacks InitialBoxEstimate, RegionalStates, RotatedChainRule,
and SafeBoxChildren in the author cache. Resolve the production dependency
closure through normal Lake validation in the assigned worker, not by copying
or fabricating oleans. Then run both files with `ci_lean_checks.run_batch` or
its exact strict Lean flags. Keep the original 50/89 and 27/52 production
counts unchanged until that worker provides actual new results.
