# Spin-chain exchange generalized to an operator family

This audit records the removal and renaming of spin-1/2 declarations, and is the
audit note required by `docs/project_conventions.md` §Style. All non-`Archive`
uses are migrated, no blueprint `\lean{...}` tag cites a removed name, and no
compatibility alias is kept.

The exchange interaction, the one-site operators and the total spin were defined
only for the spin-1/2 operators in `TNLean/MPS/Examples/SpinHalf.lean`, and the
AKLT development needed a copy for spin 1. They now live once in
`TNLean/MPS/Examples/SpinOperator.lean`, parameterized by an operator family
`S : Fin 3 → Matrix (Fin d) (Fin d) ℂ`. The spin-1/2 and spin-1 chains pass
`spinHalfOperator` and `spinOneOperator`.

## Removed or changed declarations and their replacements

- `MPSTensor.spinExchange j k` (spin-1/2 only) becomes `MPSTensor.spinExchange S j k`;
  spin-1/2 uses are `spinExchange spinHalfOperator j k`.
- `MPSTensor.spinExchange_apply` (the spin-1/2 formula \(\tfrac12P_{jk}-\tfrac14\)) is
  renamed `MPSTensor.spinExchange_spinHalfOperator_apply`. The name
  `MPSTensor.spinExchange_apply` now denotes the general coordinate formula.
- `MPSTensor.spinSite α j` is replaced by `MPSTensor.siteOperator (S α) j`, and
  `spinSite_apply` by `siteOperator_apply`.
- `MPSTensor.sum_spinSite_comp_of_ne` and `MPSTensor.sum_spinSite_comp_self` are replaced
  by `MPSTensor.sum_siteOperator_comp_of_ne` and `MPSTensor.sum_siteOperator_comp_self`.
  The latter takes the Casimir identity `∑ α, S α * S α = c • 1` as a hypothesis.
- `MPSTensor.totalSpin α` and `MPSTensor.totalSpinSq` take the operator family as an
  explicit first argument, and `MPSTensor.totalSpinSq_eq` takes the Casimir identity.
- `MPSTensor.spinHalfOperator_sum_mul_self` is restated in matrix form,
  `∑ α, spinHalfOperator α * spinHalfOperator α = (3 / 4 : ℂ) • 1`.

The private per-example transport lemma `majumdarGhoshHamiltonian_apply_eq_smul_iff`
in `TNLean/MPS/Examples/MajumdarGhoshLowerBound.lean` is removed. Its role is taken
by the shared lemmas of `TNLean/MPS/ParentHamiltonian/ShiftedParentHamiltonian.lean`.
