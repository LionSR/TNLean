# Period bound and W-state chain lengths

`MPSTensor.IsPeriodic.period_le_bondDim` replaces
`MPSTensor.IsPeriodic.period_le_sq`: the existing cyclic-sector decomposition
gives nonzero sector dimensions whose sum is the bond dimension, hence
`m ≤ D` instead of `m ≤ D²`. All uses and blueprint links of the weaker
declaration are migrated. No compatibility alias is retained, following
`docs/project_conventions.md`.

`MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor` states the existing
fifth-degree W-state bound for `N ≥ 2` when no integer between `2` and `D`
divides `N`. The prior prime-length theorem remains a derived consequence.
The general quantum Wielandt estimate and resulting exponent are unchanged.

The mathematical statements and complete proof mechanisms appear in
`blueprint/src/chapter/ch15_examples_w_state.tex`, under
`thm:periodic_period_le_bondDim` and `thm:w_state_no_small_divisor_bound`.
The source-comparison note `docs/paper-gaps/rmp_w_state_ti_bound.tex` records
the remaining restriction on chain lengths. No literature-novelty claim is made.
