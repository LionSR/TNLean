# One constant family parametrized by the crossing count

Date: 2026-10-22. Issue: #9884.

The chain constants `chainBudgetConst`, `chainShellConst` and `chainAreaLawConst` and the
full-window constants `windowBudgetConst`, `windowShellConst` and `windowAreaLawConst` used
the same three formulas and differed only in the number `N` of supports split by an
interval: `N = chainCrossConst R` for the chain and `N = 2 * R` for full windows. Each
formula is now written once, as `cutBudgetConst N q R`, `cutShellConst N q R` and
`cutAreaLawConst N q R`. The chain and window constants are those definitions at the two
values of `N`, keep their names, and unfold to their previous values with the same casts,
so no theorem statement changes. No deprecated aliases are kept.

## Removed declarations and replacements

| Removed | Replacement |
|---|---|
| `TNLean.MPS.AreaLaw.windowShellConst q R` | `TNLean.MPS.AreaLaw.cutShellConst (2 * R) q R` |
