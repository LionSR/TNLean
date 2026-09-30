# Coincident-site spin exchange

Issue #8353 identified that the coordinate definition of `spinExchange` was
valid only at distinct sites. At coincident sites it gave the spin-one-half
value `1/4` instead of the Casimir value `3/4`.

The definition now sums compositions of site operators, as in the mathematical
definition. The existing coordinate formula `spinExchange_apply` requires
distinct sites; its spin-one-half, spin-one, and cyclic restriction callers
provide that condition. The total-spin expansion uses the same definition
on both diagonal and off-diagonal terms.

## Declaration changes

- `sum_siteOperator_comp_of_ne` is removed: its equality is now definitional,
  including at coincident sites.
- `sum_siteOperator_comp_self` is replaced by `spinExchange_self`, expressing
  the Casimir identity directly for `spinExchange`.
- No compatibility aliases are retained, following the project's policy for
  otherwise unused declarations. The blueprint references the replacement.

`TNLeanTest/SpinOperator.lean` checks the coincident-site Casimir values `3/4`
and `2` for spin one-half and spin one, respectively.
