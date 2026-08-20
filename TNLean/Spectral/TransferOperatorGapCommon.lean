/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.SpectralRadius
import TNLean.Analysis.SpectralRadiusPowerDecay

/-!
# Common infrastructure for square and rectangular transfer gaps

Compatibility aliases preserve the former `MPSTensor` names of the general
spectral-radius results now in `TNLean.Analysis`.

## Main results

- `MPSTensor.geometric_bound_of_spectralRadius_lt_one`
- `MPSTensor.pow_tendsto_zero_of_spectralRadius_lt_one`
- `MPSTensor.IsIdempotentElem.eq_zero_of_spectralRadius_lt_one`
-/

namespace MPSTensor

/-! ### Compatibility aliases for spectral-radius results -/

@[deprecated _root_.geometric_bound_of_spectralRadius_lt_one (since := "2026-08-19")]
alias geometric_bound_of_spectralRadius_lt_one :=
  _root_.geometric_bound_of_spectralRadius_lt_one

@[deprecated _root_.pow_tendsto_zero_of_spectralRadius_lt_one (since := "2026-08-19")]
alias pow_tendsto_zero_of_spectralRadius_lt_one :=
  _root_.pow_tendsto_zero_of_spectralRadius_lt_one

@[deprecated _root_.IsIdempotentElem.eq_zero_of_spectralRadius_lt_one
  (since := "2026-08-19")]
alias IsIdempotentElem.eq_zero_of_spectralRadius_lt_one :=
  _root_.IsIdempotentElem.eq_zero_of_spectralRadius_lt_one

end MPSTensor
