/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Injectivity
import TNLean.MPS.Core.Word

/-!
# Injectivity and normality of matrix product tensors

The injectivity and normality predicates for a matrix product tensor are the
corresponding finite-family predicates. This file preserves their established
MPS names.

## Main declarations

* `MPSTensor.IsInjective` — the one-site matrices span the full matrix algebra
* `MPSTensor.IsNBlkInjective` — words of length $N$ span the full matrix algebra
* `MPSTensor.IsNormal` — block injectivity holds at some positive length
-/

namespace MPSTensor

export Kraus (IsInjective IsNBlkInjective IsNormal isNBlkInjective_one_of_isInjective
  isNormal_iff neZero_d_of_isInjective)

namespace IsInjective

export Kraus.IsInjective (isNormal smul span_eq_top)

end IsInjective

namespace IsNBlkInjective

export Kraus.IsNBlkInjective (span_eq_top)

end IsNBlkInjective

end MPSTensor
