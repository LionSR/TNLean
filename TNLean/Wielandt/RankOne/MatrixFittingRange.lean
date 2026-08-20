/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixFittingRange

/-!
# Matrix fitting-range compatibility names

This module preserves the established matrix-product-tensor names for the neutral matrix
results about injectivity on stabilized ranges.
-/

namespace MPSTensor.WielandtRankOne

@[deprecated Matrix.isUnit_restrict_range_toLin'_pow (since := "2026-08-20")]
alias isUnit_restrict_range_toLin'_pow := Matrix.isUnit_restrict_range_toLin'_pow

@[deprecated Matrix.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow (since := "2026-08-20")]
alias vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow :=
  Matrix.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow

@[deprecated Matrix.eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow (since := "2026-08-20")]
alias matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow :=
  Matrix.eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow

end MPSTensor.WielandtRankOne
