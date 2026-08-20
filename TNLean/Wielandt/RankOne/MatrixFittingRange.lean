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

namespace MPSTensor

@[deprecated Matrix.pow_mulVec_eq_smul_of_mulVec_eq_smul (since := "2026-08-20")]
alias pow_mulVec_eq_smul_of_mulVec_eq_smul :=
  Matrix.pow_mulVec_eq_smul_of_mulVec_eq_smul

@[deprecated Matrix.mem_range_toLin'_of_eigenvector (since := "2026-08-20")]
alias mem_range_toLin'_of_eigenvector := Matrix.mem_range_toLin'_of_eigenvector

@[deprecated Matrix.mem_range_vecMulLinear_of_transpose_eigenvector (since := "2026-08-20")]
alias mem_range_vecMulLinear_of_transpose_eigenvector :=
  Matrix.mem_range_vecMulLinear_of_transpose_eigenvector

@[deprecated Matrix.mem_range_toLin'_pow_of_eigenvector (since := "2026-08-20")]
alias mem_range_toLin'_pow_of_eigenvector := Matrix.mem_range_toLin'_pow_of_eigenvector

@[deprecated Matrix.mem_range_vecMulLinear_pow_of_transpose_eigenvector
  (since := "2026-08-20")]
alias mem_range_vecMulLinear_pow_of_transpose_eigenvector :=
  Matrix.mem_range_vecMulLinear_pow_of_transpose_eigenvector

@[deprecated Matrix.fitting_nilpotent_bound (since := "2026-08-20")]
alias fitting_nilpotent_bound := Matrix.fitting_nilpotent_bound

@[deprecated Matrix.fitting_nilpotent_pow_eq_zero (since := "2026-08-20")]
alias fitting_nilpotent_pow_eq_zero := Matrix.fitting_nilpotent_pow_eq_zero

end MPSTensor

namespace MPSTensor.WielandtRankOne

@[deprecated Module.End.range_pow_le_iSup_maxGenEigenspace_ne_zero
  (since := "2026-08-20")]
alias range_pow_le_iSup_maxGenEigenspace_ne_zero :=
  Module.End.range_pow_le_iSup_maxGenEigenspace_ne_zero

@[deprecated Module.End.iSup_maxGenEigenspace_ne_zero_le_range_pow
  (since := "2026-08-20")]
alias iSup_maxGenEigenspace_ne_zero_le_range_pow :=
  Module.End.iSup_maxGenEigenspace_ne_zero_le_range_pow

@[deprecated Module.End.range_pow_eq_iSup_maxGenEigenspace_ne_zero
  (since := "2026-08-20")]
alias range_pow_eq_iSup_maxGenEigenspace_ne_zero :=
  Module.End.range_pow_eq_iSup_maxGenEigenspace_ne_zero

@[deprecated Module.End.mapsTo_range_pow (since := "2026-08-20")]
alias mapsTo_range_pow := Module.End.mapsTo_range_pow

@[deprecated Module.End.ker_le_maxGenEigenspace_zero (since := "2026-08-20")]
alias ker_le_maxGenEigenspace_zero := Module.End.ker_le_maxGenEigenspace_zero

@[deprecated Module.End.disjoint_ker_iSup_maxGenEigenspace_ne_zero
  (since := "2026-08-20")]
alias disjoint_ker_iSup_maxGenEigenspace_ne_zero :=
  Module.End.disjoint_ker_iSup_maxGenEigenspace_ne_zero

@[deprecated Module.End.disjoint_ker_range_pow (since := "2026-08-20")]
alias disjoint_ker_range_pow := Module.End.disjoint_ker_range_pow

@[deprecated Module.End.ker_restrict_range_pow_eq_bot (since := "2026-08-20")]
alias ker_restrict_range_pow_eq_bot := Module.End.ker_restrict_range_pow_eq_bot

@[deprecated Module.End.isUnit_restrict_range_pow (since := "2026-08-20")]
alias isUnit_restrict_range_pow := Module.End.isUnit_restrict_range_pow

@[deprecated Matrix.isUnit_restrict_range_toLin'_pow (since := "2026-08-20")]
alias isUnit_restrict_range_toLin'_pow := Matrix.isUnit_restrict_range_toLin'_pow

@[deprecated Matrix.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow (since := "2026-08-20")]
alias vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow :=
  Matrix.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow

@[deprecated Matrix.eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow (since := "2026-08-20")]
alias matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow :=
  Matrix.eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow

end MPSTensor.WielandtRankOne
