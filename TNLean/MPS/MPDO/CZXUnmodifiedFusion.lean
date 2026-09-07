/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXCompletion

/-!
# The two unmodified CZX fusion contractions

For the nonidentity group label $g$, the printed unmodified fusion circuit
$\lambda^R_{g,g}$ of arXiv:2502.20257, lines 4989--5067, sends the defect
vectors $v(g,g,0)$ and $v(g,g,1)$ to $-v(e,e,0)$ and $v(e,e,1)$, respectively.
Here $e$ is the identity label and $v$ denotes the existing tensor-derived
`MPOTensor.CZX.defectVector`. These are the two displayed contractions, proved
by evaluating the monomial formula on their computational basis vectors.

This operator is `lambda`, not `circuitTuple gen gen`: the latter uses
`tildeLambda`, modified by the factor `pauliZ 0` (lines 5179--5183).
Only the two physical vector identities are asserted here; no identification
with virtual caps, common tensor-derived L-symbol, or associator is asserted.
-/

noncomputable section

namespace MPOTensor.CZX

open Matrix Complex

/-- The first contraction of the printed unmodified fusion circuit in
arXiv:2502.20257, lines 4989--5067: $\lambda^R_{g,g}v(g,g,0)=-v(e,e,0)$. -/
theorem matterMatrix_lambda_mulVec_defectVector_zero :
    matterMatrix lambda *ᵥ defectVector gen gen 0 = (-1 : ℂ) • defectVector 1 1 0 := by
  have hperm : barFlip ![1, 1, 0, 0] = ![0, 0, 0, 0] := by decide
  have hphase : hExponent ![1, 1, 0, 0] = 0 := by decide
  rw [defectVector_gen_gen_zero, defectVector_one_one_zero, mulVec_smul,
    lambda_eq, matterMatrix_monomial_mulVec_matterKet, hperm, hphase, smul_smul]
  simp

/-- The second contraction of the printed unmodified fusion circuit in
arXiv:2502.20257, lines 4989--5067: $\lambda^R_{g,g}v(g,g,1)=v(e,e,1)$. -/
theorem matterMatrix_lambda_mulVec_defectVector_one :
    matterMatrix lambda *ᵥ defectVector gen gen 1 = defectVector 1 1 1 := by
  have hperm : barFlip ![0, 0, 1, 1] = ![1, 1, 1, 1] := by decide
  have hphase : hExponent ![0, 0, 1, 1] = 1 := by decide
  rw [defectVector_gen_gen_one, defectVector_one_one_one, mulVec_smul,
    lambda_eq, matterMatrix_monomial_mulVec_matterKet, hperm, hphase, smul_smul]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]

end MPOTensor.CZX
