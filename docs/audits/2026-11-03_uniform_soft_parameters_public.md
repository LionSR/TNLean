# Uniform numerical soft parameters

The numerical existence theorem in `ALVV/UniformPhysicalSoftCalibration.lean` is now public. Its statement and proof are unchanged. The existing physical-family theorem continues to call this same numerical theorem; no second calibration or physical family is introduced.

The choices precede the chain length and interactions. At fixed local dimension and positive gap, the soft order, scale, residual cutoff, filter degree and precision determine the same corrected residual and sampling budgets, and the same natural polynomial member-bond bound. This is an auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7 and Theorem 5.8 (`prop:Cheby-AGSP-eff`, `t:aisefficient`), local source lines 1311–1420. It does not identify the printed fourth-order choice or assert a running-time estimate. The existing soft-residual and cluster-approximation gap notes remain applicable.

No Mathlib source or shared cache was changed. The temporary inspection
commands were deleted. The corresponding blueprint now separates the numerical
lemma from its physical corollary.
