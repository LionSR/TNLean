# Actual MPU-to-QCA construction

Source: arXiv:1703.09188, canonical replacement lines 257–294 and 319–356,
standard form lines 378–427 and 563–622, Appendix 2292–2306. Parent draft
#10337 provides actual finite buffering, completed forward maps, covariance
and finite propagation. This child supplies actual inverses and the bare-MPU
construction.

FiniteChainAdjoint proves actual physical-adjoint finite matrices are
adjoint matrices and their conjugations are mutual inverses for every
N>1 on the same anchored chain. CanonicalQuasiLocalAction derives concrete
standard forms for a canonical-form-II tensor and its physical adjoint
from existing source theorems. Their actual forward maps are mutual
inverses: one common chain buffers the input and its derived output
support, faithful finite-region embedding identifies the finite output,
and actual finite unitary conjugations cancel. Density completes the two
inverse identities. The resulting star-automorphism has derived covariance,
propagation and actual finite evaluation, with 4k≤4D²≤4D⁴.

The bare wrapper uses the already integrated theorem
MPOTensor.IsMPU.exists_reduced_cfii_representative from
ReducedCanonicalRepresentative.lean, which returns an actual CFII tensor
of positive bond dimension Dred≤D with identical positive-length periodic
operators. Issue #7065 is closed and this supplier is present; earlier notes
calling it missing are superseded. The wrapper transports only actual
periodic matrices at N>1 and enlarges 4Dred⁴≤4D⁴. It makes no claim about
selected source factors, ranks, or a same-bond gauge.

The final public theorem exists_isQCA_of_isMPU assumes only a nonempty
physical alphabet and the bare MPU property. Bond positivity is derived by
IsMPU.neZero_bond. The positive physical convention is explicit because the
quasi-local algebra requires it and bare IsMPU can be vacuous at d=0.
The actual object mpuQuasiLocalEquiv is a star-automorphism with IsQCA,
source radius and exact original-site finite-chain formula for every fully
buffered interval and all N>1. No CFII, supplied standard form, adjoint data,
inverse-support, compatibility, covariance, output-support or divisibility
premise is added.

The canonical intermediate result has a scope marker; the final bare result
eliminates that restriction through the existing representative theorem.
The historical gap note is updated to state that the source-faithful proof
is written, while verification and integration remain pending. Neither
#7013 nor #7040 is closed, and no MPU/QCA index comparison is asserted.

All proof bodies are complete without placeholders or bypasses. Native
source/import/roles/prose/format/integrity/tactic/whitespace checks are used.
No local Lean invocation/build/checkdecls or cache mutation. All three new
Blueprint entries remain notready until hosted verification.
