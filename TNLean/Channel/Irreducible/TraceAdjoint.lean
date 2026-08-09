/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.KrausSetup
import TNLean.MPS.Core.TransferChannel

/-!
# Trace-adjoint identity for transfer maps

For a transfer map $E(X)=\sum_i K_iXK_i^*$, the adjoint trace pairing reads
$$
\operatorname{tr}(\rho E(X))
  = \operatorname{tr}\!\left(\sum_i K_i^*\rho K_i\,X\right).
$$

## Main declaration

* `trace_mul_transferMap_adjoint`: the adjoint trace-pairing identity in MPS transfer-map
  notation.
-/
