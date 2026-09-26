/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic

/-!
# Product vectors

The product vector $\lvert\phi^1\rangle\otimes\cdots\otimes\lvert\phi^N\rangle$ of a chain
of `N` sites, written in the computational basis as a function on configurations.

## Main definitions

* `MPSTensor.productVector` : the product vector $\bigotimes_s\lvert\phi^s\rangle$.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Appendix A, "Product states",
  `Papers/2011.12127/TN-Review-main.tex` lines 2330–2333.
-/

namespace MPSTensor

variable {d N : ℕ}

/-- Source: arXiv:2011.12127, lines 2330–2333. The product vector
$\lvert\phi^1\rangle\otimes\cdots\otimes\lvert\phi^N\rangle$, with
$\lvert\phi^s\rangle=\sum_i\phi^s_i\lvert i\rangle$, in the computational basis: its
coefficient on $\lvert i_1,\dots,i_N\rangle$ is $\phi^1_{i_1}\cdots\phi^N_{i_N}$. -/
def productVector (φ : Fin N → Fin d → ℂ) : Cfg d N → ℂ :=
  fun σ => ∏ s, φ s (σ s)

end MPSTensor
