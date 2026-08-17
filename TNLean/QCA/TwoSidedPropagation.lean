/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.InversePropagation

/-!
# Two-sided finite propagation of quasi-local automorphisms

For a quasi-local star-automorphism, finite forward propagation already implies finite propagation
of the inverse. Consequently, the forward-only finite-propagation predicate is equivalent to the
two-sided convenience predicate. A forward neighborhood and its reflection can be enlarged to one
common neighborhood, and then to a symmetric integer interval.

The QCA definitions in the cited sources remain forward-only. The results here are derived
convenience statements using inverse propagation.

## Main results

* `SpinChain.PropagatesWithinTwoSided.of_forward` — a forward bound gives a common enlarged
  two-sided bound.
* `SpinChain.hasFinitePropagation_iff_hasTwoSidedFinitePropagation` — forward and two-sided finite
  propagation are equivalent for star-automorphisms.
* `SpinChain.HasFinitePropagation.exists_common_twoSided_neighborhood` — finite forward
  propagation admits a common neighborhood for the automorphism and its inverse.
* `SpinChain.HasFinitePropagation.exists_twoSided_symmetric_Icc` — the common neighborhood can be
  chosen to be a symmetric integer interval.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2298.
* Schumacher--Werner, quant-ph/0405174, Lemma 5, Theorem 6, and Corollary 7.
-/

open scoped Pointwise

namespace SpinChain

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 : Finset ℤ}

namespace PropagatesWithinTwoSided

/-- A forward propagation bound by \(\mathcal N\) gives a common two-sided bound after enlarging
to \(\mathcal N\cup(-\mathcal N)\).

The inverse bound is first derived on the reflected neighborhood. This avoids asserting a generally
unavailable common bound on the original, possibly nonsymmetric, neighborhood. -/
theorem of_forward (hω : PropagatesWithin ω 𝓝) :
    PropagatesWithinTwoSided ω (𝓝 ∪ (-𝓝)) :=
  of_reflected hω hω.symm

end PropagatesWithinTwoSided

/-- Finite forward propagation is equivalent to two-sided finite propagation for quasi-local
star-automorphisms.

The forward condition is the locality condition in arXiv:1703.09188, Appendix, line 2298, and
Schumacher--Werner, Definition 1. The reverse implication uses the first projection; the forward
implication uses derived inverse locality. -/
theorem hasFinitePropagation_iff_hasTwoSidedFinitePropagation :
    HasFinitePropagation ω ↔ HasTwoSidedFinitePropagation ω :=
  ⟨fun hω ↦ ⟨hω, hω.symm⟩, And.left⟩

namespace HasFinitePropagation

/-- Finite forward propagation admits one common finite neighborhood for an automorphism and its
inverse.

This combines derived inverse finite propagation with the common-neighborhood enlargement for
separately supplied bounds. -/
theorem exists_common_twoSided_neighborhood (hω : HasFinitePropagation ω) :
    ∃ 𝓝 : Finset ℤ, PropagatesWithinTwoSided ω 𝓝 :=
  (hasFinitePropagation_iff_hasTwoSidedFinitePropagation.mp hω).exists_common_neighborhood

/-- Finite forward propagation admits a common symmetric-interval neighborhood for an
automorphism and its inverse. -/
theorem exists_twoSided_symmetric_Icc (hω : HasFinitePropagation ω) :
    ∃ R : ℕ, PropagatesWithinTwoSided ω (Finset.Icc (-(R : ℤ)) (R : ℤ)) :=
  (hasFinitePropagation_iff_hasTwoSidedFinitePropagation.mp hω).exists_symmetric_Icc

end HasFinitePropagation

end SpinChain
