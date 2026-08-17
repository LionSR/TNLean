/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.InversePropagation

/-!
# One-dimensional quantum cellular automata

A one-dimensional quantum cellular automaton (QCA) is a translation-covariant star-automorphism
of the quasi-local observable algebra with finite forward propagation. This file packages those two
conditions and records its basic interface, the identity example, and closure under composition
and inversion.

## Main definitions

* `SpinChain.IsQCA` — translation covariance together with finite forward propagation.

## Main results

* `SpinChain.isQCA_iff` — the exact unfolding of the QCA predicate.
* `SpinChain.IsQCA.trans` — forward composition of QCAs is a QCA.
* `SpinChain.IsQCA.symm` — the inverse of a QCA is a QCA.
* `SpinChain.isQCA_refl` — the identity star-automorphism is a QCA.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2298.
-/

namespace SpinChain

/-- A one-dimensional quantum cellular automaton is a translation-covariant star-automorphism of
the quasi-local observable algebra with finite forward propagation.

Source: arXiv:1703.09188, Appendix, line 2298. -/
def IsQCA {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) : Prop :=
  TranslationCovariant ω ∧ HasFinitePropagation ω

/-- The exact characterization of a QCA by translation covariance and finite forward propagation.

Source: arXiv:1703.09188, Appendix, line 2298. -/
theorem isQCA_iff {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) :
    IsQCA ω ↔ TranslationCovariant ω ∧ HasFinitePropagation ω :=
  Iff.rfl

namespace IsQCA

variable {d : ℕ} [NeZero d]
  {ω η : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- Build a QCA from translation covariance and finite forward propagation.

Source context: arXiv:1703.09188, Appendix, line 2298. -/
theorem mk (hcov : TranslationCovariant ω) (hprop : HasFinitePropagation ω) : IsQCA ω :=
  ⟨hcov, hprop⟩

/-- A QCA is translation covariant.

Source context: arXiv:1703.09188, Appendix, line 2298. -/
theorem translationCovariant (hω : IsQCA ω) : TranslationCovariant ω :=
  hω.1

/-- A QCA has finite forward propagation.

Source context: arXiv:1703.09188, Appendix, line 2298. -/
theorem hasFinitePropagation (hω : IsQCA ω) : HasFinitePropagation ω :=
  hω.2

/-- Forward composition of quantum cellular automata is a quantum cellular automaton.

Here `ω.trans η` first applies `ω` and then `η`.

Source context: arXiv:1703.09188, Appendix, line 2298; this closure property is not stated
separately there. -/
theorem trans (hω : IsQCA ω) (hη : IsQCA η) : IsQCA (ω.trans η) :=
  ⟨TranslationCovariant.trans hω.translationCovariant hη.translationCovariant,
    HasFinitePropagation.trans hω.hasFinitePropagation hη.hasFinitePropagation⟩

/-- The inverse of a quantum cellular automaton is a quantum cellular automaton.

The QCA definition is forward-only. Inverse locality is a derived consequence, corresponding to
Schumacher--Werner, Lemma 5, Theorem 6, and Corollary 7. -/
theorem symm (hω : IsQCA ω) : IsQCA ω.symm :=
  ⟨hω.translationCovariant.symm, hω.hasFinitePropagation.symm⟩

end IsQCA

/-- The identity star-automorphism of the quasi-local algebra is a QCA.

Its propagation neighborhood is the singleton \(\{0\}\).

Source context: arXiv:1703.09188, Appendix, line 2298. -/
theorem isQCA_refl {d : ℕ} [NeZero d] :
    IsQCA (StarAlgEquiv.refl ℂ (QuasiLocalAlgebra d)) := by
  refine IsQCA.mk translationCovariant_refl ⟨{0}, ?_⟩
  intro Λ x hx
  change QuasiLocalSupportedIn x (regionSumset Λ {0})
  simpa only [regionSumset_zero_right] using hx

end SpinChain
