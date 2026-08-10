/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.Entropy

/-!
# Quantum mutual information

This module exposes the bipartite mutual information defined in
`TNLean.Analysis.Entropy` under the `Entropy` namespace without importing
strong subadditivity or its consequences.

## Main definitions

* `Entropy.mutualInformation` is the namespaced alias of
  `_root_.mutualInformation`.

## Main results

* `Entropy.mutualInformation_congr` shows that mutual information respects
  equality of the matrix independently of its Hermiticity witness.
-/

namespace Entropy

/-- **Quantum mutual information** between subsystems A and B,
namespaced alias.

`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` measures the total correlations
between A and B. Definitionally equal to `_root_.mutualInformation`.

Source: blueprint `def:entropy_mutual_information`. -/
noncomputable alias mutualInformation := _root_.mutualInformation

/-- Mutual information is independent of the Hermiticity witness and respects
equality of the underlying bipartite matrix. -/
theorem mutualInformation_congr
    {dA dB : ℕ}
    {ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : ρ = σ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    mutualInformation ρ hρ = mutualInformation σ hσ := by
  subst σ
  rfl

end Entropy
