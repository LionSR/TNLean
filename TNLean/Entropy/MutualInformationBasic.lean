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

## Main declaration

* `Entropy.mutualInformation` is the namespaced alias of
  `_root_.mutualInformation`.
-/

namespace Entropy

/-- **Quantum mutual information** between subsystems A and B,
namespaced alias.

`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` measures the total correlations
between A and B. Definitionally equal to `_root_.mutualInformation`.

Source: blueprint `def:entropy_mutual_information`. -/
noncomputable alias mutualInformation := _root_.mutualInformation

end Entropy
