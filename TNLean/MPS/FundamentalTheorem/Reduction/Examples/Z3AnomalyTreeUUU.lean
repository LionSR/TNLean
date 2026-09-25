/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalyTreeData

/-!
# Local identities of the fusion trees of the triple `(g,g,g)`

The two-letter intertwining identities and the single-letter relation of the two fusion
trees of the triple `(g,g,g)` for `Z3Anomalous.family`, checked over `ℤ[ω]` by `decide +kernel`.
-/

open scoped Matrix
open MPSTensor EisensteinInt

namespace Z3Anomalous

set_option maxRecDepth 8000 in
/-- The tree of `(g,g,g)` fusing the first two factors first intertwines two letters of the triple
product with the identity tensor. -/
theorem leftUUU_pair : ∀ a b : Fin 9,
    leftUUUEis * tripleUUUTable a * tripleUUUTable b =
      identityEisMPS a * leftUUUEis * tripleUUUTable b := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- The tree of `(g,g,g)` fusing the last two factors first intertwines two letters of the triple
product with the identity tensor. -/
theorem rightUUU_pair : ∀ a b : Fin 9,
    rightUUUEis * tripleUUUTable a * tripleUUUTable b =
      identityEisMPS a * rightUUUEis * tripleUUUTable b := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- On one letter of the triple product, the two trees of `(g,g,g)` differ by `-1 - ω`. -/
theorem UUU_letter : ∀ a : Fin 9,
    leftUUUEis * tripleUUUTable a =
      (⟨-1, -1⟩ : EisensteinInt) • (rightUUUEis * tripleUUUTable a) := by
  decide +kernel

end Z3Anomalous
