/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalyTreeData

/-!
# Local identities of the fusion trees of the triple `(g,g²,g)`

The two-letter intertwining identities and the single-letter relation of the two fusion
trees of the triple `(g,g²,g)` for `Z3Anomalous.family`, checked over `ℤ[ω]` by `decide +kernel`.
-/

open scoped Matrix
open MPSTensor EisensteinInt

namespace Z3Anomalous

set_option maxRecDepth 8000 in
/-- The tree of `(g,g²,g)` fusing the first two factors first intertwines two letters of the triple
product with `U`. -/
theorem leftUDU_pair : ∀ a b : Fin 9,
    leftUDUEis * tripleUDUTable a * tripleUDUTable b =
      uEisMPS a * leftUDUEis * tripleUDUTable b := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- The tree of `(g,g²,g)` fusing the last two factors first intertwines two letters of the triple
product with `U`. -/
theorem rightUDU_pair : ∀ a b : Fin 9,
    rightUDUEis * tripleUDUTable a * tripleUDUTable b =
      uEisMPS a * rightUDUEis * tripleUDUTable b := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- On one letter of the triple product, the two trees of `(g,g²,g)` agree. -/
theorem UDU_letter : ∀ a : Fin 9,
    leftUDUEis * tripleUDUTable a = rightUDUEis * tripleUDUTable a := by
  decide +kernel

end Z3Anomalous
