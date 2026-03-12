/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Topology.Separation.Hausdorff

namespace Filter

/-- If `f` tends to `a`, then it cannot also tend to a different limit `b`. -/
theorem Tendsto.ne_nhds {α X : Type*} [TopologicalSpace X] [T2Space X]
    {f : α → X} {l : Filter α} [NeBot l] {a b : X}
    (ha : Tendsto f l (nhds a)) (hab : a ≠ b) :
    ¬ Tendsto f l (nhds b) := by
  intro hb
  exact hab (tendsto_nhds_unique ha hb)

end Filter
