import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix ComplexOrder MatrixOrder

variable (D : ℕ)

-- Check NonUnitalNormedRing via @
#check @Matrix.instCStarRing ℂ (Fin D) _ _ _

-- Maybe the NonUnitalNormedRing comes from a different import/approach
-- Try using the L2OpRing structure directly
set_option trace.Meta.synthInstance true in
noncomputable example : NonUnitalNormedRing (Matrix (Fin D) (Fin D) ℂ) := inferInstance

