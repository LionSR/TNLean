/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation

/-!
# Enlarging the bounds on rational MPS representations

The actual virtual spaces and local entries of a rational open-chain representation
remain unchanged when its upper bond bound is enlarged. A common coordinate-height
bound may likewise be enlarged. These operations permit representations with different
individual bounds to be placed under one uniform bound.
-/

namespace TNLean.MPS.AreaLaw

namespace RationalLeftOpenMPSRepresentation

/-- Enlarge the advertised bond bound while preserving the actual virtual spaces,
the local tensors, and the represented vector. -/
def mono_bond {L q k b b' : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (hb : b ≤ b') :
    RationalLeftOpenMPSRepresentation b' v where
  tensor :=
    { bondDim := R.tensor.bondDim
      bondDim_le := fun p ↦ (R.tensor.bondDim_le p).trans
        (max_le_max le_rfl (max_le_max le_rfl hb))
      left_dim := R.tensor.left_dim
      right_dim := R.tensor.right_dim
      tensor := R.tensor.tensor }
  scalar := R.scalar
  internal_bondDim_le p hp hp' :=
    (R.internal_bondDim_le p hp hp').trans (max_le_max le_rfl hb)
  coeff_eq := R.coeff_eq
  scalar_rational := R.scalar_rational
  tensor_rational := R.tensor_rational

end RationalLeftOpenMPSRepresentation

namespace RationalLeftOpenMPSRepresentationOfHeight

/-- Enlarge a common coordinate-height bound without changing the rational data. -/
def mono_height {L q k H H' b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hH : H ≤ H') :
    RationalLeftOpenMPSRepresentationOfHeight H' b v where
  data := R.data
  scalar_height := R.scalar_height.mono hH
  tensor_height p i a c := (R.tensor_height p i a c).mono hH

/-- Enlarge a bond bound without changing the scalar, local entries, or their height. -/
def mono_bond {L q k H b b' : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hb : b ≤ b') :
    RationalLeftOpenMPSRepresentationOfHeight H b' v where
  data := R.data.mono_bond hb
  scalar_height := R.scalar_height
  tensor_height := R.tensor_height

/-- Enlarge the common coordinate height and bond bound simultaneously. -/
def mono {L q k H H' b b' : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v)
    (hH : H ≤ H') (hb : b ≤ b') :
    RationalLeftOpenMPSRepresentationOfHeight H' b' v :=
  (R.mono_bond hb).mono_height hH

end RationalLeftOpenMPSRepresentationOfHeight

end TNLean.MPS.AreaLaw
