/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.Algebra.SpinCover

/-!
# On-site rotational symmetry of the AKLT state

This module formalizes the on-site rotational symmetry of the AKLT matrix
product state in its Cartesian (Pauli) form `A^i = σ^i`, `i ∈ {x, y, z}`
(arXiv:2011.12127, around line 1159).

The physical site carries the spin-`1` (defining) representation of the
rotations, while the virtual/bond index transforms in the projective
spin-`½` representation: for every `U ∈ SU(2)`, conjugation of the Pauli
vector by `U` is a rotation `R(U)` of the three physical components, and the
AKLT tensor twisted by `R(U)` is gauge equivalent to the original through the
gauge `U⁻¹`.  This is the projective-representation content of the
symmetry-protected topological phase.  The symmetry is first stated over the
cover `SU(2)`; the `SO(3)` version then follows from the surjectivity of the
cover, both proved here.

The spin double cover `SU(2) → SO(3)` and the supporting Pauli-conjugation
machinery (`SpinCover.pauliConjAd`, `SpinCover.spinHalfCover`,
`SpinCover.spinHalfCover_surjective_onto_SO3`, `SpinCover.so3_euler_decomp`)
are AKLT-independent and live in `TNLean.Algebra.SpinCover`; this module only
adds the AKLT-facing consequences.

## Main definitions

* `MPSTensor.akltCartesian` : the AKLT tensor `A^i = σ^i`
* `MPSTensor.so3DefiningRep` : the spin-`1` defining representation of `SO(3)`

## Main results

* `MPSTensor.aklt_isOnSiteSymmetric_spinHalfCover` : the AKLT tensor is on-site
  symmetric under the `SU(2)`-parametrized rotations
* `MPSTensor.aklt_isOnSiteSymmetric_SO3` : the AKLT tensor is on-site symmetric
  under the spin-`1` representation of `SO(3)`

## References

* RMP review (arXiv:2011.12127) line 1159 (`A^i = σ^i`, on-site `SO(3)`)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The AKLT tensor and its on-site symmetry -/

/-- The AKLT tensor in Cartesian (Pauli) form `A^i = σ^i`, `i ∈ {x, y, z}`
(arXiv:2011.12127, around line 1159). -/
def akltCartesian : MPSTensor 3 2 := SpinCover.pauli

@[simp] lemma akltCartesian_apply (i : Fin 3) : akltCartesian i = SpinCover.pauli i := rfl

/-- For every `U ∈ GL (Fin 2) ℂ` the AKLT tensor twisted on the physical index by
the rotation `R(U)` is gauge equivalent to the original through the virtual gauge
`U⁻¹`: this is the projective spin-`½` representation acting on the bond index
(arXiv:2011.12127, around line 1159). -/
theorem aklt_gaugeEquiv_spinHalfCover (U : GL (Fin 2) ℂ) :
    GaugeEquiv akltCartesian (twistedTensor akltCartesian SpinCover.spinHalfCover U) := by
  refine ⟨U⁻¹, fun i => ?_⟩
  -- The gauge `X = U⁻¹` sends `B i = ↑U⁻¹ * pauli i * ↑(U⁻¹)⁻¹`.
  simp only [twistedTensor, SpinCover.spinHalfCover_apply, akltCartesian_apply]
  rw [SpinCover.pauli_conj_eq U⁻¹ i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SpinCover.pauliConjAd_swap U i j]

/-- The AKLT tensor is on-site symmetric under the `SU(2)`-cover-parametrized
rotations `R(U)`.  The physical site carries the spin-`1` representation `R(U)`
while the virtual bond index transforms in the projective spin-`½`
representation, with the gauge for `U` given by `U⁻¹`.  This cover form is
strictly stronger bookkeeping than the `SO(3)` statement
`aklt_isOnSiteSymmetric_SO3`, which follows from it by the surjectivity of the
cover `SpinCover.spinHalfCover_surjective_onto_SO3` (arXiv:2011.12127,
around line 1159). -/
theorem aklt_isOnSiteSymmetric_spinHalfCover :
    IsOnSiteSymmetric akltCartesian SpinCover.spinHalfCover :=
  fun U => (aklt_gaugeEquiv_spinHalfCover U).sameMPV

/-! ### On-site `SO(3)` symmetry of the AKLT tensor -/

/-- The spin-`1` (defining) representation of the rotation group on the physical
index, embedded into the complex matrices. -/
noncomputable def so3DefiningRep :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun M := (M : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal
  map_one' := by simp
  map_mul' M N := by
    have hof : (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom := rfl
    simp only [Submonoid.coe_mul, hof, Matrix.map_mul]

@[simp] lemma so3DefiningRep_apply (M : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    so3DefiningRep M = (M : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal := rfl

/-- The AKLT tensor is on-site symmetric under the full rotation group `SO(3)`
acting through its spin-`1` representation on the physical index.  Surjectivity of
the spin-`½` cover upgrades the `SU(2)`-cover symmetry to a literal `SO(3)`
symmetry: every rotation is the conjugation action of some `SU(2)` matrix, whose
virtual gauge then witnesses the same matrix product vector
(arXiv:2011.12127, around line 1159). -/
theorem aklt_isOnSiteSymmetric_SO3 : IsOnSiteSymmetric akltCartesian so3DefiningRep := by
  intro M
  obtain ⟨U, hU, hRU⟩ :=
    SpinCover.spinHalfCover_surjective_onto_SO3 (M : Matrix (Fin 3) (Fin 3) ℝ) M.2
  have key : twistedTensor akltCartesian so3DefiningRep M
      = twistedTensor akltCartesian SpinCover.spinHalfCover (SpinCover.su2ToGL U hU) := by
    unfold twistedTensor
    simp only [so3DefiningRep_apply, SpinCover.spinHalfCover_apply, ← hRU]
  rw [key]
  exact (aklt_gaugeEquiv_spinHalfCover (SpinCover.su2ToGL U hU)).sameMPV

end MPSTensor

end
