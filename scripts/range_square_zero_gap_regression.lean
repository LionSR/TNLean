import TNLean.PEPS.Approximation.RangeSquareGroundState

/-! Exercise the TN square-to-range conversion at Delta=0 on a one-site q=2
zero Hamiltonian. No uniqueness premise is supplied. -/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open TNLean.PEPS.Approximation

noncomputable section
namespace RangeSquareZeroGapRegression

def zeroSquare : ManyBody.SquareInteraction 1 2 where
  term _ := 0
  mem _ := zero_mem _

def omega : StateSpace 1 2 := EuclideanSpace.single (fun _ ↦ 0) 1

theorem squareGroundState : IsSquareGroundState 2 0 0 1 omega := by
  refine ⟨zeroSquare, ?_, ?_, 0, ?_, ?_, ?_⟩
  · simp [zeroSquare, ManyBody.Interaction.hamiltonian]
  · intro i
    simp [zeroSquare]
  · simp [omega]
  · simpa [zeroSquare, ManyBody.Interaction.hamiltonian] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (ManyBody.SquareLatticeVertex 1 1 → Fin 2)
          (ManyBody.SquareLatticeVertex 1 1 → Fin 2) ℂ).PosSemidef)
  · simp [ManyBody.groundSpace, zeroSquare, ManyBody.Interaction.hamiltonian]

example : IsRangeSquareGroundState 2 1 0 0 1 omega :=
  squareGroundState.isRangeSquareGroundState

end RangeSquareZeroGapRegression
