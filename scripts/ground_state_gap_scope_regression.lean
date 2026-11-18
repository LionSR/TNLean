import TNLean.MPS.AreaLaw.OverlapEnergy
import TNLean.MPS.AreaLaw.BoundaryGap
import TNLean.PEPS.Approximation.Basic

/-! Regression for the unrestricted projector-gap domain: a degenerate zero
Hamiltonian satisfies the algebraic inputs, and generalized TNLean helpers accept it. -/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace GapScopeRegression
def omega : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

theorem zeroGap_projector_condition :
    ‖omega‖ = 1 ∧
    Matrix.toEuclideanLin (0 : Matrix (Fin 2) (Fin 2) ℂ) omega = (0 : ℂ) • omega ∧
    ((0 : Matrix (Fin 2) (Fin 2) ℂ) - (0 : ℂ) • 1 -
      (0 : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp omega) (star (WithLp.ofLp omega)))).PosSemidef := by
  simpa [omega] using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef)

theorem zeroGap_eigenspace_not_singleton_span :
    ManyBody.groundSpace (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 ≠
      Submodule.span ℂ {omega} := by
  intro h
  change Module.End.eigenspace (Matrix.toEuclideanLin (0 : Matrix (Fin 2) (Fin 2) ℂ)) 0 =
    Submodule.span ℂ {omega} at h
  have hv : EuclideanSpace.single (1 : Fin 2) (1 : ℂ) ∈
      Module.End.eigenspace (Matrix.toEuclideanLin (0 : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
    simp
  rw [h, Submodule.mem_span_singleton] at hv
  obtain ⟨c, hc⟩ := hv
  have hh := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hc
  simp [omega] at hh

theorem zeroGap_isGapped :
    ManyBody.IsGapped (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  constructor
  · intro h
    have hv : omega ∈ ManyBody.groundSpace (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 := by
      simp [ManyBody.groundSpace]
    rw [h, Submodule.mem_bot] at hv
    have hn := zeroGap_projector_condition.1
    rw [hv, norm_zero] at hn
    exact zero_ne_one hn
  · intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have he := hv.apply_eq_smul
    have he' : μ • v = 0 := by simpa using he.symm
    exact Or.inl (by simpa using (smul_eq_zero.mp he').resolve_right hv.2)

noncomputable def zeroChain := TNLean.MPS.AreaLaw.ChainHamiltonian.zero 1 2 1 1 (by norm_num)
noncomputable def chainOmega : EuclideanSpace ℂ (Fin 1 → Fin 2) :=
  EuclideanSpace.single (fun _ ↦ 0) 1

example :
    (⟪chainOmega, Matrix.toEuclideanLin zeroChain.operator chainOmega⟫_ℂ).re - 0 ≤
      8 * (1 : ℝ) * 0 := by
  simpa using zeroChain.re_inner_sub_le_of_overlap_of_range_one
    (Ω := chainOmega) (v := chainOmega) (E₀ := 0) (δ := 0)
    (by simp [chainOmega])
    (by simp [ManyBody.groundSpace, zeroChain,
      TNLean.MPS.AreaLaw.ChainHamiltonian.operator, TNLean.MPS.AreaLaw.ChainHamiltonian.zero])
    (by simp [chainOmega]) (by simp [chainOmega])

example : (0 : ℝ) ≤ 4 * 1 := by
  apply zeroChain.gap_le_four_mul_of_range_one (Ω := chainOmega) (E₀ := 0)
      (by decide) (by decide)
  · simp [chainOmega]
  · simpa [zeroChain, TNLean.MPS.AreaLaw.ChainHamiltonian.operator,
      TNLean.MPS.AreaLaw.ChainHamiltonian.zero] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ).PosSemidef)
  · simp [ManyBody.groundSpace, zeroChain,
      TNLean.MPS.AreaLaw.ChainHamiltonian.operator, TNLean.MPS.AreaLaw.ChainHamiltonian.zero]

noncomputable def zeroSquare : ManyBody.SquareInteraction 1 2 where
  term _ := 0
  mem _ := zero_mem _

noncomputable def squareOmega : TNLean.PEPS.Approximation.StateSpace 1 2 :=
  EuclideanSpace.single (fun _ ↦ 0) 1

example : TNLean.PEPS.Approximation.IsSquareGroundState 2 0 0 1 squareOmega := by
  refine ⟨zeroSquare, ?_, ?_, 0, ?_, ?_, ?_⟩
  · simp [zeroSquare, ManyBody.Interaction.hamiltonian]
  · intro i
    simp [zeroSquare]
  · simp [squareOmega]
  · simpa [zeroSquare, ManyBody.Interaction.hamiltonian] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (ManyBody.SquareLatticeVertex 1 1 → Fin 2)
          (ManyBody.SquareLatticeVertex 1 1 → Fin 2) ℂ).PosSemidef)
  · simp [ManyBody.groundSpace, zeroSquare, ManyBody.Interaction.hamiltonian]

end GapScopeRegression
