import TNLean.PEPS.AreaLaw.RectangularHamiltonian
import TNLean.PEPS.Approximation.PinnedZeroFloorOptimizer
import TNLean.MPS.AreaLaw.Hastings.ThreeWaySplitting

/-! Actual TN wrapper calls at zero gap. The optimizer conclusions remain weighted
by Δ; this regression does not assert unweighted fidelity or ground-space uniqueness.
Range-square and box-supremum coverage are not provided by this file yet. -/

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open TNLean.PEPS.AreaLaw TNLean.PEPS.Approximation

noncomputable section
namespace ZeroGapTNWrappersRegression

open Pinned.NestedFilter
open TNLean.MPS.AreaLaw.Hastings

def zeroRectangle (w h : ℕ) : ManyBody.RectangleInteraction w h 2 where
  term _ := 0
  mem _ := zero_mem _

def rectangleOmega (w h : ℕ) : RectangleStateSpace w h 2 :=
  EuclideanSpace.single (fun _ ↦ 0) 1

theorem rectangleTermBound (w h : ℕ) : ∀ i, ‖(zeroRectangle w h).term i‖ ≤ (0 : ℝ) := by
  intro i
  simp [zeroRectangle]

-- A nonempty one-site q=2 system really has more than one ground-state direction.
theorem nonSingletonGroundSpace :
    ManyBody.groundSpace (zeroRectangle 1 1).hamiltonian 0 ≠
      Submodule.span ℂ {rectangleOmega 1 1} := by
  have hconfigs : (fun _ : ManyBody.SquareLatticeVertex 1 1 ↦ (1 : Fin 2)) ≠
      (fun _ ↦ (0 : Fin 2)) := by
    intro h
    have := congrFun h (0, 0)
    norm_num at this
  intro hspan
  have hv : EuclideanSpace.single (fun _ : ManyBody.SquareLatticeVertex 1 1 ↦ (1 : Fin 2))
      (1 : ℂ) ∈ ManyBody.groundSpace (zeroRectangle 1 1).hamiltonian 0 := by
    simp [ManyBody.groundSpace, zeroRectangle, ManyBody.Interaction.hamiltonian]
  rw [hspan, Submodule.mem_span_singleton] at hv
  obtain ⟨c, hc⟩ := hv
  have heval := congrArg (fun v : RectangleStateSpace 1 1 2 ↦ v (fun _ ↦ 1)) hc
  simp [rectangleOmega, hconfigs] at heval

-- Arbitrary dimensions include the degenerate 1×2 system and empty width/height.
example (w h : ℕ) :
    ‖rectangleAreaLawState (rectangleOmega w h)‖ = 1 ∧
    (zeroRectangle w h).toAreaLawHamiltonian.hamiltonian.PosSemidef ∧
    rectangleAreaLawState (rectangleOmega w h) ∈ ManyBody.groundSpace
      (zeroRectangle w h).toAreaLawHamiltonian.hamiltonian 0 := by
  simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
    (zeroRectangle w h).projectorGap_toAreaLawHamiltonian (E₀ := 0) (Δ := 0)
      (Ω := rectangleOmega w h)
      (by simp [zeroRectangle, ManyBody.Interaction.hamiltonian])
      (by simp [rectangleOmega])
      (by simpa [zeroRectangle, ManyBody.Interaction.hamiltonian] using
        (Matrix.PosSemidef.zero : (0 : Matrix (ManyBody.SquareLatticeVertex w h → Fin 2)
          (ManyBody.SquareLatticeVertex w h → Fin 2) ℂ).PosSemidef))
      (by simp [ManyBody.groundSpace, zeroRectangle, ManyBody.Interaction.hamiltonian])


def zeroChain : ManyBody.ChainInteraction 1 2 1 where
  term _ := 0
  mem _ := zero_mem _
def chainOmega : EuclideanSpace ℂ (Fin 1 → Fin 2) :=
  EuclideanSpace.single (fun _ ↦ 0) 1

-- All natural j,m include zero, the endpoint, and cuts beyond the single site.
example (j m : ℕ) :
    ‖chainOmega‖ = 1 ∧
    (groundCentered chainOmega (zeroChain.leftPart j m) +
      groundCentered chainOmega (zeroChain.bufferPart j m) +
      groundCentered chainOmega (zeroChain.rightPart j m)).PosSemidef ∧
    chainOmega ∈ ManyBody.groundSpace
      (groundCentered chainOmega (zeroChain.leftPart j m) +
        groundCentered chainOmega (zeroChain.bufferPart j m) +
        groundCentered chainOmega (zeroChain.rightPart j m)) 0 := by
  simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
    zeroChain.isGapped_groundCentered_parts_sum (E₀ := 0) (Δ := 0) (Ω := chainOmega)
      (by simp [chainOmega])
      (by simpa [zeroChain, ManyBody.Interaction.hamiltonian] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ).PosSemidef))
      (by simp [ManyBody.groundSpace, zeroChain, ManyBody.Interaction.hamiltonian]) j m


-- Empty nested regions with weight one for every m, including m=0 and m=1.
example (m : ℕ) :
    ∃ F : FilterFamily 2 m (fun _ ↦ ∅),
      IsMaximizer (rectangleOmega 1 1) (fun _ ↦ 1) F ∧
      0 < ‖output F (rectangleOmega 1 1)‖ ∧
      ‖normalizedOutput F (rectangleOmega 1 1)‖ = 1 ∧
      |(⟪normalizedOutput F (rectangleOmega 1 1),
        toEuclideanLin (zeroRectangle 1 1).hamiltonian
          (normalizedOutput F (rectangleOmega 1 1))⟫_ℂ).re| ≤ 0 ∧
      (0 : ℝ) * (1 - ‖⟪rectangleOmega 1 1,
        normalizedOutput F (rectangleOmega 1 1)⟫_ℂ‖ ^ 2) ≤ 0 := by
  simpa only [mul_zero, zero_mul, sub_zero] using
    ManyBody.SquareInteraction.exists_pinned_maximizer_energy_fidelity (zeroRectangle 1 1)
      (m := m) (J := 0) (E₀ := 0) (Δ := 0) (Ω := rectangleOmega 1 1)
      (by simp [zeroRectangle, ManyBody.Interaction.hamiltonian])
      (by intro i; simp [zeroRectangle])
      (by simp [rectangleOmega])
      (by simpa [zeroRectangle, ManyBody.Interaction.hamiltonian] using
        (Matrix.PosSemidef.zero : (0 : Matrix (ManyBody.SquareLatticeVertex 1 1 → Fin 2)
          (ManyBody.SquareLatticeVertex 1 1 → Fin 2) ℂ).PosSemidef))
      (by simp [ManyBody.groundSpace, zeroRectangle, ManyBody.Interaction.hamiltonian])
      (fun _ ↦ ∅) (by intro i j hij; exact Finset.Subset.refl _)
      (by intro e i j hi; simp [Pinned.NestedFilter.Energy.Crosses] at hi)
      (fun _ ↦ 1) (by intro j; norm_num) (by intro j; norm_num)


local instance : LinearOrder (TNLean.Lattice.Site (rectangularDomain 1 1)) :=
  LinearOrder.lift' (rectangleSiteEquiv 1 1).symm (rectangleSiteEquiv 1 1).symm.injective

example (m : ℕ) :
    ∃ K : (j : Fin m) → Matrix
        (Entropy.RegionConfig (fun _ : TNLean.Lattice.Site (rectangularDomain 1 1) ↦ 2) ∅)
        (Entropy.RegionConfig (fun _ : TNLean.Lattice.Site (rectangularDomain 1 1) ↦ 2) ∅) ℂ,
      (∀ j : Fin m, Entropy.IsFeasibleFilter 0 1 (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix
          (Entropy.RegionConfig (fun _ : TNLean.Lattice.Site (rectangularDomain 1 1) ↦ 2) ∅)
          (Entropy.RegionConfig (fun _ : TNLean.Lattice.Site (rectangularDomain 1 1) ↦ 2) ∅) ℂ,
        (∀ j : Fin m, Entropy.IsFeasibleFilter 0 1 (K' j)) →
        ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList (fun _ ↦ ∅) K' fun _ ↦ True))
            (rectangleAreaLawState (rectangleOmega 1 1))‖ ≤
          ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList (fun _ ↦ ∅) K fun _ ↦ True))
            (rectangleAreaLawState (rectangleOmega 1 1))‖) ∧
      let ψ := toEuclideanLin (Entropy.liftProd (Entropy.chainList (fun _ ↦ ∅) K fun _ ↦ True))
        (rectangleAreaLawState (rectangleOmega 1 1))
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin
          (zeroRectangle 1 1).toAreaLawHamiltonian.hamiltonian φ⟫_ℂ).re|
          ≤ 0 ∧
        (0 : ℝ) * (1 - ‖⟪rectangleAreaLawState (rectangleOmega 1 1), φ⟫_ℂ‖ ^ 2) ≤ 0 := by
  simpa only [mul_zero, zero_mul, sub_zero] using
    ManyBody.SquareInteraction.exists_zero_floor_maximizer_energy_fidelity (zeroRectangle 1 1)
      (m := m) (J := 0) (E₀ := 0) (Δ := 0) (Ω := rectangleOmega 1 1)
      (by simp [zeroRectangle, ManyBody.Interaction.hamiltonian])
      (by intro i; simp [zeroRectangle])
      (by simp [rectangleOmega])
      (by simpa [zeroRectangle, ManyBody.Interaction.hamiltonian] using
        (Matrix.PosSemidef.zero : (0 : Matrix (ManyBody.SquareLatticeVertex 1 1 → Fin 2)
          (ManyBody.SquareLatticeVertex 1 1 → Fin 2) ℂ).PosSemidef))
      (by simp [ManyBody.groundSpace, zeroRectangle, ManyBody.Interaction.hamiltonian])
      (fun _ ↦ ∅) (by intro i j hij; exact Finset.Subset.refl _)
      (by intro e i j hi; simp at hi)
      (fun _ ↦ 1) (by intro j; norm_num) (by intro j; norm_num)


end ZeroGapTNWrappersRegression
