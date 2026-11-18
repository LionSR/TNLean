import TNLean.PEPS.AreaLaw.RectangularHamiltonian
import TNLean.PEPS.Approximation.PinnedZeroFloorOptimizer
import TNLean.MPS.AreaLaw.Hastings.ThreeWaySplitting

/-! Actual TN wrapper calls at zero gap. The optimizer conclusions remain weighted
by Δ; this regression does not assert unweighted fidelity or ground-space uniqueness.
Range-square and box-supremum coverage are not provided by this file yet. -/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open TNLean.PEPS.AreaLaw TNLean.PEPS.Approximation

noncomputable section
namespace ZeroGapTNWrappersRegression

def zeroRectangle (w h : ℕ) : ManyBody.RectangleInteraction w h 2 where
  term _ := 0
  mem _ := zero_mem _

def rectangleOmega (w h : ℕ) : RectangleStateSpace w h 2 :=
  EuclideanSpace.single (fun _ ↦ 0) 1

-- Arbitrary dimensions include the degenerate 1×2 system and empty width/height.
example (w h : ℕ) :=
  (zeroRectangle w h).projectorGap_toAreaLawHamiltonian (J := 0) (E₀ := 0) (Δ := 0)
    (Ω := rectangleOmega w h)
    (by intro i; simp [zeroRectangle])
    (by simp [zeroRectangle, ManyBody.Interaction.hamiltonian])
    (by simp [rectangleOmega])
    (by simpa [zeroRectangle, ManyBody.Interaction.hamiltonian] using
      (Matrix.PosSemidef.zero : (0 : Matrix (ManyBody.SquareLatticeVertex w h → Fin 2)
        (ManyBody.SquareLatticeVertex w h → Fin 2) ℂ).PosSemidef))
    (by simp [ManyBody.groundSpace, zeroRectangle, ManyBody.Interaction.hamiltonian])


def zeroChain := TNLean.MPS.AreaLaw.ChainHamiltonian.zero 1 2 1 1 (by norm_num)
def chainOmega : EuclideanSpace ℂ (Fin 1 → Fin 2) :=
  EuclideanSpace.single (fun _ ↦ 0) 1

-- All natural j,m include zero, the endpoint, and cuts beyond the single site.
example (j m : ℕ) :=
  zeroChain.isGapped_groundCentered_parts_sum (E₀ := 0) (Δ := 0) (Ω := chainOmega)
    (by simp [chainOmega])
    (by simpa [zeroChain, TNLean.MPS.AreaLaw.ChainHamiltonian.operator,
      TNLean.MPS.AreaLaw.ChainHamiltonian.zero] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ).PosSemidef))
    (by simp [ManyBody.groundSpace, zeroChain, TNLean.MPS.AreaLaw.ChainHamiltonian.operator,
      TNLean.MPS.AreaLaw.ChainHamiltonian.zero]) j m


-- Empty nested regions with weight one for every m, including m=0 and m=1.
example (m : ℕ) :=
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

example (m : ℕ) :=
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
