import TNLean.PEPS.AreaLaw.Scan.BoxEntropySupremum

/-! Actual zero-gap box-supremum inputs. The integer rectangle has size one;
the physical cut is empty. At scale zero there are no admissible rectangles.
The bridge is used only under its stated uniform box-power hypothesis. -/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open TNLean.Lattice TNLean.PEPS.AreaLaw

noncomputable section
namespace BoxSupremumZeroGapRegression

def domain : Finset (ℤ × ℤ) := {(0, 0)}
def zeroHamiltonian := LocalHamiltonian.zero domain 2 1 0 (by norm_num)
def omega : StateSpace domain 2 := EuclideanSpace.single (fun _ ↦ 0) 1

def rectangle : IntRect := ⟨0, 0, 0, 0, by decide, by decide⟩

theorem omega_norm : ‖omega‖ = 1 := by simp [omega]

theorem projector_gap : (zeroHamiltonian.operator - (0 : ℂ) • 1 - (0 : ℂ) •
    (1 - Matrix.vecMulVec (fun x ↦ omega x) (star (fun x ↦ omega x)))).PosSemidef := by
  simpa [zeroHamiltonian, LocalHamiltonian.operator, LocalHamiltonian.zero] using
    (Matrix.PosSemidef.zero :
      (0 : Matrix (Configuration domain 2) (Configuration domain 2) ℂ).PosSemidef)

theorem omega_mem : omega ∈ ManyBody.groundSpace zeroHamiltonian.operator 0 := by
  simp [ManyBody.groundSpace, zeroHamiltonian, LocalHamiltonian.operator, LocalHamiltonian.zero]

theorem safe_empty : IsSafe domain ∅ 0 rectangle := by
  simp [IsSafe]

theorem actual_value_mem :
    regionalEntropy domain 2 omega (rectRegion ∅ rectangle) ∈
      boxEntropyValues 2 1 0 0 0 1 := by
  exact ⟨domain, zeroHamiltonian, 0, omega, ∅, rectangle, omega_norm,
    projector_gap, omega_mem, safe_empty, by decide, rfl⟩

example : regionalEntropy domain 2 omega (rectRegion ∅ rectangle) ≤
    boxEntropy 2 1 0 0 0 1 :=
  regionalEntropy_le_boxEntropy (by decide) zeroHamiltonian omega_norm projector_gap
    omega_mem safe_empty (by decide)

theorem values_at_zero_empty : boxEntropyValues 2 1 0 0 0 0 = ∅ := by
  ext s
  constructor
  · rintro ⟨Λ, h, E₀, Ω, A, Q, hΩ, hgap, hmem, hsafe, hsize, hs⟩
    have hpos := Q.one_le_size
    omega
  · simp

example : boxEntropy 2 1 0 0 0 0 = 0 := by
  simp [boxEntropy, values_at_zero_empty]

-- This is a conditional wrapper call, not a claim of a nonpositive-gap area law.
example (C e : ℝ) (he : 0 < 1 + e)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy 2 1 0 0 0 r ≤ C * (r : ℝ) ^ (1 + e)) :
    regionalEntropy domain 2 omega (rectRegion ∅ rectangle) ≤
      C * (rectangle.size : ℝ) ^ (1 + e) :=
  regionalEntropy_le_of_boxEntropy_power (by decide : 1 ≤ (2 : ℕ)) he hbox
    zeroHamiltonian omega_norm projector_gap omega_mem ∅ rectangle safe_empty

end BoxSupremumZeroGapRegression
