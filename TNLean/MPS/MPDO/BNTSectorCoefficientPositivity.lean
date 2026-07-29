/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexPhasePositivity
import TNLean.MPS.MPDO.BNTThreeSiteReducedClosure
import TNLean.MPS.MPDO.GSNNCHSectorRescaling
import TNLean.MPS.MPDO.PhysicalSectorActiveBond

/-!
# Positivity of orthogonally supported BNT coefficients

Global positivity and pairwise orthogonal two-sided physical supports force the
coefficient of every nonzero BNT sector operator to be a nonnegative real
number. A sector operator which vanishes at one fixed length may instead be
given coefficient zero, without changing the decomposition at that length.

This is the compression argument for the BNT sum in CPSV16, Appendix C.2,
equation `sigmaNKj`, lines 1753--1760, used here to repair Proposition
`prop3to4`, lines 1786--1796.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

open PhysicalSectorFactorization

variable {d : ℕ}

/-- Compressing an orthogonally supported physical sector retains the matching
tensor and kills every other tensor in the family.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNKj`, lines
1753--1760. -/
theorem changePhysicalBasis_eq_ite_of_pairwise_orthogonal_twoSided_physicalSupport
    {g : ℕ} {dim : Fin g → ℕ}
    (K : (s : Fin g) → MPOTensor d (dim s))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (s t : Fin g) :
    changePhysicalBasis (P s) (K t) = if s = t then K t else 0 := by
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    exact changePhysicalBasis_eq_self_of_twoSided_physicalSlice
      (P s) (K s) (hP s) (hSupport s)
  · rw [if_neg hst]
    ext i j β α
    change (P s * physicalSlice (K t) β α * (P s)ᴴ) i j = 0
    rw [(hP s).1.eq]
    calc
      (P s * physicalSlice (K t) β α * P s) i j =
          (P s * (P t * physicalSlice (K t) β α) * P s) i j := by
        rw [(hSupport t β α).1]
      _ = 0 := by
        rw [← Matrix.mul_assoc (P s) (P t), hPorth hst, zero_mul, zero_mul]
        rfl

/-- Sitewise compression of an orthogonally supported sector sum isolates its
matching scalar-weighted sector operator.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNKj`, lines
1753--1760. -/
theorem singleKrausMap_sitewise_eq_coefficient_smul_of_orthogonalSupport
    {g N : ℕ} {dim : Fin g → ℕ}
    (K : (s : Fin g) → MPOTensor d (dim s))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (coefficient : Fin g → ℂ) (ρ : ChainOperator d N)
    (hρ : ρ = ∑ s : Fin g, coefficient s • mpo (K s) N)
    (hN : 0 < N) (s : Fin g) :
    singleKrausMap (sitewisePhysicalMatrix (P s) N) ρ =
      coefficient s • mpo (K s) N := by
  classical
  rw [hρ, map_sum]
  simp_rw [map_smul, singleKrausMap_sitewisePhysicalMatrix_mpo,
    changePhysicalBasis_eq_ite_of_pairwise_orthogonal_twoSided_physicalSupport
      K P hP hPorth hSupport s]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Ne.symm hts, mpo_zero_of_pos hN]
  · simp

/-- At one fixed chain length, global positivity turns a complex orthogonal
sector expansion into an equal expansion with nonnegative real coefficients.
The coefficient is set to zero when the corresponding sector operator
vanishes.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop3to4`, lines
1786--1796; the standing positive-MPDO hypothesis is stated at lines
1626--1629. -/
theorem exists_nonnegative_sectorCoefficient_of_orthogonalSupport
    {g N : ℕ} {dim : Fin g → ℕ}
    (K : (s : Fin g) → MPOTensor d (dim s))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (coefficient : Fin g → ℂ) (ρ : ChainOperator d N)
    (hρpos : ρ.PosSemidef)
    (hSectorPos : ∀ s, (mpo (K s) N).PosSemidef)
    (hρ : ρ = ∑ s : Fin g, coefficient s • mpo (K s) N)
    (hN : 0 < N) :
    ∃ coefficientReal : Fin g → ℝ,
      (∀ s, 0 ≤ coefficientReal s) ∧
      (∀ s, (coefficientReal s : ℂ) • mpo (K s) N =
        coefficient s • mpo (K s) N) := by
  classical
  have hTermPos (s : Fin g) :
      (coefficient s • mpo (K s) N).PosSemidef := by
    rw [← singleKrausMap_sitewise_eq_coefficient_smul_of_orthogonalSupport
      K P hP hPorth hSupport coefficient ρ hρ hN s]
    exact hρpos.mul_mul_conjTranspose_same
      (B := sitewisePhysicalMatrix (P s) N)
  have hExists (s : Fin g) : ∃ r : ℝ, 0 ≤ r ∧
      (r : ℂ) • mpo (K s) N = coefficient s • mpo (K s) N := by
    by_cases hSectorZero : mpo (K s) N = 0
    · exact ⟨0, le_rfl, by simp [hSectorZero]⟩
    by_cases hCoefficientZero : coefficient s = 0
    · exact ⟨0, le_rfl, by simp [hCoefficientZero]⟩
    obtain ⟨r, hr, hcoeff⟩ :=
      Matrix.exists_pos_real_smul_eq_of_smul_posSemidef
        hSectorZero (hTermPos s) (by simpa using hSectorPos s)
        hCoefficientZero one_ne_zero
    refine ⟨r, hr.le, ?_⟩
    rw [hcoeff]
    simp only [mul_one]
  choose coefficientReal hCoefficientReal hTerm using hExists
  exact ⟨coefficientReal, hCoefficientReal, hTerm⟩

/-- If every sector operator is nonzero, the original complex coefficients
are themselves nonnegative real numbers.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop3to4`, lines
1786--1796; the standing positive-MPDO hypothesis is stated at lines
1626--1629. -/
theorem exists_nonnegative_real_eq_sectorCoefficient_of_orthogonalSupport
    {g N : ℕ} {dim : Fin g → ℕ}
    (K : (s : Fin g) → MPOTensor d (dim s))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (coefficient : Fin g → ℂ) (ρ : ChainOperator d N)
    (hρpos : ρ.PosSemidef)
    (hSectorPos : ∀ s, (mpo (K s) N).PosSemidef)
    (hSectorNe : ∀ s, mpo (K s) N ≠ 0)
    (hρ : ρ = ∑ s : Fin g, coefficient s • mpo (K s) N)
    (hN : 0 < N) :
    ∃ coefficientReal : Fin g → ℝ,
      (∀ s, 0 ≤ coefficientReal s) ∧
      (∀ s, (coefficientReal s : ℂ) = coefficient s) := by
  obtain ⟨coefficientReal, hnonneg, hterm⟩ :=
    exists_nonnegative_sectorCoefficient_of_orthogonalSupport
      K P hP hPorth hSupport coefficient ρ hρpos hSectorPos hρ hN
  refine ⟨coefficientReal, hnonneg, fun s ↦ ?_⟩
  have hzero : ((coefficientReal s : ℂ) - coefficient s) • mpo (K s) N = 0 := by
    rw [sub_smul, hterm s, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (hSectorNe s))

end MPOTensor
