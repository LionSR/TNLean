/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarInformation
import TNLean.PEPS.AreaLaw.AmplificationCutClearance

/-!
# Degenerate zero-gap inputs to the collar and amplification bounds

A zero Hamiltonian on one two-level site has a two-dimensional ground space.
The four conditional bounds can be specialized to its normalized zero configuration
without a ground-space uniqueness premise. No unconditional zero-gap area law is asserted.
-/

open TNLean.Lattice TNLean.PEPS.AreaLaw
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace GenericGapBoundaryRegression

def domain : Finset (ℤ × ℤ) := {(0, 0)}

def zeroHamiltonian : LocalHamiltonian domain 2 1 0 where
  term _ := 0
  supported _ := zero_mem _
  hermitian _ := Matrix.isHermitian_zero
  norm_le _ := by simp

def omega : StateSpace domain 2 := EuclideanSpace.single (fun _ ↦ 0) 1

theorem norm_omega : ‖omega‖ = 1 := by simp [omega]

theorem omega_mem : omega ∈ ManyBody.groundSpace zeroHamiltonian.operator 0 := by
  simp [ManyBody.groundSpace, zeroHamiltonian, LocalHamiltonian.operator]

theorem zero_projector_bound :
    (zeroHamiltonian.operator - (0 : ℂ) • 1 - (0 : ℂ) •
      (1 - Matrix.vecMulVec (fun x ↦ omega x) (star (fun x ↦ omega x)))).PosSemidef := by
  simpa [zeroHamiltonian, LocalHamiltonian.operator] using
    (Matrix.PosSemidef.zero : (0 : Matrix (Configuration domain 2) _ ℂ).PosSemidef)

theorem groundSpace_not_span :
    ManyBody.groundSpace zeroHamiltonian.operator 0 ≠ Submodule.span ℂ {omega} := by
  classical
  intro h
  have hv : EuclideanSpace.single (fun _ : Site domain ↦ (1 : Fin 2)) (1 : ℂ) ∈
      ManyBody.groundSpace zeroHamiltonian.operator 0 := by
    simp [ManyBody.groundSpace, zeroHamiltonian, LocalHamiltonian.operator]
  rw [h, Submodule.mem_span_singleton] at hv
  obtain ⟨c, hc⟩ := hv
  have hne : (fun _ : Site domain ↦ (0 : Fin 2)) ≠ fun _ ↦ 1 := by
    intro he
    have := congrFun he ⟨(0, 0), by simp [domain]⟩
    norm_num at this
  have hh := congrArg (fun v : StateSpace domain 2 ↦ v (fun _ ↦ 1)) hc
  simp [omega, Ne.symm hne] at hh

example {D Ctpl C : ℝ} {N n s : ℕ}
    (hb : SublinearCollarBoundAt 2 1 0 0 D Ctpl C N) (hn : N ≤ n)
    (A : Finset (Site domain)) (T : Geometry.Template Ctpl n s)
    (hsep : T.IsSeparated D (Geometry.boundaryEndpoints domain A))
    (hL : ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s) :
    FiniteProduct.mutualInformation (fun _ : Site domain ↦ Fin 2) omega
      (A.filter fun x ↦ x.val ∈ T.points)
      (A.filter fun x ↦ x.val ∈ ambientDilation T.points
        ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
      C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) :=
  (hb n s hn domain zeroHamiltonian 0 omega norm_omega zero_projector_bound omega_mem
    A T hsep hL).1

example {D Ctpl : ℝ} (hb : SublinearCollarBound 2 1 0 0 D Ctpl) :
    ∃ C N, SublinearCollarBoundAt 2 1 0 0 D Ctpl C N :=
  sublinearCollarBound_iff_exists_sublinearCollarBoundAt.mp hb

example {C : ℝ} {N n : ℕ} (hb : AmplificationBoundAt 2 1 0 0 1 1 C N)
    (hn : 2 ≤ n) (hN : N ≤ n) :
    ∃ r : ℕ, (r : ℝ) ≤ C * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) := by
  obtain ⟨r, hr, -⟩ := hb n hn hN domain zeroHamiltonian 0 omega
    norm_omega zero_projector_bound omega_mem ∅ ∅
    (by simp) (by simp) (by simp) (by simp)
    (by
      simp only [Finset.filter_empty, FiniteProduct.mutualInformation, Finset.empty_union,
        FiniteProduct.entropy_empty _ _ norm_omega, zero_add, sub_self, one_mul]
      positivity)
  exact ⟨r, hr⟩

example (hb : AmplificationBound 2 1 0 0) :
    ∃ C N, AmplificationBoundAt 2 1 0 0 1 1 C N :=
  (amplificationBound_iff_forall_exists_amplificationBoundAt.mp hb) 1 (by norm_num) 1 le_rfl

end GenericGapBoundaryRegression
