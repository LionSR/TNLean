/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Separation.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Paths in the unitary group of complex matrices

Every unitary complex square matrix is joined to the identity by a path of
unitary matrices. Consequently any two matrices that are unitary between the
same pair of finite coordinate spaces are joined by a path of such matrices.

The proof rotates a unitary `u` by a scalar `z` on the unit circle chosen so
that `-z` is not an eigenvalue of `u`. The spectrum of `z⁻¹ u` then lies in the
slit plane, so `‖z⁻¹ u - 1‖ < 2` and Mathlib's `Unitary.joined` joins it to the
identity; the scalar `z` is joined to `1` along the circle.

This is the "smoothly connected" step for the gates of the standard form in
arXiv:1703.09188, proof of Theorem `IndexTh` (iv), lines 857--865.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem circle_coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, Complex.star_def, ← Circle.coe_inv_eq_conj,
    ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

private theorem exists_circle_neg_notMem (S : Set ℂ) (hS : S.Finite) :
    ∃ z : Circle, -(z : ℂ) ∉ S := by
  have : Nontrivial Circle := ⟨⟨1, Circle.exp Real.pi, fun h ↦ by
    have := congrArg (fun z : Circle ↦ (z : ℂ)) h
    simp [Circle.coe_exp, Complex.exp_pi_mul_I] at this
    norm_num at this⟩⟩
  have : Infinite Circle := PreconnectedSpace.infinite
  have hfin : {z : Circle | -(z : ℂ) ∈ S}.Finite :=
    (hS.preimage (f := fun z : Circle ↦ -(z : ℂ))
      (fun a _ b _ h ↦ Circle.ext (neg_injective h)))
  obtain ⟨z, hz⟩ := hfin.infinite_compl.nonempty
  exact ⟨z, hz⟩

/-- The scalar unitary `z • 1` attached to a point `z` of the circle. -/
private noncomputable def circleScalar (z : Circle) : unitary (Matrix n n ℂ) :=
  ⟨(z : ℂ) • 1, Unitary.smul_mem_of_mem (circle_coe_mem_unitary z) (one_mem _)⟩

private theorem continuous_circleScalar : Continuous (circleScalar (n := n)) :=
  Continuous.subtype_mk (continuous_subtype_val.smul continuous_const) _

/-- Every unitary complex square matrix is joined to the identity inside the
unitary group. Source: the path-connectedness of finite-dimensional unitary
groups used in arXiv:1703.09188, proof of Theorem `IndexTh` (iv),
lines 857--865. -/
theorem joined_one_unitaryGroup (u : Matrix.unitaryGroup n ℂ) : Joined 1 u := by
  obtain ⟨z, hz⟩ := exists_circle_neg_notMem (spectrum ℂ (u : Matrix n n ℂ))
    (Matrix.finite_spectrum _)
  let w : unitary (Matrix n n ℂ) := circleScalar z⁻¹ * u
  have hw : ‖((w : Matrix n n ℂ) - 1)‖ < 2 := by
    rw [← Unitary.spectrum_subset_slitPlane_iff_norm_lt_two w.2]
    intro s hs
    have hwu : (w : Matrix n n ℂ) = (Units.mk0 ((z : ℂ)⁻¹) (by simp)) • (u : Matrix n n ℂ) := by
      simp [w, circleScalar, Units.smul_def]
    rw [hwu, spectrum.unit_smul_eq_smul] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have htn : ‖t‖ = 1 := by
      simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) u.2 ht
    have hne : t ≠ -(z : ℂ) := fun h ↦ hz (h ▸ ht)
    change (z : ℂ)⁻¹ * t ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    by_contra hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    set μ := (z : ℂ)⁻¹ * t with hμ_def
    have hμn : ‖μ‖ = 1 := by simp [hμ_def, htn]
    have hμ1 : μ = -1 := by
      have habs : ‖μ‖ = |μ.re| := by
        rw [← Complex.re_add_im μ, him]; simp
      rw [hμn] at habs
      apply Complex.ext
      · simp only [Complex.neg_re, Complex.one_re]
        rcases abs_eq (zero_le_one) |>.mp habs.symm with h | h <;> linarith
      · simp [him]
    apply hne
    have : t = (z : ℂ) * μ := by
      rw [hμ_def, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_mul]
    rw [this, hμ1, mul_neg_one]
  have hu : u = circleScalar z * w := by
    apply Subtype.ext
    simp [w, circleScalar, smul_smul]
  have h1 : Joined (1 : unitary (Matrix n n ℂ)) (circleScalar z) := by
    have h0 : circleScalar (n := n) 1 = 1 := Subtype.ext (by simp [circleScalar])
    exact h0 ▸ (PathConnectedSpace.joined (1 : Circle) z).map (continuous_circleScalar (n := n))
  have h2 : Joined (1 : unitary (Matrix n n ℂ)) w := by
    simpa using Unitary.joined 1 w (by simpa using hw)
  rw [hu]
  simpa using h1.mul h2

/-- Two complex matrices that are unitary between the same coordinate spaces
are joined by a path of such matrices. Source: arXiv:1703.09188, proof of
Theorem `IndexTh` (iv), lines 857--865 ("they can be smoothly connected to
each other"). -/
theorem IsUnitaryBetween.joinedIn {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {A B : Matrix m k ℂ}
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween) :
    JoinedIn {X : Matrix m k ℂ | X.IsUnitaryBetween} A B := by
  have hG : B * Aᴴ ∈ Matrix.unitaryGroup m ℂ :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp (hB.mul _ _ hA.conjTranspose)
  obtain ⟨γ⟩ := joined_one_unitaryGroup ⟨B * Aᴴ, hG⟩
  have hf : Continuous fun g : Matrix.unitaryGroup m ℂ ↦ (g : Matrix m m ℂ) * A :=
    continuous_subtype_val.matrix_mul continuous_const
  have h0 : ((1 : Matrix.unitaryGroup m ℂ) : Matrix m m ℂ) * A = A := by simp
  have h1 : B * Aᴴ * A = B := by rw [Matrix.mul_assoc, hA.1, Matrix.mul_one]
  refine ⟨(γ.map hf).cast h0.symm h1.symm, fun t ↦ ?_⟩
  change ((γ t : Matrix.unitaryGroup m ℂ) : Matrix m m ℂ) * A ∈ _
  exact ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (γ t).2).mul _ _ hA

end Matrix
