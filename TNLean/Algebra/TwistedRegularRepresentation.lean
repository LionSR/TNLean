/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Algebra.CircleCohomology

/-!
# Cocycle-twisted regular representations

This file formalizes the left and right regular actions in
arXiv:2502.20257, lines 412--418, and the onsite specialization at lines
3758--3766. For a scalar cocycle `ω`, we use its canonical circle-valued
representative `ω.circlePhase` and the paper's inverse conventions

`Lᵠ_g |h⟩ = ϕ(g,h)⁻¹ |gh⟩`,

`Rᵠ_g |h⟩ = ϕ(h,g⁻¹)⁻¹ |hg⁻¹⟩`.

The extra identity used to rewrite the onsite Gauss coefficient assumes
`ϕ(g⁻¹,g) = 1` explicitly.  It is not inferred from cocyclicity.
-/

noncomputable section

namespace TNLean.Algebra

variable {G : Type*} [Group G]

namespace ScalarCocycle

/-- The complex coefficient of the canonical circle-valued representative of
`ω`. -/
abbrev phase (ω : ScalarCocycle G) (g h : G) : ℂ :=
  (ω.circlePhase g h : ℂ)

/-- The circle phase of a scalar cocycle satisfies the complex-valued cocycle
equation. -/
theorem phase_isCocycle {ω : ScalarCocycle G} (hω : ω.IsCocycle) (g h k : G) :
    ω.phase g h * ω.phase (g * h) k =
      ω.phase g (h * k) * ω.phase h k := by
  have hc := ω.circlePhase_isMulCocycle₂ hω g h k
  change ω.circlePhase (g * h) k * ω.circlePhase g h =
    ω.circlePhase h k * ω.circlePhase g (h * k) at hc
  have hcℂ := congrArg (fun z : Circle ↦ z.1) hc
  change (ω.circlePhase (g * h) k : ℂ) * (ω.circlePhase g h : ℂ) =
    (ω.circlePhase h k : ℂ) * (ω.circlePhase g (h * k) : ℂ) at hcℂ
  simpa only [mul_comm] using hcℂ

omit [Group G] in
/-- Every coefficient of the canonical circle-valued representative has norm
one. -/
lemma norm_phase (ω : ScalarCocycle G) (g h : G) : ‖ω.phase g h‖ = 1 :=
  Circle.norm_coe _

attribute [simp] norm_phase

omit [Group G] in
/-- Every coefficient of the canonical circle-valued representative is
nonzero. -/
lemma phase_ne_zero (ω : ScalarCocycle G) (g h : G) : ω.phase g h ≠ 0 := by
  exact norm_ne_zero_iff.mp (by simp)

attribute [simp] phase_ne_zero

/-- The cocycle-twisted left regular matrix

`Lᵠ_g = ∑_h ϕ(g,h)⁻¹ |gh⟩⟨h|`

from arXiv:2502.20257, lines 412--415. -/
def twistedLeftRegular (ω : ScalarCocycle G) (g : G) : Matrix G G ℂ := by
  classical
  exact fun i h ↦ if i = g * h then (ω.phase g h)⁻¹ else 0

/-- The cocycle-twisted right regular matrix

`Rᵠ_g = ∑_h ϕ(h,g⁻¹)⁻¹ |hg⁻¹⟩⟨h|`

from arXiv:2502.20257, lines 416--418. -/
def twistedRightRegular (ω : ScalarCocycle G) (g : G) : Matrix G G ℂ := by
  classical
  exact fun i h ↦ if i = h * g⁻¹ then (ω.phase h g⁻¹)⁻¹ else 0

@[simp]
theorem twistedLeftRegular_apply_of_eq (ω : ScalarCocycle G) (g i h : G)
    (hi : i = g * h) :
    twistedLeftRegular ω g i h = (ω.phase g h)⁻¹ := by
  classical
  simp [twistedLeftRegular, hi]

@[simp]
theorem twistedLeftRegular_apply_of_ne (ω : ScalarCocycle G) (g i h : G)
    (hi : i ≠ g * h) : twistedLeftRegular ω g i h = 0 := by
  classical
  simp [twistedLeftRegular, hi]

@[simp]
theorem twistedRightRegular_apply_of_eq (ω : ScalarCocycle G) (g i h : G)
    (hi : i = h * g⁻¹) :
    twistedRightRegular ω g i h = (ω.phase h g⁻¹)⁻¹ := by
  classical
  simp [twistedRightRegular, hi]

@[simp]
theorem twistedRightRegular_apply_of_ne (ω : ScalarCocycle G) (g i h : G)
    (hi : i ≠ h * g⁻¹) : twistedRightRegular ω g i h = 0 := by
  classical
  simp [twistedRightRegular, hi]

/-- The left regular matrix acts on coefficient functions by
`(Lᵠ_g v)(gh) = ϕ(g,h)⁻¹ v(h)`. -/
theorem twistedLeftRegular_mulVec_apply [Fintype G]
    (ω : ScalarCocycle G) (g h : G) (v : G → ℂ) :
    (twistedLeftRegular ω g).mulVec v (g * h) = (ω.phase g h)⁻¹ * v h := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single h]
  · rw [twistedLeftRegular_apply_of_eq ω g (g * h) h rfl]
  · intro j hj
    rw [twistedLeftRegular_apply_of_ne]
    · simp
    · intro heq
      exact hj (mul_left_cancel heq.symm)

/-- The right regular matrix acts on coefficient functions by
`(Rᵠ_g v)(hg⁻¹) = ϕ(h,g⁻¹)⁻¹ v(h)`. -/
theorem twistedRightRegular_mulVec_apply [Fintype G]
    (ω : ScalarCocycle G) (g h : G) (v : G → ℂ) :
    (twistedRightRegular ω g).mulVec v (h * g⁻¹) =
      (ω.phase h g⁻¹)⁻¹ * v h := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single h]
  · rw [twistedRightRegular_apply_of_eq ω g (h * g⁻¹) h rfl]
  · intro j hj
    rw [twistedRightRegular_apply_of_ne]
    · simp
    · intro heq
      exact hj (mul_right_cancel heq.symm)

/-- The twisted left regular matrices obey the projective multiplication law
`Lᵠ_g Lᵠ_h = ϕ(g,h)⁻¹ Lᵠ_{gh}`. -/
theorem twistedLeftRegular_mul [Fintype G] {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (g h : G) :
    twistedLeftRegular ω g * twistedLeftRegular ω h =
      (ω.phase g h)⁻¹ • twistedLeftRegular ω (g * h) := by
  classical
  ext i k
  rw [Matrix.mul_apply, Fintype.sum_eq_single (h * k)]
  · rw [twistedLeftRegular_apply_of_eq ω h (h * k) k rfl]
    change twistedLeftRegular ω g i (h * k) * (ω.phase h k)⁻¹ =
      (ω.phase g h)⁻¹ * twistedLeftRegular ω (g * h) i k
    by_cases hi : i = g * (h * k)
    · rw [twistedLeftRegular_apply_of_eq ω g i (h * k) hi,
        twistedLeftRegular_apply_of_eq ω (g * h) i k (by simpa only [mul_assoc] using hi)]
      rw [← mul_inv_rev, ← mul_inv_rev]
      congr 1
      simpa only [mul_comm] using (phase_isCocycle hω g h k).symm
    · rw [twistedLeftRegular_apply_of_ne ω g i (h * k) hi,
        twistedLeftRegular_apply_of_ne ω (g * h) i k
          (by simpa only [mul_assoc] using hi)]
      simp
  · intro j hj
    rw [twistedLeftRegular_apply_of_ne ω h j k hj]
    simp

/-- The twisted right regular matrices obey the projective multiplication law
`Rᵠ_g Rᵠ_h = ϕ(h⁻¹,g⁻¹)⁻¹ Rᵠ_{gh}`. -/
theorem twistedRightRegular_mul [Fintype G] {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (g h : G) :
    twistedRightRegular ω g * twistedRightRegular ω h =
      (ω.phase h⁻¹ g⁻¹)⁻¹ • twistedRightRegular ω (g * h) := by
  classical
  ext i k
  rw [Matrix.mul_apply, Fintype.sum_eq_single (k * h⁻¹)]
  · rw [twistedRightRegular_apply_of_eq ω h (k * h⁻¹) k rfl]
    change twistedRightRegular ω g i (k * h⁻¹) * (ω.phase k h⁻¹)⁻¹ =
      (ω.phase h⁻¹ g⁻¹)⁻¹ * twistedRightRegular ω (g * h) i k
    by_cases hi : i = (k * h⁻¹) * g⁻¹
    · rw [twistedRightRegular_apply_of_eq ω g i (k * h⁻¹) hi,
        twistedRightRegular_apply_of_eq ω (g * h) i k
          (by simpa only [mul_inv_rev, mul_assoc] using hi)]
      rw [mul_comm (ω.phase (k * h⁻¹) g⁻¹)⁻¹, ← mul_inv_rev, ← mul_inv_rev]
      congr 1
      simpa only [mul_inv_rev, mul_comm] using phase_isCocycle hω k h⁻¹ g⁻¹
    · rw [twistedRightRegular_apply_of_ne ω g i (k * h⁻¹) hi,
        twistedRightRegular_apply_of_ne ω (g * h) i k
          (by simpa only [mul_inv_rev, mul_assoc] using hi)]
      simp
  · intro j hj
    rw [twistedRightRegular_apply_of_ne ω h j k hj]
    simp

/-- The cocycle-twisted left and right regular matrices commute. -/
theorem twistedLeftRegular_commute [Fintype G] {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (g h : G) :
    twistedLeftRegular ω g * twistedRightRegular ω h =
      twistedRightRegular ω h * twistedLeftRegular ω g := by
  classical
  ext i k
  rw [Matrix.mul_apply, Fintype.sum_eq_single (k * h⁻¹),
    Matrix.mul_apply, Fintype.sum_eq_single (g * k)]
  · rw [twistedRightRegular_apply_of_eq ω h (k * h⁻¹) k rfl,
      twistedLeftRegular_apply_of_eq ω g (g * k) k rfl]
    by_cases hi : i = g * (k * h⁻¹)
    · rw [twistedLeftRegular_apply_of_eq ω g i (k * h⁻¹) hi,
        twistedRightRegular_apply_of_eq ω h i (g * k)
          (by simpa only [mul_assoc] using hi)]
      rw [← mul_inv_rev, ← mul_inv_rev]
      congr 1
      simpa only [mul_comm] using (phase_isCocycle hω g k h⁻¹).symm
    · rw [twistedLeftRegular_apply_of_ne ω g i (k * h⁻¹) hi,
        twistedRightRegular_apply_of_ne ω h i (g * k)
          (by simpa only [mul_assoc] using hi)]
      simp
  · intro j hj
    rw [twistedLeftRegular_apply_of_ne ω g j k hj]
    simp
  · intro j hj
    rw [twistedRightRegular_apply_of_ne ω h j k hj]
    simp

/-- The cocycle-twisted left regular matrix is unitary because its phase
coefficients have norm one. -/
theorem twistedLeftRegular_mem_unitaryGroup [Fintype G] [DecidableEq G]
    (ω : ScalarCocycle G) (g : G) :
    twistedLeftRegular ω g ∈ Matrix.unitaryGroup G ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (g * i)]
  · by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq]
      rw [Matrix.star_apply, twistedLeftRegular_apply_of_eq ω g (g * i) i rfl,
        star_inv₀, ← mul_inv_rev]
      rw [show ω.phase g i * star (ω.phase g i) = 1 by
        calc
          ω.phase g i * star (ω.phase g i) = Complex.normSq (ω.phase g i) :=
            Complex.mul_conj _
          _ = 1 := by
            norm_cast
            exact Circle.normSq_coe _]
      simp
    · simp [twistedLeftRegular, hij]
  · intro k hk
    simp [twistedLeftRegular, hk]

/-- The cocycle-twisted right regular matrix is unitary because its phase
coefficients have norm one. -/
theorem twistedRightRegular_mem_unitaryGroup [Fintype G] [DecidableEq G]
    (ω : ScalarCocycle G) (g : G) :
    twistedRightRegular ω g ∈ Matrix.unitaryGroup G ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (i * g⁻¹)]
  · by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq]
      rw [Matrix.star_apply, twistedRightRegular_apply_of_eq ω g (i * g⁻¹) i rfl,
        star_inv₀, ← mul_inv_rev]
      rw [show ω.phase i g⁻¹ * star (ω.phase i g⁻¹) = 1 by
        calc
          ω.phase i g⁻¹ * star (ω.phase i g⁻¹) = Complex.normSq (ω.phase i g⁻¹) :=
            Complex.mul_conj _
          _ = 1 := by
            norm_cast
            exact Circle.normSq_coe _]
      simp
    · simp [twistedRightRegular, hij]
  · intro k hk
    simp [twistedRightRegular, hk]

/-- The coefficient identity used in the onsite Gauss operator,

`ϕ(ag⁻¹,gb) / ϕ(a,b) = 1 / (ϕ(a,g⁻¹) ϕ(g,b))`.

Besides cocyclicity, this explicitly assumes `ϕ(t⁻¹,t) = 1`, the normalization
corresponding to the scalar convention `S_{t⁻¹} = S_t⁻¹` at line 238. The
normalization is not claimed as a consequence of an arbitrary cocycle. The
coefficient rewrite is arXiv:2502.20257, lines 3763--3766. -/
theorem onsiteGauss_phase_div {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (hInv : ∀ t : G, ω.phase t⁻¹ t = 1)
    (a g b : G) :
    ω.phase (a * g⁻¹) (g * b) / ω.phase a b =
      1 / (ω.phase a g⁻¹ * ω.phase g b) := by
  have hOne : ω.phase 1 b = 1 := by
    have hc := phase_isCocycle hω 1 1 b
    have := hInv 1
    simp only [inv_one] at this
    rw [this] at hc
    simpa using hc.symm
  have h₁ := phase_isCocycle hω a g⁻¹ (g * b)
  have h₂ := phase_isCocycle hω g⁻¹ g b
  simp only [inv_mul_cancel_left] at h₁
  simp only [inv_mul_cancel] at h₂
  rw [hInv g, hOne] at h₂
  have h₂' : ω.phase g⁻¹ (g * b) * ω.phase g b = 1 := by simpa using h₂.symm
  field_simp
  calc
    ω.phase (a * g⁻¹) (g * b) * ω.phase a g⁻¹ * ω.phase g b
        = (ω.phase a g⁻¹ * ω.phase (a * g⁻¹) (g * b)) * ω.phase g b := by
            ring
    _ = (ω.phase a b * ω.phase g⁻¹ (g * b)) * ω.phase g b := by rw [h₁]
    _ = ω.phase a b := by rw [mul_assoc, h₂']; simp

end ScalarCocycle

end TNLean.Algebra
