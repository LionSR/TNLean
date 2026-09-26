/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TNLean.Algebra.LSymbol

/-!
# Time reversal and real scalar three-cocycles

This file isolates the scalar algebra of the interplay between a group matrix
product operator symmetry and an antiunitary time reversal, arXiv:2203.12563,
subsection `sec:TRS`, lines 865--958. Complex conjugation acts on scalar
cochains and L-symbols pointwise through `star`. No antiunitary operator,
matrix product operator, or action tensor is constructed here.

The source derives two scalar relations from time-reversal symmetry. For the
anomaly three-cocycle, lines 873--891 give `ω = ω* · (dβ)⁻¹` for a
fusion-tensor phase `β`, so that `ω` is cohomologous to its complex conjugate.
For the L-symbols, lines 935--952 give a relation between the conjugated
action tensors that yields `L* = (1, γ) ▷ L` for an action-tensor phase `γ`.

## Main results

* `ScalarThreeCochain.exists_cohomologousTo_star_eq_self`: a scalar
  three-cochain cohomologous to its complex conjugate is cohomologous to a
  real one (lines 873--891).
* `LSymbol.exists_gauge_star_eq_self`: if complex conjugation of `(ω, L)` is a
  joint scalar gauge, one joint scalar gauge makes both `ω` and `L` real.
  This conditional statement goes beyond the source.
* `LSymbol.star_apply_eq_gauge_one_apply`: the scalar step of lines 935--954,
  giving `L*ˣ_{g,h} / Lˣ_{g,h} = γ_{gh,x} / (γ_{h,x} γ_{g,h·x})`.
* `LSymbol.phase_sq_eq_of_gauge_eq_star`: under that relation the square of
  the phase `L / |L|` is an action-tensor gauge ratio.

The proofs use the unimodular square root `phaseRoot u = exp (i arg u / 2)`,
for which `u = phaseRoot u ^ 2 · |u|`. They need no finiteness of `G` or of
the set of blocks.
-/

namespace TNLean.Algebra

open Complex

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### Unimodular square roots of phases -/

/-- The unimodular square root `exp (i arg u / 2)` of the phase of a nonzero
complex number. -/
noncomputable def phaseRoot (u : Units ℂ) : Units ℂ :=
  Units.mk0 (exp (arg (u : ℂ) / 2 * I)) (exp_ne_zero _)

/-- The modulus `|u|` of a nonzero complex number, as a complex unit. -/
noncomputable def modulusUnit (u : Units ℂ) : Units ℂ :=
  Units.mk0 ((‖(u : ℂ)‖ : ℝ) : ℂ) (by simp)

/-- The phase root is unimodular: its conjugate is its inverse. -/
theorem star_phaseRoot (u : Units ℂ) : star (phaseRoot u) = (phaseRoot u)⁻¹ := by
  apply Units.ext
  rw [Units.coe_star, Units.val_inv_eq_inv_val]
  simp only [phaseRoot, Units.val_mk0]
  rw [← exp_neg, star_def, ← exp_conj]
  congr 1
  simp [map_div₀, conj_ofReal, map_ofNat]

/-- Polar decomposition `u = phaseRoot u ^ 2 · |u|`. -/
theorem phaseRoot_mul_phaseRoot_mul_modulusUnit (u : Units ℂ) :
    phaseRoot u * phaseRoot u * modulusUnit u = u := by
  apply Units.ext
  simp only [phaseRoot, modulusUnit, Units.val_mul, Units.val_mk0]
  rw [← exp_add, ← add_mul, add_halves, mul_comm]
  exact norm_mul_exp_arg_mul_I (u : ℂ)

/-- A complex unit whose conjugate is a positive real multiple of itself is
real. -/
theorem star_eq_self_of_star_eq_ofReal_mul {w p : Units ℂ}
    (hp : ∃ r : ℝ, 0 < r ∧ (p : ℂ) = r) (h : star w = p * w) :
    p = 1 ∧ star w = w := by
  obtain ⟨r, hr, hpr⟩ := hp
  have hnorm := congrArg (fun u : Units ℂ => ‖(u : ℂ)‖) h
  simp only [Units.coe_star, norm_star, Units.val_mul, norm_mul] at hnorm
  have hw : ‖(w : ℂ)‖ ≠ 0 := by simp
  have hpn : ‖(p : ℂ)‖ = 1 := by
    have := hnorm.symm
    field_simp at this
    linarith [this]
  have hp1 : p = 1 := by
    apply Units.ext
    rw [hpr, Units.val_one]
    rw [hpr, norm_real, Real.norm_eq_abs, abs_of_pos hr] at hpn
    simp [hpn]
  exact ⟨hp1, by simpa [hp1] using h⟩

/-! ### Scalar three-cochains -/

namespace ScalarThreeCochain

/-- The coboundary of a pointwise product of scalar 2-cochains is the product
of their coboundaries. -/
theorem coboundary_mul (β γ : ScalarCocycle G) :
    coboundary (β * γ) = coboundary β * coboundary γ := by
  funext g h k
  simp only [coboundary, Pi.mul_apply]
  apply Units.ext
  push_cast
  field_simp

/-- Complex conjugation commutes with the fusion gauge action. -/
theorem star_fusionGauge (β : ScalarCocycle G) (ω : ScalarThreeCochain G) :
    star (fusionGauge β ω) = fusionGauge (star β) (star ω) := by
  funext g h k
  simp only [fusionGauge, coboundary, Pi.star_apply]
  apply Units.ext
  simp only [Units.coe_star, Units.val_mul, Units.val_div_eq_div_val, star_mul',
    star_div₀]

/-- The coboundary of the modulus of a scalar 2-cochain takes positive real
values. -/
theorem coboundary_modulusUnit_pos (β : ScalarCocycle G) (g h k : G) :
    ∃ r : ℝ, 0 < r ∧
      (coboundary (fun a b => modulusUnit (β a b)) g h k : ℂ) = r := by
  refine ⟨‖(β g (h * k) : ℂ)‖ * ‖(β h k : ℂ)‖ /
      (‖(β g h : ℂ)‖ * ‖(β (g * h) k : ℂ)‖), ?_, ?_⟩
  · have := fun u : Units ℂ => norm_pos_iff.2 u.ne_zero
    exact div_pos (mul_pos (this _) (this _)) (mul_pos (this _) (this _))
  simp [coboundary, modulusUnit]

/-- **Time reversal makes the anomaly real, explicit gauge.** If the fusion
gauge by `β` maps `ω` to its complex conjugate, then the fusion gauge by the
unimodular square root of the phase of `β` makes `ω` real.

This is the scalar content of arXiv:2203.12563, lines 873--891, written in the
orientation of `fusionGauge`. -/
theorem star_fusionGauge_phaseRoot {β : ScalarCocycle G} {ω : ScalarThreeCochain G}
    (hω : fusionGauge β ω = star ω) :
    star (fusionGauge (fun g h => phaseRoot (β g h)) ω) =
      fusionGauge (fun g h => phaseRoot (β g h)) ω := by
  set s : ScalarCocycle G := fun g h => phaseRoot (β g h)
  set N : ScalarCocycle G := fun g h => modulusUnit (β g h)
  have hβ : β = s * s * N := by
    funext g h
    exact (phaseRoot_mul_phaseRoot_mul_modulusUnit (β g h)).symm
  have hs : star s = s⁻¹ := by
    funext g h
    exact star_phaseRoot (β g h)
  have hstar : star (fusionGauge s ω) = fusionGauge N (fusionGauge s ω) := by
    rw [star_fusionGauge, hs, ← hω, hβ, fusionGauge_comp, fusionGauge_comp]
    congr 1
    funext g h
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [mul_right_comm _ (N g h), mul_inv_cancel_right]
  funext g h k
  have hpt := congrFun (congrFun (congrFun hstar g) h) k
  simp only [Pi.star_apply] at hpt
  simp only [Pi.star_apply]
  exact (star_eq_self_of_star_eq_ofReal_mul (coboundary_modulusUnit_pos β g h k)
    (by simpa only [fusionGauge] using hpt)).2

/-- **Time reversal makes the anomaly real.** A scalar three-cochain
cohomologous to its complex conjugate is cohomologous to a real-valued one.

This is arXiv:2203.12563, lines 873--891: from
`ω = ω* β_{g,h} β_{gh,k} / (β_{h,k} β_{g,hk})` the source concludes that `ω`
can be gauge transformed to a real number. The hypothesis is exactly that
display for some `β`. -/
theorem exists_cohomologousTo_star_eq_self {ω : ScalarThreeCochain G}
    (h : CohomologousTo ω (star ω)) :
    ∃ ω' : ScalarThreeCochain G, CohomologousTo ω' ω ∧ star ω' = ω' := by
  obtain ⟨β, hβ⟩ := h
  have hω : fusionGauge (star β) ω = star ω := by
    have := congrArg star hβ
    rwa [star_fusionGauge, star_star] at this
  exact ⟨_, ⟨_, rfl⟩, star_fusionGauge_phaseRoot hω⟩

end ScalarThreeCochain

/-! ### L-symbols -/

namespace LSymbol

/-- Complex conjugation commutes with the joint scalar gauge action. -/
theorem star_gauge (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (L : LSymbol G X) :
    star (gauge β γ L) = gauge (star β) (star γ) (star L) := by
  funext x g h
  simp only [gauge, Pi.star_apply]
  apply Units.ext
  simp only [Units.coe_star, Units.val_mul, Units.val_div_eq_div_val, star_mul',
    star_div₀]

/-- The joint scalar gauge by the moduli of `β` and `γ` has positive real
prefactor. -/
theorem gauge_modulusUnit_pos (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (x : X) (g h : G) :
    ∃ r : ℝ, 0 < r ∧
      (((modulusUnit (γ (g * h) x) * modulusUnit (β g h)) /
        (modulusUnit (γ g (h • x)) * modulusUnit (γ h x)) : Units ℂ) : ℂ) = r := by
  refine ⟨‖(γ (g * h) x : ℂ)‖ * ‖(β g h : ℂ)‖ /
      (‖(γ g (h • x) : ℂ)‖ * ‖(γ h x : ℂ)‖), ?_, ?_⟩
  · have := fun u : Units ℂ => norm_pos_iff.2 u.ne_zero
    exact div_pos (mul_pos (this _) (this _)) (mul_pos (this _) (this _))
  simp [modulusUnit]

/-- **Time reversal makes the L-symbols real, explicit gauge.** If the joint
gauge by `(β, γ)` maps `L` to its complex conjugate, then the joint gauge by
the unimodular square roots of the phases of `β` and `γ` makes `L` real. -/
theorem star_gauge_phaseRoot {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    {L : LSymbol G X} (hL : gauge β γ L = star L) :
    star (gauge (fun g h => phaseRoot (β g h)) (fun g x => phaseRoot (γ g x)) L) =
      gauge (fun g h => phaseRoot (β g h)) (fun g x => phaseRoot (γ g x)) L := by
  set s : ScalarCocycle G := fun g h => phaseRoot (β g h)
  set N : ScalarCocycle G := fun g h => modulusUnit (β g h)
  set t : ActionTensorGauge G X := fun g x => phaseRoot (γ g x)
  set M : ActionTensorGauge G X := fun g x => modulusUnit (γ g x)
  have hβ : β = s * s * N := by
    funext g h
    exact (phaseRoot_mul_phaseRoot_mul_modulusUnit (β g h)).symm
  have hγ : γ = t * t * M := by
    funext g x
    exact (phaseRoot_mul_phaseRoot_mul_modulusUnit (γ g x)).symm
  have hs : star s = s⁻¹ := by
    funext g h
    exact star_phaseRoot (β g h)
  have ht : star t = t⁻¹ := by
    funext g x
    exact star_phaseRoot (γ g x)
  have hstar : star (gauge s t L) = gauge N M (gauge s t L) := by
    rw [star_gauge, hs, ht, ← hL, hβ, hγ, gauge_comp, gauge_comp]
    congr 1
    · funext g h
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_right_comm _ (N g h), mul_inv_cancel_right]
    · funext g x
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_right_comm _ (M g x), mul_inv_cancel_right]
  funext x g h
  have hpt := congrFun (congrFun (congrFun hstar x) g) h
  simp only [Pi.star_apply] at hpt
  simp only [Pi.star_apply]
  exact (star_eq_self_of_star_eq_ofReal_mul (gauge_modulusUnit_pos β γ x g h)
    (by simpa only [gauge] using hpt)).2

/-- **Time reversal makes the anomaly and the L-symbols jointly real.** If
complex conjugation of a scalar three-cochain `ω` and of L-symbols `L` is the
joint scalar gauge by `(β, γ)`, then a single joint scalar gauge makes both
real.

This is not a statement of arXiv:2203.12563. The source derives
`β ▷ ω = ω*` at lines 873--891 and, with the fusion-tensor phase omitted,
`(1, γ) ▷ L = L*` at lines 935--954; the hypotheses here, with the same `β`
in both relations, are assumed rather than derived from a time-reversal
operator. Compatibility of `L` with `ω` is not needed. -/
theorem exists_gauge_star_eq_self {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    {ω : ScalarThreeCochain G} {L : LSymbol G X}
    (hω : ScalarThreeCochain.fusionGauge β ω = star ω) (hL : gauge β γ L = star L) :
    ∃ (β' : ScalarCocycle G) (γ' : ActionTensorGauge G X),
      star (ScalarThreeCochain.fusionGauge β' ω) =
          ScalarThreeCochain.fusionGauge β' ω ∧
        star (gauge β' γ' L) = gauge β' γ' L :=
  ⟨_, _, ScalarThreeCochain.star_fusionGauge_phaseRoot hω, star_gauge_phaseRoot hL⟩

/-- **Corrected L-symbol relation under time reversal.** Let `T` be a nonzero
vector, the complex conjugate of the fused action tensor `W_{g,h} V_{gh,x}`,
and let `P` be the complex conjugate of the composite `V_{g,h·x} V_{h,x}`, so
that the conjugate of `F1group` reads `P = L*ˣ_{g,h} T`. If the time-reversal
display `γ_{h,x} γ_{g,h·x} P = Lˣ_{g,h} γ_{gh,x} T` holds, then

`L*ˣ_{g,h} = γ_{gh,x} / (γ_{h,x} γ_{g,h·x}) · Lˣ_{g,h}`,

that is, the conjugate of `L` is the joint gauge of `L` by `(1, γ)`.

This is the scalar step of arXiv:2203.12563, lines 935--954.

**Local fix (conjugate ratio in `TRSF1group`):** The source prints the
consequence, `TRSF1group` at line 954, as
`|Lˣ_{g,h}|² = γ_{gh,x} / (γ_{h,x} γ_{g,h·x})`. Its own display at lines
935--952 together with the conjugate of `F1group` gives the ratio `L* / L`
in place of `|L|²`, and the printed form fails for an on-site
`ℤ₂ × ℤ₂` symmetry. This declaration and
`LSymbol.phase_sq_eq_of_gauge_eq_star` use the corrected ratio. See
`docs/paper-gaps/glm23_time_reversal_l_symbol.tex`. -/
theorem star_apply_eq_gauge_one_apply {E : Type*} [AddCommGroup E] [Module ℂ E]
    {γ : ActionTensorGauge G X} {L : LSymbol G X} {x : X} {g h : G} {T P : E}
    (hT : T ≠ 0) (hconj : P = (star (L x g h : ℂ)) • T)
    (hdisp : ((γ h x : ℂ) * γ g (h • x)) • P = ((L x g h : ℂ) * γ (g * h) x) • T) :
    star (L x g h) = gauge (fun _ _ => 1) γ L x g h := by
  rw [hconj, smul_smul] at hdisp
  have hscalar := smul_left_injective ℂ hT hdisp
  apply Units.ext
  simp only [Units.coe_star, gauge, Units.val_mul, Units.val_div_eq_div_val, mul_one]
  have h1 : (γ h x : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (γ g (h • x) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  linear_combination hscalar

/-- **The squared phase of an L-symbol is a gauge ratio.** If the conjugate
of `L` is its joint gauge by `(β, γ)`, then the square of the phase
`Lˣ_{g,h} / |Lˣ_{g,h}|` equals `γ_{g,h·x} γ_{h,x} / (γ_{gh,x} β_{g,h})`, the
joint gauge of the constant L-symbol one by `(β⁻¹, γ⁻¹)`.

For `β = 1` this is the correct form of the statement of arXiv:2203.12563,
lines 954--957, that the L-symbols squared are trivial because they can be
decomposed as a gauge transformation. The modulus `|L|` is not constrained.
The local correction is recorded at `LSymbol.star_apply_eq_gauge_one_apply`. -/
theorem phase_sq_eq_of_gauge_eq_star {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    {L : LSymbol G X} (hL : gauge β γ L = star L) (x : X) (g h : G) :
    ((L x g h : ℂ) / (‖(L x g h : ℂ)‖ : ℂ)) ^ 2 =
      ((γ g (h • x) * γ h x / (γ (g * h) x * β g h) : Units ℂ) : ℂ) := by
  have hpt := congrArg Units.val (congrFun (congrFun (congrFun hL x) g) h)
  simp only [gauge, Units.val_mul, Units.val_div_eq_div_val, Pi.star_apply,
    Units.coe_star] at hpt
  have hsq : (star (L x g h : ℂ)) * (L x g h : ℂ) = ((‖(L x g h : ℂ)‖ : ℂ)) ^ 2 := by
    rw [star_def, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
    push_cast
    ring
  have hLn : (‖(L x g h : ℂ)‖ : ℂ) ≠ 0 := by simp
  have h1 : (γ g (h • x) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (γ h x : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : (γ (g * h) x : ℂ) ≠ 0 := Units.ne_zero _
  have h4 : (β g h : ℂ) ≠ 0 := Units.ne_zero _
  simp only [Units.val_mul, Units.val_div_eq_div_val]
  rw [← hpt] at hsq
  field_simp
  field_simp at hsq
  linear_combination hsq

end LSymbol

end TNLean.Algebra
