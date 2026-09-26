/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Dimension

/-!
# Fusion rings and their positive regular element

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex` line 1236: the matrix product operator algebras of physical
symmetries carry "a unique identity element, the notion of a dual element, a pivotal
structure, etc.", captured by a fusion category; and lines 1801–1803 (`symboundary`), which use
"the fact that the algebra represents a fusion category" to produce a positive common
eigenvector of the multiplicity matrices of a module.

**Formalized here.** The fusion-ring shadow of a fusion category: structure constants
`N_{ab}^c ∈ ℕ` that are associative, have a unit `e`, and carry an involutive duality `a ↦ a*`
with `N_{ab}^e = δ_{b,a*}` and `N_{b*a*}^{c*} = N_{ab}^c` (the fusion ring of simple objects).
For such a ring, the matrix of right multiplication by the sum of all labels has strictly
positive entries, and its positive Perron–Frobenius eigenvector is a regular element `R` of the
ring: `a R = d_a R` for every label `a`, with `d_a > 0` the Perron–Frobenius dimension.

## Main definitions

* `MPOTensor.IsFusionRing`: associative structure constants with unit and duality.

## Main results

* `MPOTensor.IsFusionRing.exists_pos_mul`: every label `c` occurs in `b × a` for some `a`.
* `MPOTensor.IsFusionRing.exists_pos_regular`: a positive regular element,
  `∑_b r_b N_{ab}^c = d_a r_c`.
* `MPOTensor.IsFusionRing.perronFrobeniusDim_pos`: the Perron–Frobenius dimensions are positive.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix

namespace MPOTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fusion ring.**

Source: arXiv:2203.12563, line 1236: the fusion ring of the fusion category of a symmetry,
with its identity element and duality. The structure constants `N_{ab}^c` are associative,
`(a × b) × c = a × (b × c)`; the label `e` is a two-sided unit; the duality `a ↦ a*` is an
involution with `N_{ab}^e = δ_{b,a*}` (the unit occurs once in `a × a*` and in no other product
of two labels) and reverses products, `N_{b*a*}^{c*} = N_{ab}^c`. -/
structure IsFusionRing (N : ι → ι → ι → ℕ) (e : ι) (dual : ι → ι) : Prop where
  /-- Associativity `(a × b) × c = a × (b × c)` on the structure constants. -/
  assoc : ∀ a b c f, ∑ x, N a b x * N x c f = ∑ x, N b c x * N a x f
  /-- The label `e` is a two-sided unit. -/
  isFusionUnit : IsFusionUnit N e
  /-- The duality is an involution. -/
  dual_dual : ∀ a, dual (dual a) = a
  /-- The unit occurs in `a × b` exactly when `b = a*`, with multiplicity one. -/
  apply_unit : ∀ a b, N a b e = if b = dual a then 1 else 0
  /-- The duality reverses products. -/
  dual_anti : ∀ a b c, N (dual b) (dual a) (dual c) = N a b c

namespace IsFusionRing

variable {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}

/-- The unit label `e` satisfies `N_{ec}^c = 1`. -/
theorem unit_left (hN : IsFusionRing N e dual) (c : ι) : N e c c = 1 := by
  simpa using (hN.isFusionUnit c c).1

/-- The unit label `e` satisfies `N_{ce}^c = 1`. -/
theorem unit_right (hN : IsFusionRing N e dual) (c : ι) : N c e c = 1 := by
  simpa using (hN.isFusionUnit c c).2

/-- **Every label occurs in a right product of every label**: for all `b` and `c` there is a
label `a` with `N_{ba}^c > 0`. The coefficient of `c` in `(b × b*) × c` is at least
`N_{bb*}^e N_{ec}^c = 1`; by associativity it equals the coefficient of `c` in
`b × (b* × c)`. -/
theorem exists_pos_mul (hN : IsFusionRing N e dual) (b c : ι) : ∃ a, 0 < N b a c := by
  by_contra h
  push Not at h
  have hrhs : ∑ x, N (dual b) c x * N b x c = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [Nat.le_zero.1 (h x), mul_zero]
  rw [← hN.assoc] at hrhs
  have := (Finset.sum_eq_zero_iff.1 hrhs) e (Finset.mem_univ _)
  rw [hN.apply_unit, ite_eq_left_iff.mpr (fun h => absurd rfl h), hN.unit_left, one_mul] at this
  exact one_ne_zero this

/-- **Positive regular element of a fusion ring.** There are positive reals `r_b` with
`∑_b r_b N_{ab}^c = d_a r_c` for all labels `a` and `c`, where `d_a` is the Perron–Frobenius
dimension: `R = ∑_b r_b b` satisfies `a × R = d_a R`.

Project result, the input from the fusion category invoked at arXiv:2203.12563,
lines 1801–1803. The matrix `P_{bc} = ∑_a N_{ba}^c` of right multiplication by the sum of all
labels has positive entries (`MPOTensor.IsFusionRing.exists_pos_mul`), so its positive
Perron–Frobenius left eigenvector `r` spans its eigenspace
(`Matrix.exists_eq_smul_of_pos_of_mulVec_eq`); left multiplication by `a` commutes with right
multiplication by associativity, hence maps `r` to a multiple of `r`, and a positive left
eigenvector of `N_a` has the Perron–Frobenius dimension as its eigenvalue. -/
theorem exists_pos_regular (hN : IsFusionRing N e dual) :
    ∃ r : ι → ℝ, (∀ b, 0 < r b) ∧
      ∀ a c, ∑ b, r b * N a b c = perronFrobeniusDim N a * r c := by
  have : Nonempty ι := ⟨e⟩
  set P : Matrix ι ι ℝ := Matrix.of fun b c => ∑ a, (N b a c : ℝ) with hPdef
  have hP : ∀ b c, 0 < P b c := by
    intro b c
    obtain ⟨a, ha⟩ := hN.exists_pos_mul b c
    exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
      ⟨a, Finset.mem_univ _, by exact_mod_cast ha⟩
  obtain ⟨r, hr0, hrnn, hr⟩ :=
    Matrix.exists_nonneg_mulVec_eq_spectralRadius_smul (M := Pᵀ) fun b c => (hP c b).le
  set ρ := (spectralRadius ℂ (Pᵀ.map ((↑) : ℝ → ℂ))).toReal
  have hρ : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hrpos : ∀ c, 0 < r c := by
    intro c
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hr0
    have hbpos : 0 < r b := lt_of_le_of_ne (hrnn b) (Ne.symm hb)
    have hsum : 0 < (Pᵀ *ᵥ r) c :=
      Finset.sum_pos' (fun k _ => mul_nonneg (hP k c).le (hrnn k))
        ⟨b, Finset.mem_univ _, mul_pos (hP b c) hbpos⟩
    rw [hr, Pi.smul_apply, smul_eq_mul] at hsum
    exact lt_of_le_of_ne (hrnn c) fun h => by rw [← h, mul_zero] at hsum; exact lt_irrefl _ hsum
  have hrP : r ᵥ* P = ρ • r := by rw [← Matrix.mulVec_transpose, hr]
  refine ⟨r, hrpos, fun a => ?_⟩
  set F : Matrix ι ι ℝ := (fusionMatrix N a).map ((↑) : ℕ → ℝ)
  have hcomm : F * P = P * F := by
    ext b c
    have hnat : ∑ x, N a b x * ∑ z, N x z c = ∑ x, (∑ z, N b z x) * N a x c := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => hN.assoc a b z c
    simp only [Matrix.mul_apply, F, hPdef, Matrix.map_apply, fusionMatrix_apply, Matrix.of_apply]
    exact_mod_cast hnat
  have hw : Pᵀ *ᵥ (r ᵥ* F) = ρ • (r ᵥ* F) := by
    rw [Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hcomm, ← Matrix.vecMul_vecMul, hrP,
      Matrix.smul_vecMul]
  obtain ⟨t, ht⟩ := Matrix.exists_eq_smul_of_pos_of_mulVec_eq (fun b c => hP c b) hrpos hr hw
  have hrow : ∀ c, ∑ b, r b * N a b c = t * r c := fun c => by
    simpa [Matrix.vecMul, dotProduct, F] using congrFun ht c
  have hd : perronFrobeniusDim N a = t := perronFrobeniusDim_eq_of_pos_left_eigenvector hrpos hrow
  intro c
  rw [hd, hrow]

/-- **The Perron–Frobenius dimensions of a fusion ring are positive**: the coefficient of `a`
in `a × R` is at least `r_e N_{ae}^a = r_e > 0`. -/
theorem perronFrobeniusDim_pos (hN : IsFusionRing N e dual) (a : ι) :
    0 < perronFrobeniusDim N a := by
  obtain ⟨r, hr, hreg⟩ := hN.exists_pos_regular
  have hle : r e ≤ ∑ b, r b * N a b a := by
    have := Finset.single_le_sum (f := fun b => r b * (N a b a : ℝ))
      (fun b _ => mul_nonneg (hr b).le (Nat.cast_nonneg _)) (Finset.mem_univ e)
    simpa [hN.unit_right] using this
  rw [hreg] at hle
  exact pos_of_mul_pos_left ((hr e).trans_le hle) (hr a).le

end IsFusionRing

end MPOTensor
