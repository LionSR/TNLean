/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.TimeReversalIndex
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# No normal spin-`1/2` MPS is invariant under on-site `SU(2)`

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
`Papers/2011.12127/TN-Review-main.tex` line 1100, and §III.C, paragraph
"Kramers theorem and Lieb-Schultz-Mattis" (line 1230): for a spin-`1/2` chain with
`SU(2)` symmetry, no uniform normal MPS exhibits the symmetry, the tensor-network
form of the Lieb–Schultz–Mattis theorem.

**Formalized here.**
* `MPSTensor.not_anticommuting_gauges_of_isNormal`: if two physical operators
  anticommute, `P Q = -Q P`, no normal tensor of positive bond dimension has
  virtual gauges for both, `∑ⱼ Pᵢⱼ Aʲ = ζ X Aⁱ X⁻¹` and
  `∑ⱼ Qᵢⱼ Aʲ = η Y Aⁱ Y⁻¹` with `ζ, η ≠ 0`: composing the two twists in both orders
  gives `(Y X) Aⁱ (Y X)⁻¹ = -(X Y) Aⁱ (X Y)⁻¹`, which eq. `eq:XAX=B` rules out.
* `MPSTensor.mpv_twistedTensor_eq_of_mul_eq`: if every twist of a tensor multiplies
  its matrix product vector at length `N` by a phase, the phase of a commutator is
  one.
* `MPSTensor.not_forall_mpv_twistedTensor_eq_smul_specialUnitaryGroup_of_isNormal`:
  no normal tensor on a spin-`1/2` site of positive bond dimension is invariant up to
  phases, `U(g)^{⊗N} |ψ_N⟩ ≃ |ψ_N⟩`, under the defining representation of `SU(2)`.
  The phases are trivial on `iσ_x` and `iσ_z`, which are commutators in `SU(2)`;
  blocking to an odd injective length, these two elements act by anticommuting
  Kronecker powers.  `MPSTensor.not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal`
  is the exact-invariance form.

The source argues through the Clebsch–Gordan structure of the virtual
representations (integer and half-integer spins alternate).  The proof here uses
only the anticommuting pair `iσ_x`, `iσ_z` inside `SU(2)`.

## Main results

* `MPSTensor.not_anticommuting_gauges_of_isNormal`
* `MPSTensor.blockKron_smul`
* `MPSTensor.mpv_twistedTensor`
* `MPSTensor.mpv_twistedTensor_eq_of_mul_eq`
* `MPSTensor.not_forall_mpv_twistedTensor_eq_smul_specialUnitaryGroup_of_isNormal`
* `MPSTensor.not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Twisting a gauge-transformed family:
if `Bʲ = c Y Cʲ Y⁻¹`, then `∑ⱼ Pᵢⱼ Bʲ = c Y (∑ⱼ Pᵢⱼ Cʲ) Y⁻¹`. -/
private lemma sum_smul_gauge {B C : MPSTensor d D} (P : Matrix (Fin d) (Fin d) ℂ)
    (Y : GL (Fin D) ℂ) (c : ℂ)
    (h : ∀ j, B j = c • ((Y : Matrix (Fin D) (Fin D) ℂ) * C j *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) (i : Fin d) :
    ∑ j : Fin d, P i j • B j = c • ((Y : Matrix (Fin D) (Fin D) ℂ) *
      (∑ j : Fin d, P i j • C j) * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  simp only [h, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Matrix.mul_smul,
    Matrix.smul_mul, smul_comm c]

/-- The twist by a product is the composite of the twists. -/
private lemma sum_mul_smul (A : MPSTensor d D) (P Q : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    ∑ k : Fin d, (P * Q) i k • A k = ∑ j : Fin d, P i j • ∑ k : Fin d, Q j k • A k := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- The composite of two gauged twists is gauged by the product of the gauges. -/
private lemma sum_mul_smul_gauge {A : MPSTensor d D} {P Q : Matrix (Fin d) (Fin d) ℂ}
    {X Y : GL (Fin D) ℂ} {ζ η : ℂ}
    (hX : ∀ i, ∑ j : Fin d, P i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (hY : ∀ i, ∑ j : Fin d, Q i j • A j =
      η • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (i : Fin d) :
    ∑ k : Fin d, (P * Q) i k • A k = (η * ζ) •
      (((Y * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((Y * X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  rw [sum_mul_smul, sum_smul_gauge P Y η hY i, hX i]
  simp only [mul_inv_rev, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc]

/-- **Anticommuting physical symmetries have no common gauge description.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1085–1086 and 1117): a physical symmetry acting projectively on the site is
obstructed by eq. `eq:XAX=B`.  If `P Q = -Q P`, no normal tensor of positive bond
dimension satisfies both `∑ⱼ Pᵢⱼ Aʲ = ζ X Aⁱ X⁻¹` and
`∑ⱼ Qᵢⱼ Aʲ = η Y Aⁱ Y⁻¹` with `ζ, η ≠ 0`. -/
theorem not_anticommuting_gauges_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {P Q : Matrix (Fin d) (Fin d) ℂ} (hPQ : P * Q = -(Q * P))
    (X Y : GL (Fin D) ℂ) {ζ η : ℂ} (hζ : ζ ≠ 0) (hη : η ≠ 0)
    (hX : ∀ i, ∑ j : Fin d, P i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (hY : ∀ i, ∑ j : Fin d, Q i j • A j =
      η • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ))) :
    False := by
  have hPQA := sum_mul_smul_gauge hX hY
  have hQPA := sum_mul_smul_gauge hY hX
  -- `(Y X) Aⁱ (Y X)⁻¹ = -(X Y) Aⁱ (X Y)⁻¹`.
  have hrel : ∀ i, (((Y * X : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
      (((Y * X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = (-1 : ℂ) •
        ((((X * Y : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((X * Y)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    have h1 : ∑ k : Fin d, (P * Q) i k • A k = -∑ k : Fin d, (Q * P) i k • A k := by
      rw [hPQ, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.neg_apply, neg_smul]
    rw [hPQA i, hQPA i, mul_comm ζ η, ← smul_neg] at h1
    rw [smul_right_injective _ (mul_ne_zero hη hζ) h1, neg_one_smul]
  obtain ⟨hc, -⟩ := gauge_phase_unique_of_isNormal hA (X := (Y * X)⁻¹) (Y := (X * Y)⁻¹)
    (c := -1) (fun i => by rw [inv_inv, inv_inv]; exact hrel i)
  norm_num at hc

/-- The Kronecker power of a scalar multiple: `blockKron L (c • P) = c ^ L • blockKron L P`. -/
theorem blockKron_smul {m n : ℕ} (L : ℕ) (c : ℂ) (P : Matrix (Fin m) (Fin n) ℂ) :
    blockKron L (c • P) = c ^ L • blockKron L P := by
  ext I J
  simp [blockKron, Finset.prod_mul_distrib, Finset.prod_const]

/-- **The twisted matrix product vector is the Kronecker-power image of the original.**
`ψ_{A_g}(σ) = ∑_τ (∏ₗ U(g)_{σₗ τₗ}) ψ_A(τ)`. -/
theorem mpv_twistedTensor {G : Type*} [Monoid G] (B : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (twistedTensor B U g) σ =
      ∑ τ : Fin N → Fin d, (∏ l, U g (σ l) (τ l)) * mpv B τ := by
  simp only [mpv, coeff, evalWord_ofFn_eq_prod, twistedTensor]
  exact Matrix.trace_prod_ofFn_sum_smul (fun l j => U g (σ l) j) (fun _ j => B j)

/-- **Invariance up to a phase is exact on commutators.** Suppose that at length `N`
every twist of `A` has a matrix product vector proportional to that of `A`,
`U(g)^{⊗N} ψ = c(g) ψ`.  If `k b a = a b`, that is, `k` is the commutator
`a b a⁻¹ b⁻¹`, then the twist by `k` has the same matrix product vector as `A`: the
phases `c` are multiplicative whenever `ψ ≠ 0`, so `c(k) = 1`. -/
theorem mpv_twistedTensor_eq_of_mul_eq {G : Type*} [Group G] {A : MPSTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {N : ℕ}
    (hproj : ∀ g : G, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
      mpv (twistedTensor A U g) σ = c * mpv A σ)
    {a b k : G} (hk : k * (b * a) = a * b) (σ : Fin N → Fin d) :
    mpv (twistedTensor A U k) σ = mpv A σ := by
  classical
  by_cases hψ : ∀ τ : Fin N → Fin d, mpv A τ = 0
  · obtain ⟨c, hc⟩ := hproj k
    rw [hc, hψ, mul_zero]
  push Not at hψ
  obtain ⟨τ₀, hτ₀⟩ := hψ
  choose c hc using hproj
  have hmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    have e : mpv (twistedTensor A U (g * h)) τ₀ = c g * c h * mpv A τ₀ := by
      rw [twistedTensor_mul, mpv_twistedTensor]
      simp_rw [hc h, mul_left_comm _ (c h), ← Finset.mul_sum, ← mpv_twistedTensor, hc g]
      ring
    exact mul_right_cancel₀ hτ₀ ((hc (g * h) τ₀).symm.trans e)
  have h1 : c 1 = 1 := by
    have e := hc 1 τ₀
    rw [twistedTensor_one] at e
    exact mul_right_cancel₀ hτ₀ (e.symm.trans (one_mul _).symm)
  have hne : ∀ g, c g ≠ 0 := fun g h0 => by
    have e := hmul g g⁻¹
    rw [mul_inv_cancel, h1, h0, zero_mul] at e
    exact one_ne_zero e
  have hck : c k = 1 := by
    have e := congrArg c hk
    rw [hmul, hmul, hmul] at e
    exact mul_right_cancel₀ (mul_ne_zero (hne b) (hne a)) (by rw [e, one_mul, mul_comm])
  rw [hc k, hck, one_mul]

/-- The matrix `iσ_x` lies in `SU(2)`. -/
private lemma iPauliX_mem : (!![0, Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, by simp [Matrix.det_fin_two]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

/-- The matrix `iσ_z` lies in `SU(2)`. -/
private lemma iPauliZ_mem : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, by simp [Matrix.det_fin_two]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

/-- A binary-tetrahedral element `b₁` with `iσ_x = [iσ_z, b₁]`. -/
private lemma tetraX_mem :
    (!![(1 - Complex.I) / 2, (1 - Complex.I) / 2; (-1 - Complex.I) / 2, (1 + Complex.I) / 2] :
      Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, map_ofNat,
        Complex.ext_iff] <;> norm_num
  · simp [Matrix.det_fin_two, Complex.ext_iff]; norm_num

/-- A binary-tetrahedral element `b₂` with `iσ_z = [iσ_x, b₂]`. -/
private lemma tetraZ_mem :
    (!![(1 - Complex.I) / 2, (1 + Complex.I) / 2; (-1 + Complex.I) / 2, (1 + Complex.I) / 2] :
      Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, map_ofNat,
        Complex.ext_iff] <;> norm_num
  · simp [Matrix.det_fin_two, Complex.ext_iff]; norm_num

/-- **No normal spin-`1/2` MPS is invariant, even up to phases, under on-site
`SU(2)`.** Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1086 and 1100): for the symmetry `U(g)^{⊗N} |ψ_N⟩ ≃ |ψ_N⟩` of a spin-`1/2`
chain under `SU(2)`, "no uniform normal/injective MPS can exhibit such a symmetry", the
tensor-network form of the Lieb–Schultz–Mattis theorem (line 1230).

The hypothesis is the source's invariance up to a phase: at every length `N`, the
Kronecker power of each `g ∈ SU(2)` maps the matrix product vector to a multiple of
itself.  The phases are trivial on the commutators `iσ_x = [iσ_z, b₁]` and
`iσ_z = [iσ_x, b₂]` (with `b₁, b₂` in the binary tetrahedral group), which reduces to
the anticommuting pair `iσ_x`, `iσ_z`. -/
theorem not_forall_mpv_twistedTensor_eq_smul_specialUnitaryGroup_of_isNormal [NeZero D]
    {A : MPSTensor 2 D} (hA : Kraus.IsNormal A) :
    ¬ ∀ (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (N : ℕ), ∃ c : ℂ, ∀ σ : Fin N → Fin 2,
      mpv (twistedTensor A (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype g) σ =
        c * mpv A σ := by
  intro hproj
  obtain ⟨N, hNpos, hN⟩ := hA
  let U := (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype
  let gx : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, iPauliX_mem⟩
  let gz : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, iPauliZ_mem⟩
  let b₁ : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, tetraX_mem⟩
  let b₂ : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, tetraZ_mem⟩
  have hx : gx * (b₁ * gz) = gz * b₁ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gx, gz, b₁, Complex.ext_iff] <;> norm_num
  have hz : gz * (b₂ * gx) = gx * b₂ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gz, gx, b₂, Complex.ext_iff] <;> norm_num
  have hSx : SameMPV A (twistedTensor A U gx) := fun M σ =>
    (mpv_twistedTensor_eq_of_mul_eq (fun g => hproj g M) hx σ).symm
  have hSz : SameMPV A (twistedTensor A U gz) := fun M σ =>
    (mpv_twistedTensor_eq_of_mul_eq (fun g => hproj g M) hz σ).symm
  -- Block to the odd length `L = 2N + 1`, where the blocked tensor is injective.
  set L := 2 * N + 1 with hL
  have hinj : Kraus.IsInjective (blockTensor A L) :=
    (isNBlkInjective_iff_blockTensor_isInjective A L).1
      (isNBlkInjective_of_le hNpos hN (by omega))
  have hgauge {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hS : SameMPV A (twistedTensor A U g)) :
      GaugeEquiv (blockTensor A L) (twistedTensor (blockTensor A L) (blockKronAction L U) g) := by
    rw [twistedTensor_blockTensor_comm]
    exact (sameMPV_iff_gaugeEquiv_of_injective hinj).1 (hS.blockTensor L)
  obtain ⟨X, hX⟩ := hgauge hSx
  obtain ⟨Y, hY⟩ := hgauge hSz
  have hanti : (gx : Matrix (Fin 2) (Fin 2) ℂ) * (gz : Matrix (Fin 2) (Fin 2) ℂ) =
      (-1 : ℂ) • ((gz : Matrix (Fin 2) (Fin 2) ℂ) * (gx : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gx, gz, Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ : blockKron L (gx : Matrix (Fin 2) (Fin 2) ℂ) * blockKron L gz =
      -(blockKron L (gz : Matrix (Fin 2) (Fin 2) ℂ) * blockKron L gx) := by
    rw [← blockKron_mul, ← blockKron_mul, hanti, blockKron_smul, hL, pow_succ, pow_mul]
    simp
  exact not_anticommuting_gauges_of_isNormal hinj.isNormal hPQ X Y one_ne_zero one_ne_zero
    (fun i => by simpa [twistedTensor, U] using hX i)
    (fun i => by simpa [twistedTensor, U] using hY i)

/-- **No normal spin-`1/2` MPS is invariant under on-site `SU(2)`.** The exact form of
`not_forall_mpv_twistedTensor_eq_smul_specialUnitaryGroup_of_isNormal`: on-site
symmetry, which preserves the matrix product vectors exactly, is invariance with every
phase equal to one. -/
theorem not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal [NeZero D]
    {A : MPSTensor 2 D} (hA : Kraus.IsNormal A) :
    ¬ IsOnSiteSymmetric A (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype := fun hsymm =>
  not_forall_mpv_twistedTensor_eq_smul_specialUnitaryGroup_of_isNormal hA fun g _ =>
    ⟨1, fun σ => by rw [one_mul, ← hsymm g _ σ]⟩

end MPSTensor
