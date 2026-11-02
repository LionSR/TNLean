/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTraceForcedBond
import TNLean.MPS.Core.ForcedColumnNormality
import TNLean.MPS.Examples.Z3Anomalous.Z3ClockDefect
import TNLean.MPS.MPDO.BondOneOperator
import TNLean.MPS.MPDO.IdentityTensor
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorCohomology
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# The anomaly class of the `ℤ₃` clock symmetry is trivial

The clock operators `U = X^{⊗N} ∏_k CZ_{k,k+1}` and `V = X^{2 ⊗ N} ∏_k CZ²_{k,k+1} Z²_k` of
`Z3ClockTensor` multiply as `ℤ₃` only up to the phases `ω^N`: `U² = ω^N V`, `U V = V U = ω^N`,
`V² = U`. Rescaling every site by a cube root `α` of `ω` removes these phases. With
`U' = α^N U` and `V' = (α² ω)^N V`,

`U'² = V'`, `U' V' = V' U' = 1`, `V'² = U'`

on every nonempty periodic chain, so the identity tensor of bond dimension one together with
the tensors `α U` and `α² ω V` is an exact representation of `ℤ₃` by normal tensors
(`clockFamily_isNormalRepresentation`). The class computed below is the class of this
rescaled family; it is trivial for each of the three cube roots `α` of `ω`.

The class is computed through the obstruction theorem of arXiv:2502.20257, `main.tex`
line 1545 (`IsNormalRepresentation.isTrivialGaugeClass_omega_of_invariant`): a normal matrix
product state fixed by every operator of the family forces the anomaly three-cocycle to have
trivial gauge class. The fixed state is the bond-three state
`|ψ⟩ = ∑_s ∏_k α^{s_{k+1}} ω^{p(s_k, s_{k+1})} |s⟩` for an explicit exponent table `p`
(`clockState`): the controlled phase of `U` is absorbed by the shift of `p` up to a term
`k(s_k) − k(s_{k+1})` that telescopes around the ring, and the carry of the shift `s ↦ s + 1`
at `s = 2` is absorbed by `α³ = ω`.

Hence for every choice of fusion tensors the anomaly three-cocycle is cohomologous to the
trivial one, the class in `H³(ℤ₃, ℂˣ)` vanishes, and the gauge-invariant product
`ω(g,1,g) ω(g,g,g) ω(g,g²,g)` is one, against `ω₃²` for the anomalous representation of
`Z3AnomalyClass`.

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), `Papers/2405.00439/MPU-DW.tex`
line 2040: the classes `ω_j` of `ℤ_n`, with `j = 0` trivial. arXiv:2502.20257, `main.tex`
line 1545 and lines 1920–1925: an anomalous representation has no invariant normal state.
The clock tensors themselves are a construction of this development (`Z3ClockTensor`).

## Main definitions

* `Z3Clock.normUTensor`, `Z3Clock.normVTensor`: the rescaled tensors `α U` and `α² ω V`.
* `Z3Clock.clockFamily`: the group family `{1, α U, α² ω V}` over `ℤ₃`.
* `Z3Clock.clockState`: the invariant normal state of bond dimension three.

## Main results

* `Z3Clock.clockFamily_isNormalRepresentation`: the rescaled family is an exact
  representation of `ℤ₃` with normal tensors.
* `Z3Clock.fixesMPV_clockState`: every operator of the family fixes the state.
* `Z3Clock.isTrivialGaugeClass_omega_clockFamily`: for every choice of fusion tensors the
  anomaly three-cocycle has trivial gauge class.
* `Z3Clock.clockFamily_anomalyClass_eq_zero`: the anomaly class vanishes in `H³(ℤ₃, ℂˣ)`.
* `Z3Clock.cyclicInvariant_omega_clockFamily`: the gauge-invariant product is one.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Z3Clock

open MPOTensor MPSTensor TNLean.Algebra

/-! ### Cube roots of `ω` -/

/-- The primitive ninth root of unity `exp(2πi/9)`, a cube root of `ω`. -/
def clockAlpha : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

theorem clockAlpha_pow_three : clockAlpha ^ 3 = omega := by
  rw [clockAlpha, ← Complex.exp_nat_mul]
  simp only [omega, ScalarThreeCochain.rootOfUnity]
  congr 1
  push_cast
  ring

theorem omega_ne_zero : omega ≠ 0 := isPrimitiveRoot_omega.ne_zero (by norm_num)

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using h

variable {α : ℂ}

theorem ne_zero_of_pow_three_eq_omega (hα : α ^ 3 = omega) : α ≠ 0 := by
  rintro rfl
  exact omega_ne_zero (by simpa using hα.symm)

theorem phaseChar_ne_zero (a : Fin 3) : phaseChar a ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_phaseChar]; exact one_ne_zero)

theorem phaseChar_two : phaseChar 2 = omega ^ 2 := by
  simp [phaseChar_apply]

/-! ### The rescaled tensors -/

/-- The tensor `α U`: the periodic operator is `α^N X^{⊗N} ∏_k CZ_{k,k+1}`. -/
def normUTensor (α : ℂ) : MPOTensor 3 3 := α • uTensor

/-- The tensor `α² ω V`: the periodic operator is `(α² ω)^N X^{2 ⊗ N} ∏_k CZ²_{k,k+1} Z²_k`. -/
def normVTensor (α : ℂ) : MPOTensor 3 3 := (α ^ 2 * omega) • vTensor

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem mpo_normUTensor : mpo (normUTensor α) N = α ^ N • mpo uTensor N := mpo_smul _ _ _

omit [NeZero N] in
theorem mpo_normVTensor :
    mpo (normVTensor α) N = (α ^ 2 * omega) ^ N • mpo vTensor N := mpo_smul _ _ _

/-- **`U'² = V'`** on every nonempty periodic chain. -/
theorem mpo_normU_mul_normU :
    mpo (normUTensor α) N * mpo (normUTensor α) N = mpo (normVTensor α) N := by
  rw [mpo_normUTensor, mpo_normVTensor, Matrix.smul_mul, Matrix.mul_smul, mpo_u_mul_u,
    smul_smul, smul_smul, ← pow_add, ← two_mul, pow_mul, ← mul_pow]

/-- **`U' V' = 1`** on every nonempty periodic chain. -/
theorem mpo_normU_mul_normV (hα : α ^ 3 = omega) :
    mpo (normUTensor α) N * mpo (normVTensor α) N = 1 := by
  rw [mpo_normUTensor, mpo_normVTensor, Matrix.smul_mul, Matrix.mul_smul, mpo_u_mul_v,
    smul_smul, smul_smul, ← mul_pow, ← mul_pow]
  have h : α * (α ^ 2 * omega) * omega = 1 := by
    rw [show α * (α ^ 2 * omega) * omega = α ^ 3 * omega ^ 2 by ring, hα, ← pow_succ',
      omega_pow_three]
  rw [h, one_pow, one_smul]

/-- **`V' U' = 1`** on every nonempty periodic chain. -/
theorem mpo_normV_mul_normU (hα : α ^ 3 = omega) :
    mpo (normVTensor α) N * mpo (normUTensor α) N = 1 := by
  rw [mpo_normUTensor, mpo_normVTensor, Matrix.smul_mul, Matrix.mul_smul, mpo_v_mul_u,
    smul_smul, smul_smul, ← mul_pow, ← mul_pow]
  have h : α ^ 2 * omega * α * omega = 1 := by
    rw [show α ^ 2 * omega * α * omega = α ^ 3 * omega ^ 2 by ring, hα, ← pow_succ',
      omega_pow_three]
  rw [h, one_pow, one_smul]

/-- **`V'² = U'`** on every nonempty periodic chain. -/
theorem mpo_normV_mul_normV (hα : α ^ 3 = omega) :
    mpo (normVTensor α) N * mpo (normVTensor α) N = mpo (normUTensor α) N := by
  rw [mpo_normUTensor, mpo_normVTensor, Matrix.smul_mul, Matrix.mul_smul, mpo_v_mul_v,
    smul_smul, ← mul_pow]
  congr 2
  rw [show α ^ 2 * omega * (α ^ 2 * omega) = α * (α ^ 3 * omega ^ 2) by ring, hα, ← pow_succ',
    omega_pow_three, mul_one]

/-! ### The group family -/

/-- The tensors of the identity, `α U` and `α² ω V`, indexed by the residues `0, 1, 2`; the bond
dimensions are those of the unscaled family `{1, U, V}`. -/
def clockRepTensor (α : ℂ) : (a : Fin 3) → MPOTensor 3 (repBondDim a)
  | 0 => idTensor 3
  | 1 => normUTensor α
  | 2 => normVTensor α

/-- **The rescaled clock family `{1, α U, α² ω V}` over `ℤ₃`**: the residue `a` carries the
tensor of `(α U)^a`. -/
def clockFamily (α : ℂ) : GroupFamily (Multiplicative (ZMod 3)) 3 where
  bondDim g := repBondDim (Multiplicative.toAdd g)
  bondDim_pos g := by
    generalize (Multiplicative.toAdd g : Fin 3) = a
    fin_cases a <;> decide
  tensor g := clockRepTensor α (Multiplicative.toAdd g)

omit [NeZero N] in
private theorem mpo_clockRepTensor_mul (hα : α ^ 3 = omega) (hN : 0 < N) (a b : Fin 3) :
    mpo (clockRepTensor α a) N * mpo (clockRepTensor α b) N =
      mpo (clockRepTensor α (a + b)) N := by
  have : NeZero N := ⟨by omega⟩
  fin_cases a <;> fin_cases b
  · exact (mpo_idTensor 3 N).symm ▸ Matrix.one_mul _
  · exact (mpo_idTensor 3 N).symm ▸ Matrix.one_mul _
  · exact (mpo_idTensor 3 N).symm ▸ Matrix.one_mul _
  · exact (mpo_idTensor 3 N).symm ▸ Matrix.mul_one _
  · exact mpo_normU_mul_normU
  · exact (mpo_normU_mul_normV hα).trans (mpo_idTensor 3 N).symm
  · exact (mpo_idTensor 3 N).symm ▸ Matrix.mul_one _
  · exact (mpo_normV_mul_normU hα).trans (mpo_idTensor 3 N).symm
  · exact mpo_normV_mul_normV hα

/-! ### Normality -/

/-- `ω^{a b} = (ω^b)^a` on residues. -/
theorem phaseChar_mul (a b : Fin 3) : phaseChar (a * b) = phaseChar b ^ (a : ℕ) := by
  fin_cases a
  · simp
  · simp
  · exact (by rw [show (2 : Fin 3) * b = b + b by revert b; decide, AddChar.map_add_eq_mul, sq] :
      phaseChar (2 * b) = phaseChar b ^ 2)

theorem phaseChar_injective : Function.Injective phaseChar := by
  intro a b h
  rw [phaseChar_apply, phaseChar_apply] at h
  exact Fin.ext (isPrimitiveRoot_omega.pow_inj a.isLt b.isLt h)

/-- A matrix whose columns are nonzero multiples of the columns of a Vandermonde matrix with
distinct nodes is invertible. -/
private theorem det_scaled_vandermonde_ne_zero {n : ℕ} {x c : Fin n → ℂ}
    (hx : Function.Injective x) (hc : ∀ j, c j ≠ 0) :
    (Matrix.of fun l j : Fin n ↦ c j * x j ^ (l : ℕ)).det ≠ 0 := by
  have h : (Matrix.of fun l j : Fin n ↦ c j * x j ^ (l : ℕ)) =
      (Matrix.vandermonde x)ᵀ * Matrix.diagonal c := by
    ext l j
    simp [Matrix.vandermonde_apply, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hc j)

/-- The letter `(j + 1, j)` of `α U` is the matrix whose only nonzero column is the column `j`,
with entries `α ω^{l j}`. -/
theorem toMPSTensor_normUTensor (j : Fin 3) :
    (normUTensor α).toMPSTensor (finProdFinEquiv (j + 1, j)) =
      Matrix.of fun l r ↦ if r = j then α * phaseChar (uWeight l j) else 0 := by
  ext l r
  rw [toMPSTensor_finProdFinEquiv]
  simp [normUTensor, uTensor, clockTensor_apply]

/-- The letter `(j + 2, j)` of `α² ω V` is the matrix whose only nonzero column is the column
`j`, with entries `α² ω ω^{2 l j + 2 j}`. -/
theorem toMPSTensor_normVTensor (j : Fin 3) :
    (normVTensor α).toMPSTensor (finProdFinEquiv (j + 2, j)) =
      Matrix.of fun l r ↦ if r = j then α ^ 2 * omega * phaseChar (vWeight l j) else 0 := by
  ext l r
  rw [toMPSTensor_finProdFinEquiv]
  simp [normVTensor, vTensor, clockTensor_apply]

/-- **`α U` is normal**: its letters `(j + 1, j)` carry the columns of the invertible matrix
`(α ω^{l j})`. -/
theorem normUTensor_isNormal (hα : α ^ 3 = omega) : Kraus.IsNormal (normUTensor α).toMPSTensor := by
  have hα0 := ne_zero_of_pow_three_eq_omega hα
  refine isNormal_of_forced_column (fun j ↦ finProdFinEquiv (j + 1, j))
    (fun j l ↦ α * phaseChar (uWeight l j)) toMPSTensor_normUTensor
    (fun _ _ ↦ mul_ne_zero hα0 (phaseChar_ne_zero _)) ?_
  simpa only [uWeight, phaseChar_mul] using
    det_scaled_vandermonde_ne_zero phaseChar_injective fun _ ↦ hα0

/-- **`α² ω V` is normal**: its letters `(j + 2, j)` carry the columns of the invertible matrix
`(α² ω ω^{2 l j + 2 j})`. -/
theorem normVTensor_isNormal (hα : α ^ 3 = omega) : Kraus.IsNormal (normVTensor α).toMPSTensor := by
  have hα0 := ne_zero_of_pow_three_eq_omega hα
  have hc : α ^ 2 * omega ≠ 0 := mul_ne_zero (pow_ne_zero _ hα0) omega_ne_zero
  refine isNormal_of_forced_column (fun j ↦ finProdFinEquiv (j + 2, j))
    (fun j l ↦ α ^ 2 * omega * phaseChar (vWeight l j)) toMPSTensor_normVTensor
    (fun _ _ ↦ mul_ne_zero hc (phaseChar_ne_zero _)) ?_
  have hv : ∀ l j : Fin 3, α ^ 2 * omega * phaseChar (vWeight l j) =
      (α ^ 2 * omega * phaseChar (2 * j)) * phaseChar (2 * j) ^ (l : ℕ) := by
    intro l j
    rw [vWeight, show 2 * l * j + 2 * j = l * (2 * j) + 2 * j by revert l j; decide,
      AddChar.map_add_eq_mul, phaseChar_mul l (2 * j)]
    ring
  simp only [hv]
  exact det_scaled_vandermonde_ne_zero
    (phaseChar_injective.comp (by decide : Function.Injective fun j : Fin 3 ↦ 2 * j))
    fun _ ↦ mul_ne_zero hc (phaseChar_ne_zero _)

/-- **The rescaled clock family is an exact representation of `ℤ₃` with normal tensors**, for
every cube root `α` of `ω`: the identity tensor of bond dimension one, `α U` and `α² ω V` are
normal, and their periodic operators multiply as `ℤ₃` on every nonempty chain.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 1684 (the representation law);
the tensors are those of `Z3ClockTensor`, rescaled. -/
theorem clockFamily_isNormalRepresentation (hα : α ^ 3 = omega) :
    (clockFamily α).IsNormalRepresentation where
  isNormal := Multiplicative.forall_zmod_three (idTensor_isNormal (d := 3))
    (normUTensor_isNormal hα) (normVTensor_isNormal hα)
  operator_mul g h _ hN :=
    mpo_clockRepTensor_mul hα hN (Multiplicative.toAdd g) (Multiplicative.toAdd h)

/-! ### The invariant state -/

/-- The exponent table `p` of the invariant state. -/
def clockExponent : Fin 3 → Fin 3 → Fin 3 := ![![0, 0, 1], ![0, 0, 0], ![1, 0, 1]]

/-- The single-site function `k` whose difference `k(s_k) − k(s_{k+1})` telescopes. -/
def clockGauge : Fin 3 → Fin 3 := ![0, 0, 2]

/-- The carry of `s ↦ s + 1` at `s = 2`. -/
def clockCarry : Fin 3 → Fin 3 := ![0, 0, 1]

/-- The bond amplitude `α^s ω^{p(l, s)}` of the invariant state. -/
def clockAmplitude (α : ℂ) (l s : Fin 3) : ℂ := α ^ (s : ℕ) * phaseChar (clockExponent l s)

/-- **The invariant state**: the bond-three tensor whose letter `s` has the single nonzero
column `s`, with entries `α^s ω^{p(l, s)}`. -/
def clockState (α : ℂ) : MPSTensor 3 3 :=
  fun s ↦ Matrix.of fun l r ↦ if r = s then clockAmplitude α l s else 0

/-- The amplitude of the invariant state is the product of the bond amplitudes around the
ring. -/
theorem mpv_clockState (σ : Fin N → Fin 3) :
    mpv (clockState α) σ = ∏ n, clockAmplitude α (σ n) (σ (n + 1)) :=
  mpv_of_forced_right_bond (β := id) (φ := fun s l ↦ clockAmplitude α l s)
    (fun _ _ _ ↦ rfl) σ

theorem det_clockExponent :
    (Matrix.of fun l s : Fin 3 ↦ phaseChar (clockExponent l s)).det = 3 * omega := by
  rw [Matrix.det_fin_three]
  simp [clockExponent]
  linear_combination (-1 : ℂ) * omega_sq_add_omega_add_one

/-- **The invariant state is normal**: its columns are those of the invertible matrix
`(ω^{p(l, s)})` scaled by `α^s`. -/
theorem clockState_isNormal (hα : α ^ 3 = omega) : Kraus.IsNormal (clockState α) := by
  have hα0 := ne_zero_of_pow_three_eq_omega hα
  refine isNormal_of_forced_column id (fun s l ↦ clockAmplitude α l s) (fun _ ↦ rfl)
    (fun _ _ ↦ mul_ne_zero (pow_ne_zero _ hα0) (phaseChar_ne_zero _)) ?_
  have h : (Matrix.of fun l s : Fin 3 ↦ clockAmplitude α l s) =
      (Matrix.of fun l s : Fin 3 ↦ phaseChar (clockExponent l s)) *
        Matrix.diagonal fun s : Fin 3 ↦ α ^ (s : ℕ) := by
    ext l s
    simp [clockAmplitude, mul_comm]
  rw [h, Matrix.det_mul, det_clockExponent, Matrix.det_diagonal]
  exact mul_ne_zero (mul_ne_zero three_ne_zero omega_ne_zero)
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ hα0)

/-- The shift `s ↦ s + 1` multiplies `α^s` by `α`, up to the carry `α³ = ω` at `s = 2`. -/
theorem pow_val_add_one (hα : α ^ 3 = omega) (y : Fin 3) :
    α ^ ((y + 1 : Fin 3) : ℕ) = α * α ^ (y : ℕ) * phaseChar (-clockCarry y) := by
  fin_cases y
  · simp [clockCarry]
  · simp [clockCarry, sq]
  · change α ^ ((2 + 1 : Fin 3) : ℕ) = α * α ^ ((2 : Fin 3) : ℕ) * phaseChar (-clockCarry 2)
    rw [show clockCarry 2 = 1 from rfl, show (-1 : Fin 3) = 2 from rfl, phaseChar_two,
      show ((2 + 1 : Fin 3) : ℕ) = 0 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_zero,
      show α * α ^ 2 * omega ^ 2 = α ^ 3 * omega ^ 2 by ring, hα, ← pow_succ',
      omega_pow_three]

/-- **The bond amplitude under the shift**: `a(x + 1, y + 1) = α ω^{x y + k(x) − k(y)} a(x, y)`.
The controlled phase `ω^{x y}` of `U` is produced by the shift of the exponent table up to the
telescoping term `k(x) − k(y)`. -/
theorem clockAmplitude_add_one (hα : α ^ 3 = omega) (x y : Fin 3) :
    clockAmplitude α (x + 1) (y + 1) =
      α * phaseChar (uWeight x y + clockGauge x - clockGauge y) * clockAmplitude α x y := by
  have hexp : -clockCarry y + clockExponent (x + 1) (y + 1) =
      uWeight x y + clockGauge x - clockGauge y + clockExponent x y := by
    revert x y
    decide
  rw [clockAmplitude, clockAmplitude, pow_val_add_one hα, mul_assoc (α * _),
    ← AddChar.map_add_eq_mul, hexp, AddChar.map_add_eq_mul]
  ring

/-- **`α U` fixes the invariant state** on every nonempty periodic chain. -/
theorem fixesMPV_normUTensor (hα : α ^ 3 = omega) :
    GroupFamily.FixesMPV (normUTensor α) (clockState α) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  rw [mpo_normUTensor, uTensor, mpo_clockTensor, Matrix.smul_monomial,
    Matrix.monomial_mulVec_eq_self_iff]
  intro t
  have hk : ∑ n, clockGauge (t (n + 1)) = ∑ n, clockGauge (t n) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl
  simp only [mpv_clockState, clockShift_apply, clockAmplitude_add_one hα,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Pi.smul_apply, smul_eq_mul, clockPhase, ← phaseChar_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hk, add_sub_cancel_right]

/-- **Every operator of the rescaled clock family fixes the invariant state** on every nonempty
periodic chain. -/
theorem fixesMPV_clockState (hα : α ^ 3 = omega) :
    ∀ g, GroupFamily.FixesMPV ((clockFamily α).tensor g) (clockState α) := by
  refine Multiplicative.forall_zmod_three ?_ (fixesMPV_normUTensor hα) ?_
  · intro N _
    change mpo (idTensor 3) N *ᵥ _ = _
    rw [mpo_idTensor, Matrix.one_mulVec]
  · intro N hN
    have : NeZero N := ⟨by omega⟩
    change mpo (normVTensor α) N *ᵥ _ = _
    rw [← mpo_normU_mul_normU, ← Matrix.mulVec_mulVec, fixesMPV_normUTensor hα N hN,
      fixesMPV_normUTensor hα N hN]

/-! ### The anomaly class -/

/-- **The clock symmetry is not anomalous**: for every cube root `α` of `ω` and every choice of
fusion tensors of the rescaled clock family, the anomaly three-cocycle has trivial gauge class.

Source: arXiv:2502.20257, `main.tex` line 1545 (an invariant normal state forces a trivial
anomaly); arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040 (the class `ω_0`). -/
theorem isTrivialGaugeClass_omega_clockFamily (hα : α ^ 3 = omega)
    (fd : (clockFamily α).FusionData) : ScalarThreeCochain.IsTrivialGaugeClass fd.omega :=
  (clockFamily_isNormalRepresentation hα).isTrivialGaugeClass_omega_of_invariant fd
    (clockState_isNormal hα) (by norm_num) (fixesMPV_clockState hα)

/-- **The Else–Nayak class of the clock symmetry vanishes**: the anomaly class of the rescaled
clock family in the degree-three group cohomology `H³(ℤ₃, ℂˣ)` is zero.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040 (`j = 0`); arXiv:2502.20257,
`main.tex` line 1545. -/
theorem clockFamily_anomalyClass_eq_zero (hα : α ^ 3 = omega) :
    (clockFamily_isNormalRepresentation hα).anomalyClass = 0 := by
  obtain ⟨fd⟩ := (clockFamily_isNormalRepresentation hα).nonempty_fusionData
  exact (GroupFamily.FusionData.isTrivialGaugeClass_omega_iff _ fd).1
    (isTrivialGaugeClass_omega_clockFamily hα fd)

/-- **The gauge-invariant product of the clock symmetry is one**: for every choice of fusion
tensors, `ω(g,1,g) ω(g,g,g) ω(g,g²,g) = 1` at the generator `g`, against the value `ω₃²` of
the anomalous representation `{1, U, U†}`.

Source: arXiv:2502.20257, `eq:omegagauge`; arXiv:2405.00439, line 2040. -/
theorem cyclicInvariant_omega_clockFamily (hα : α ^ 3 = omega)
    (fd : (clockFamily α).FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd 1) 3 = 1 :=
  ScalarThreeCochain.cyclicInvariant_eq_one_of_isTrivialGaugeClass
    (isTrivialGaugeClass_omega_clockFamily hα fd) (by decide)

/-- The cube root `exp(2πi/9)` of `ω` gives an exact representation whose anomaly class
vanishes. -/
theorem clockFamily_clockAlpha_anomalyClass_eq_zero :
    (clockFamily_isNormalRepresentation clockAlpha_pow_three).anomalyClass = 0 :=
  clockFamily_anomalyClass_eq_zero clockAlpha_pow_three

end Z3Clock
