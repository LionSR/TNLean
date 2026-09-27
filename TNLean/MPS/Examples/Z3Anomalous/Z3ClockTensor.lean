/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPU.GroupCocycleMPO.Instances

/-!
# Non-anomalous `ℤ₃` clock symmetry: the tensors `U` and `V` and their operator laws

**Source.** Construction of this development; no source prints the `ℤ₃` clock tensors below.
Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection "Periodic boundary
condition case", `Papers/2203.12563/REsubmission.tex` lines 2202–2224: from a three-cocycle `ω`
of a finite group `G`, the periodic operators `U_g = ⨂_i (L_g^i ⊗ L_g^{i+1}) · W_g^{i,i+1}`
form a representation of `G` (for the nontrivial cocycle of `ℤ₂`, line 2224 prints
`U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`). Garre-Rubio, Schuch 2024 (arXiv:2405.00439), subsection
"Example: `G = ℤ_n` with fully symmetry breaking", `Papers/2405.00439/MPU-DW.tex` lines
2038–2040: the three-cocycles `ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with
`j = 0` the trivial class.

**Formalized here.** On a periodic chain of `N ≥ 1` qutrits, with `X |s⟩ = |s + 1⟩`,
`CZ |a, b⟩ = ω^{ab} |a, b⟩` and `ω = exp(2πi/3)`, the clock operator
`U = X^{⊗N} ∏_k CZ_{k,k+1}` and the operator `V = X^{2 ⊗ N} ∏_k CZ²_{k,k+1} Z²_k` are periodic
matrix product unitaries of bond dimension three, with kernels
`⟨s|U|t⟩ = ∏_k δ_{s_k, t_k + 1} ω^{t_k t_{k+1}}` and
`⟨s|V|t⟩ = ∏_k δ_{s_k, t_k + 2} ω^{2 t_k t_{k+1} + 2 t_{k+1}}`. They multiply with a phase per
site:
`U² = ω^N V`, `U V = V U = ω^N`, `V² = U`, `U³ = ω^{2N}`.
So `{1, U, V}` represents `ℤ₃` only up to the length-dependent phases `ω^N`, which are
trivial when `3 ∣ N`.

Both tensors are the tensors of the construction of arXiv:2203.12563 for the trivial cocycle
`ω_0 = 1`, multiplied entrywise by the controlled-phase weight of the bond: at the level of
periodic operators, `U` is the operator `U_g` of `ω_0` for the generator `g`, the plain shift
`X^{⊗N}`, times the diagonal circuit `∏_k CZ_{k,k+1}`, and `V` is `U_{g²}` times
`∏_k CZ²_{k,k+1} Z²_k` (`mpo_clockTensor_eq_cocycle`). The operators `U_g` of `ω_0` alone form an
exact representation; the controlled-phase circuits produce the phases `ω^N`.

The symmetry is not anomalous: its Else–Nayak class is trivial. This is recorded, with the
cohomology computation, in the verification record below and is not formalized here.

## Main definitions

* `Z3Clock.omega`, `Z3Clock.phaseChar`: the cube root of unity `ω` and the character
  `a ↦ ω^a` of `ℤ₃`.
* `Z3Clock.clockTensor`: the monomial bond-three tensor with shift `g` and bond weight
  `ω^{f(l, j)}`.
* `Z3Clock.uTensor`, `Z3Clock.vTensor`: the clock tensors `U` and `V`.

## Main results

* `Z3Clock.mpo_clockTensor`: the periodic operator of a clock tensor is monomial.
* `Z3Clock.mpo_clockTensor_eq_cocycle`: the bridge to the construction of arXiv:2203.12563 with
  the trivial cocycle.
* `Z3Clock.mpo_u_mul_u`, `Z3Clock.mpo_u_mul_v`, `Z3Clock.mpo_v_mul_u`, `Z3Clock.mpo_v_mul_v`,
  `Z3Clock.mpo_u_mul_u_mul_u`: the multiplication table with the phases `ω^N`.
* `Z3Clock.clockTensor_isMPUPos`: every clock tensor is a matrix product unitary.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*

## Provenance
The tensors `U` and `V`, their kernels, their multiplication table and the triviality of the
anomaly class were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`,
§0, §1 and §3.0, and checked over `ℤ[ω]` by
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`; they are verification records, not
the source. The letters listed there are the letters `clockTensor g f i j` below, with the
output label `i` first.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Z3Clock

open MPOTensor TNLean.Algebra TNLean.Algebra.ScalarThreeCochain

/-! ### The phase character -/

/-- The primitive cube root of unity `ω = exp(2πi/3)`. -/
abbrev omega : ℂ := rootOfUnity 3

theorem omega_pow_three : omega ^ 3 = 1 := rootOfUnity_pow 3

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem omega_ne_one : omega ≠ 1 :=
  isPrimitiveRoot_omega.ne_one (by norm_num)

/-- The character `a ↦ ω^a` of `ℤ₃`, residues being represented by `Fin 3`. -/
def phaseChar : AddChar (Fin 3) ℂ where
  toFun a := omega ^ (a : ℕ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [Fin.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ omega_pow_three).symm

theorem phaseChar_apply (a : Fin 3) : phaseChar a = omega ^ (a : ℕ) := rfl

@[simp]
theorem phaseChar_one : phaseChar 1 = omega := by
  simp [phaseChar_apply]

theorem phaseChar_sum {ι : Type*} (s : Finset ι) (x : ι → Fin 3) :
    phaseChar (∑ i ∈ s, x i) = ∏ i ∈ s, phaseChar (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem norm_phaseChar (a : Fin 3) : ‖phaseChar a‖ = 1 := by
  rw [phaseChar_apply, norm_pow, isPrimitiveRoot_omega.norm'_eq_one (by norm_num), one_pow]

/-! ### Clock tensors -/

/-- The monomial bond-three tensor with shift `g` and bond weight `ω^{f(l, j)}`: the output is
the input `j` shifted by `g`, the outgoing bond carries `j`, and the incoming bond `l` (the input
of the previous site) contributes `ω^{f(l, j)}`. The first physical index is the output. -/
def clockTensor (g : Fin 3) (f : Fin 3 → Fin 3 → Fin 3) : MPOTensor 3 3 :=
  fun i j ↦ Matrix.of fun l r ↦ if i = j + g ∧ r = j then phaseChar (f l j) else 0

theorem clockTensor_apply (g : Fin 3) (f : Fin 3 → Fin 3 → Fin 3) (i j l r : Fin 3) :
    clockTensor g f i j l r = if i = j + g ∧ r = j then phaseChar (f l j) else 0 := rfl

/-- The global shift `X^{g ⊗ N}` of periodic qutrit configurations. -/
def clockShift (g : Fin 3) (N : ℕ) : Equiv.Perm (Fin N → Fin 3) :=
  Equiv.piCongrRight fun _ ↦ Equiv.addRight g

@[simp]
theorem clockShift_apply (g : Fin 3) {N : ℕ} (t : Fin N → Fin 3) (n : Fin N) :
    clockShift g N t n = t n + g := rfl

theorem clockShift_mul (g h : Fin 3) (N : ℕ) :
    clockShift g N * clockShift h N = clockShift (h + g) N := by
  ext t n
  simp [Equiv.Perm.mul_apply, add_assoc]

theorem clockShift_zero (N : ℕ) : clockShift 0 N = 1 := by
  ext t n
  simp

variable {N : ℕ} [NeZero N]

/-- The phase `ω^{∑_k f(t_k, t_{k+1})}` of the input configuration `t` around the periodic
chain. -/
def clockPhase (f : Fin 3 → Fin 3 → Fin 3) (t : Fin N → Fin 3) : ℂ :=
  phaseChar (∑ n, f (t n) (t (n + 1)))

/-- **The periodic operator of a clock tensor is monomial**: the shift by `g` with the phase
`ω^{∑_k f(t_k, t_{k+1})}` of the input configuration `t`. -/
theorem mpo_clockTensor (g : Fin 3) (f : Fin 3 → Fin 3 → Fin 3) :
    mpo (clockTensor g f) N = Matrix.monomial (clockShift g N) (clockPhase f) := by
  ext s t
  rw [mpo_apply_of_forced_right_bond (M := clockTensor g f) (π := (· + g)) (β := fun _ j ↦ j)
      (φ := fun _ j l ↦ phaseChar (f l j)) (clockTensor_apply g f),
    Matrix.monomial_apply, clockPhase, phaseChar_sum]
  rfl

/-- **Multiplication of clock operators**: if the bond weights satisfy
`f(a + h, b + h) + f'(a, b) = f''(a, b) + c + (k(a) − k(b))`, then the product of the clock
operators with shifts `g` and `h` is `ω^{c N}` times the clock operator with shift `h + g` and
weight `f''`; the term `k(a) − k(b)` telescopes around the chain. -/
theorem mpo_clockTensor_mul {g h gh c : Fin 3} {f f' f'' : Fin 3 → Fin 3 → Fin 3}
    (k : Fin 3 → Fin 3) (hgh : h + g = gh)
    (hf : ∀ a b, f (a + h) (b + h) + f' a b = f'' a b + c + (k a - k b)) :
    mpo (clockTensor g f) N * mpo (clockTensor h f') N =
      phaseChar c ^ N • mpo (clockTensor gh f'') N := by
  rw [mpo_clockTensor, mpo_clockTensor, mpo_clockTensor, Matrix.monomial_mul_monomial,
    clockShift_mul, hgh, Matrix.smul_monomial]
  congr 1
  funext t
  have hk : ∑ n, k (t (n + 1)) = ∑ n, k (t n) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl
  simp only [Pi.smul_apply, smul_eq_mul, clockPhase, clockShift_apply, ← AddChar.map_add_eq_mul,
    ← Finset.sum_add_distrib, hf]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, hk, sub_self,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, AddChar.map_add_eq_mul,
    AddChar.map_nsmul_eq_pow, mul_comm]

/-- The clock operator with no shift and no weight is the identity. -/
theorem mpo_clockTensor_zero : mpo (clockTensor 0 fun _ _ ↦ 0) N = 1 := by
  rw [mpo_clockTensor, clockShift_zero, ← Matrix.monomial_one]
  congr 1
  funext t
  simp [clockPhase]

/-! ### Unitarity -/

/-- Project result: **every clock tensor is a matrix product unitary** on every nonempty
periodic chain, its operator being a permutation times a unit-modulus phase. -/
theorem clockTensor_isMPUPos (g : Fin 3) (f : Fin 3 → Fin 3 → Fin 3) :
    IsMPUPos (clockTensor g f) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  rw [mpo_clockTensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [Complex.star_def, Complex.conj_mul', clockPhase, norm_phaseChar]
  norm_num

/-! ### The bridge to the trivial-cocycle construction -/

/-- Bridge: the shift of the construction of arXiv:2203.12563 on `ℤ₃`, with residues as
labels, is the clock shift. -/
theorem siteShift_residueEquiv (g : Multiplicative (ZMod 3)) (j : Fin 3) :
    GroupCocycle.siteShift (GroupCocycle.residueEquiv 2) g j = j + GroupCocycle.residueEquiv 2 g :=
  add_comm _ _

/-- Bridge: the global shift of the construction of arXiv:2203.12563 on `ℤ₃` is the clock
shift. -/
theorem shift_residueEquiv (g : Multiplicative (ZMod 3)) (N : ℕ) :
    GroupCocycle.shift (GroupCocycle.residueEquiv 2) g N =
      clockShift (GroupCocycle.residueEquiv 2 g) N := by
  ext t n
  exact congrArg Fin.val (siteShift_residueEquiv g (t n))

/-- The values of the trivial cocycle `ω_0` are one. -/
theorem cyclicCocycle_zero_val (a b c : Multiplicative (ZMod 3)) :
    (cyclicCocycle 3 0 a b c : ℂ) = 1 := by
  simp [cyclicCocycle_val]

/-- Bridge: **a clock tensor is the tensor of the trivial-cocycle construction times the bond
weight**. The tensor `T̂_g` of arXiv:2203.12563, lines 2206–2222, for the cocycle `ω_0 = 1` of
arXiv:2405.00439, line 2040, multiplied entrywise by `ω^{f(l, j)}`. -/
theorem clockTensor_apply_eq_cocycle (g : Multiplicative (ZMod 3))
    (f : Fin 3 → Fin 3 → Fin 3) (i j l r : Fin 3) :
    clockTensor (GroupCocycle.residueEquiv 2 g) f i j l r =
      GroupCocycle.tensor (GroupCocycle.residueEquiv 2) (cyclicCocycle 3 0) g i j l r *
        phaseChar (f l j) := by
  rw [clockTensor_apply, GroupCocycle.tensor_apply, siteShift_residueEquiv,
    cyclicCocycle_zero_val]
  split_ifs <;> simp

/-- Bridge: **a clock operator is the trivial-cocycle group operator times a diagonal
circuit**: `mpo (clockTensor g f) = U_g · diag(ω^{∑_k f(t_k, t_{k+1})})`, where `U_g` is the
periodic operator of arXiv:2203.12563, lines 2204–2222, for the cocycle `ω_0 = 1` of
arXiv:2405.00439, line 2040, namely the plain shift by `g`. -/
theorem mpo_clockTensor_eq_cocycle (g : Multiplicative (ZMod 3)) (f : Fin 3 → Fin 3 → Fin 3) :
    mpo (clockTensor (GroupCocycle.residueEquiv 2 g) f) N =
      mpo (GroupCocycle.tensor (GroupCocycle.residueEquiv 2) (cyclicCocycle 3 0) g) N *
        Matrix.diagonal (clockPhase f) := by
  rw [mpo_clockTensor, GroupCocycle.mpo_tensor, shift_residueEquiv]
  ext s t
  rw [Matrix.mul_diagonal, Matrix.monomial_apply, Matrix.monomial_apply]
  split_ifs
  · simp [GroupCocycle.phase, cyclicCocycle_zero_val]
  · simp

/-! ### The clock tensors `U` and `V` -/

/-- The bond weight `f(l, j) = l j` of `U`: the controlled phase `CZ` between neighbours. -/
def uWeight (l j : Fin 3) : Fin 3 := l * j

/-- The bond weight `f(l, j) = 2 l j + 2 j` of `V`: the controlled phase `CZ²` between
neighbours and the phase `Z²` on the site. -/
def vWeight (l j : Fin 3) : Fin 3 := 2 * l * j + 2 * j

/-- **The clock tensor `U`** of bond dimension three: the periodic operator is
`X^{⊗N} ∏_k CZ_{k,k+1}` (data file §3.0). -/
def uTensor : MPOTensor 3 3 := clockTensor 1 uWeight

/-- **The tensor `V`** of bond dimension three: the periodic operator is
`X^{2 ⊗ N} ∏_k CZ²_{k,k+1} Z²_k` (data file §3.0). -/
def vTensor : MPOTensor 3 3 := clockTensor 2 vWeight

/-- **The kernel of `U`**: `⟨s|U|t⟩ = ∏_k δ_{s_k, t_k + 1} ω^{t_k t_{k+1}}`. -/
theorem mpo_uTensor_apply (s t : Fin N → Fin 3) :
    mpo uTensor N s t = if s = fun n ↦ t n + 1 then ∏ n, omega ^ ((t n * t (n + 1) : Fin 3) : ℕ)
      else 0 := by
  rw [uTensor, mpo_clockTensor, Matrix.monomial_apply, clockPhase, phaseChar_sum]
  rfl

/-- **The kernel of `V`**: `⟨s|V|t⟩ = ∏_k δ_{s_k, t_k + 2} ω^{2 t_k t_{k+1} + 2 t_{k+1}}`. -/
theorem mpo_vTensor_apply (s t : Fin N → Fin 3) :
    mpo vTensor N s t = if s = fun n ↦ t n + 2 then
      ∏ n, omega ^ ((2 * t n * t (n + 1) + 2 * t (n + 1) : Fin 3) : ℕ) else 0 := by
  rw [vTensor, mpo_clockTensor, Matrix.monomial_apply, clockPhase, phaseChar_sum]
  rfl

/-- Bridge: **`U` is the generator of the trivial-cocycle construction dressed by `∏ CZ`**. -/
theorem mpo_uTensor_eq_cocycle :
    mpo uTensor N =
      mpo (GroupCocycle.tensor (GroupCocycle.residueEquiv 2) (cyclicCocycle 3 0)
          (Multiplicative.ofAdd 1)) N * Matrix.diagonal (clockPhase uWeight) :=
  mpo_clockTensor_eq_cocycle (Multiplicative.ofAdd 1) uWeight

/-- Bridge: **`V` is the square of the generator of the trivial-cocycle construction dressed by
`∏ CZ² Z²`**. -/
theorem mpo_vTensor_eq_cocycle :
    mpo vTensor N =
      mpo (GroupCocycle.tensor (GroupCocycle.residueEquiv 2) (cyclicCocycle 3 0)
          (Multiplicative.ofAdd 2)) N * Matrix.diagonal (clockPhase vWeight) :=
  mpo_clockTensor_eq_cocycle (Multiplicative.ofAdd 2) vWeight

/-! ### The multiplication table -/

/-- **`U² = ω^N V`** on every nonempty periodic chain (data file §3.0). -/
theorem mpo_u_mul_u : mpo uTensor N * mpo uTensor N = omega ^ N • mpo vTensor N := by
  simpa [uTensor, vTensor] using
    mpo_clockTensor_mul (N := N) (c := 1) (f'' := vWeight) id (by decide)
    (by decide : ∀ a b : Fin 3, uWeight (a + 1) (b + 1) + uWeight a b = vWeight a b + 1 + (a - b))

/-- **`U V = ω^N`** on every nonempty periodic chain (data file §3.0). -/
theorem mpo_u_mul_v : mpo uTensor N * mpo vTensor N = omega ^ N • (1 : Matrix _ _ ℂ) := by
  rw [← mpo_clockTensor_zero (N := N)]
  simpa [uTensor, vTensor] using
    mpo_clockTensor_mul (N := N) (c := 1) (f'' := fun _ _ ↦ 0) (2 * ·) (by decide)
    (by decide : ∀ a b : Fin 3, uWeight (a + 2) (b + 2) + vWeight a b = 0 + 1 + (2 * a - 2 * b))

/-- **`V U = ω^N`** on every nonempty periodic chain (data file §3.0). -/
theorem mpo_v_mul_u : mpo vTensor N * mpo uTensor N = omega ^ N • (1 : Matrix _ _ ℂ) := by
  rw [← mpo_clockTensor_zero (N := N)]
  simpa [uTensor, vTensor] using
    mpo_clockTensor_mul (N := N) (c := 1) (f'' := fun _ _ ↦ 0) (2 * ·) (by decide)
    (by decide : ∀ a b : Fin 3, vWeight (a + 1) (b + 1) + uWeight a b = 0 + 1 + (2 * a - 2 * b))

/-- **`V² = U`** on every nonempty periodic chain (data file §3.0). -/
theorem mpo_v_mul_v : mpo vTensor N * mpo vTensor N = mpo uTensor N := by
  simpa [uTensor, vTensor] using
    mpo_clockTensor_mul (N := N) (c := 0) (f'' := uWeight) id (by decide)
    (by decide : ∀ a b : Fin 3, vWeight (a + 2) (b + 2) + vWeight a b = uWeight a b + 0 + (a - b))

/-- **`U³ = ω^{2N}`** on every nonempty periodic chain (data file §3.0): `{1, U, V}` represents
`ℤ₃` only up to the phases `ω^N`. -/
theorem mpo_u_mul_u_mul_u :
    mpo uTensor N * mpo uTensor N * mpo uTensor N = omega ^ (2 * N) • (1 : Matrix _ _ ℂ) := by
  rw [mpo_u_mul_u, Matrix.smul_mul, mpo_v_mul_u, smul_smul, two_mul, pow_add]

end Z3Clock
