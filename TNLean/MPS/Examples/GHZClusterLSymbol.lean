/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCommPhase
import TNLean.Algebra.LSymbolActionMatrix
import TNLean.Algebra.StabilizerBlockIndependence
import TNLean.MPS.Examples.GHZClusterAction

/-!
# L-symbols of the `ℤ₄ × ℤ₂` GHZ–cluster state and the failure of block independence

arXiv:2502.20257, `example:z4z2` (`Papers/2502.20257/main.tex`, lines 4340–4496), considers the
GHZ state tensored with the once-blocked cluster state, a matrix product state with two injective
blocks `A_0`, `A_1`, under the onsite symmetry `G = ℤ₄ × ℤ₂`. An element `g = (a, b)` sends the
block `x` to the block `g • x = x + a (mod 2)`, and on each block it acts on the virtual level:

`u_g · A_x = S_{g,x}† A_{g • x} S_{g,x}`

(lines 4348–4362), with the action tensors `S_{g,x} = A^Γ_{g,x}` of the table at lines
4482–4487 (`z4z2GHZClusterVirtual`). These are the source's normalized action tensors: the table
fixes their scalar freedom, and `S_{1,x} = 1`. They satisfy

`S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}`

(line 4366) for the L-symbols `Lˣ_{g,h}`, which take values in `{±1, ±i}` (line 4495). Every
action tensor is a Pauli word `i^{αβ} X^α Z^β` (`z4z2ActionMatrix_eq_pauliWord`), so the
L-symbols are read off from the multiplication of Pauli words (`z4z2LSymbol`).

The unbroken subgroup, the stabilizer of the block `0`, is `H = ⟨(2,0), (0,1)⟩ ≅ ℤ₂ × ℤ₂`. The
L-symbol of the block `0` restricted to `H` is a two-cocycle `ψ` (`z4z2StabilizerCocycle`). Its
class is nontrivial, since the action tensors `X` and `Z` of the two generators anticommute
(lines 4489–4490). It does not extend to `G` (line 4385): for every two-cocycle `Ψ` of the
commutative group `G`, the commutator phase is a bicharacter, so with `u = (1,0)`, `v = (0,1)`,

`c_Ψ(u², v) = c_Ψ(u, v)² = c_Ψ(u, v²) = c_Ψ(u, 1) = 1`,

while `c_ψ(u², v) = -1`. By the converse direction of `prop:BI_psi` (lines 7042–7064), the
L-symbols are not block independent (line 4490). The modified fusion operators and the
state-level gauging that follow in the source are not treated here.

**Scope restriction (scalar L-symbols):** block independence is the scalar condition
`TNLean.Algebra.LSymbol.IsBlockIndependent` on the L-symbol computed from the action tensors, with
`ℂˣ` coefficients, as in `TNLean.Algebra.StabilizerBlockIndependence`; see
`docs/paper-gaps/fbc25_mpu_action_stabilizer_source_audit.tex`.

## Main definitions

* `MPSTensor.z4z2ActionMatrix`: the action tensors `S_{g,x}`.
* `MPSTensor.z4z2PauliWord`: the Pauli word `i^{αβ} X^α Z^β`.
* `MPSTensor.z4z2LSymbol`: the L-symbols.
* `MPSTensor.z4z2StabilizerCocycle`: the stabilizer cocycle `ψ` on the unbroken subgroup.

## Main results

* `MPSTensor.twistedTensor_z4z2GHZClusterBlock`: `u_g · A_x = S_{g,x}† A_{g • x} S_{g,x}`.
* `MPSTensor.z4z2ActionMatrix_mul`: `S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}`.
* `MPSTensor.z4z2LSymbol_isCompatible`, `MPSTensor.z4z2LSymbol_isNormalized`: the L-symbols
  are compatible with the trivial three-cocycle and normalized.
* `MPSTensor.z4z2LSymbol_pow_four`: the L-symbols are fourth roots of unity.
* `MPSTensor.z4z2StabilizerCocycle_H2π_ne_zero`: the stabilizer class is nontrivial.
* `MPSTensor.z4z2StabilizerCocycle_not_extends`,
  `MPSTensor.z4z2StabilizerCocycle_H2π_not_mem_range`: it does not extend to `ℤ₄ × ℤ₂`.
* `MPSTensor.z4z2LSymbol_not_isBlockIndependent`: block independence fails.
-/

open scoped Matrix TNLean.Algebra.ScalarCohomology
open Matrix TNLean.Algebra

namespace MPSTensor

/-! ### The action on the blocks -/

/-- The action of `ℤ₄ × ℤ₂` on the two block labels: `(a, b) • x = x + a (mod 2)`
(arXiv:2502.20257, `example:z4z2`, lines 4481–4489). -/
instance z4z2GHZClusterBlockMulAction : MulAction (Multiplicative (ZMod 4 × ZMod 2)) (Fin 2) where
  smul g x := z4z2GHZClusterBlockAction g.toAdd x
  one_smul := by decide
  mul_smul := by decide

theorem z4z2_smul_def (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    g • x = z4z2GHZClusterBlockAction g.toAdd x := rfl

/-- The action tensor `S_{g,x} = A^Γ_{g,x}` of arXiv:2502.20257, lines 4482–4487. -/
noncomputable def z4z2ActionMatrix (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  z4z2GHZClusterVirtual g.toAdd x

/-- **The onsite symmetry moves to the virtual level** in the source's convention:
`u_g · A_x = S_{g,x}† A_{g • x} S_{g,x}` (arXiv:2502.20257, `example:z4z2`, lines 4348–4362,
with the action tensors of lines 4482–4487). -/
theorem twistedTensor_z4z2GHZClusterBlock (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2)
    (i : Fin 8) :
    twistedTensor (z4z2GHZClusterBlock x) z4z2GHZClusterAction g i =
      (z4z2ActionMatrix g x)ᴴ * z4z2GHZClusterBlock (g • x) i * z4z2ActionMatrix g x := by
  rw [z4z2GHZClusterBlock_covariance, z4z2ActionMatrix, z4z2GHZClusterVirtual_adjoint]
  rfl

/-- **The action tensors of the identity are trivial**, `S_{1,x} = 1`. -/
theorem z4z2ActionMatrix_one (x : Fin 2) : z4z2ActionMatrix 1 x = 1 := by
  fin_cases x <;> rfl

/-- Every action tensor is unitary. -/
theorem z4z2ActionMatrix_mul_conjTranspose (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    z4z2ActionMatrix g x * (z4z2ActionMatrix g x)ᴴ = 1 := by
  rw [z4z2ActionMatrix, z4z2GHZClusterVirtual_adjoint, z4z2GHZClusterVirtual_sq]

theorem z4z2ActionMatrix_ne_zero (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    z4z2ActionMatrix g x ≠ 0 := by
  intro h
  have := z4z2ActionMatrix_mul_conjTranspose g x
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

/-! ### Pauli words -/

/-- The Pauli word `i^{αβ} X^α Z^β`. The four words are `1`, `X`, `Z` and `Y = i X Z`. -/
noncomputable def z4z2PauliWord (α β : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I ^ (α.val * β.val) • (pauliX ^ α.val * pauliZ ^ β.val)

/-- The `X` exponent of the action tensor `S_{(a,b),x}`; the `Z` exponent is `b`. -/
def z4z2XCode (a : ZMod 4) (x : Fin 2) : ZMod 2 := ![![0, 1, 1, 0], ![0, 0, 1, 1]] x a

/-- The power of `i` in the product of two Pauli words:
`i^{αβ + α'β' + 2βα' - (α+α')(β+β')}`, written with nonnegative exponents. -/
def z4z2PauliPhase (α β α' β' : ZMod 2) : ℕ :=
  α.val * β.val + α'.val * β'.val + 2 * (β.val * α'.val) + 3 * ((α + α').val * (β + β').val)

private theorem pauliX_eq : pauliX = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

private theorem one_add_one_two : (1 + 1 : ZMod 2) = 0 := rfl

/-- Every action tensor is a Pauli word. -/
theorem z4z2ActionMatrix_eq_pauliWord (g : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    z4z2ActionMatrix g x = z4z2PauliWord (z4z2XCode g.toAdd.1 x) g.toAdd.2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = g := ⟨g.toAdd, rfl⟩
  rcases zmod_two_cases b with rfl | rfl <;> fin_cases a <;> fin_cases x <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4z2ActionMatrix, z4z2GHZClusterVirtual, z4z2PauliWord, z4z2XCode,
        z4z2GHZClusterPauliY, pauliX_eq, pauliZ, val_one_two])

/-- **The multiplication of Pauli words**:
`(i^{αβ} X^α Z^β)(i^{α'β'} X^{α'} Z^{β'}) = i^{e} · i^{(α+α')(β+β')} X^{α+α'} Z^{β+β'}`, with
the phase exponent `e = z4z2PauliPhase α β α' β'`. -/
theorem z4z2PauliWord_mul (α β α' β' : ZMod 2) :
    z4z2PauliWord α β * z4z2PauliWord α' β' =
      Complex.I ^ z4z2PauliPhase α β α' β' • z4z2PauliWord (α + α') (β + β') := by
  rcases zmod_two_cases α with rfl | rfl <;> rcases zmod_two_cases β with rfl | rfl <;>
    rcases zmod_two_cases α' with rfl | rfl <;> rcases zmod_two_cases β' with rfl | rfl <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4z2PauliWord, z4z2PauliPhase, pauliX_eq, pauliZ, val_one_two,
        one_add_one_two, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, Complex.I_mul_I])

/-- The `X` exponents of the action tensors are additive along the action:
`α(gh, x) = α(g, h • x) + α(h, x)`. -/
theorem z4z2XCode_mul (g h : Multiplicative (ZMod 4 × ZMod 2)) (x : Fin 2) :
    z4z2XCode (g * h).toAdd.1 x = z4z2XCode g.toAdd.1 (h • x) + z4z2XCode h.toAdd.1 x := by
  revert g h x
  decide

/-! ### The L-symbols -/

/-- The unit `i` of `ℂ`. -/
noncomputable def z4z2IUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

/-- **The L-symbols** `Lˣ_{g,h}` of the GHZ–cluster state, the phases in
`S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}` (arXiv:2502.20257, line 4366). -/
noncomputable def z4z2LSymbol : LSymbol (Multiplicative (ZMod 4 × ZMod 2)) (Fin 2) :=
  fun x g h ↦ z4z2IUnit ^ z4z2PauliPhase (z4z2XCode g.toAdd.1 (h • x)) g.toAdd.2
    (z4z2XCode h.toAdd.1 x) h.toAdd.2

theorem coe_z4z2LSymbol (x : Fin 2) (g h : Multiplicative (ZMod 4 × ZMod 2)) :
    (z4z2LSymbol x g h : ℂ) = Complex.I ^ z4z2PauliPhase (z4z2XCode g.toAdd.1 (h • x)) g.toAdd.2
      (z4z2XCode h.toAdd.1 x) h.toAdd.2 := by
  simp [z4z2LSymbol, z4z2IUnit]

/-- **The defining relation of the L-symbols**: `S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}`
(arXiv:2502.20257, `example:z4z2`, line 4366). -/
theorem z4z2ActionMatrix_mul (x : Fin 2) (g h : Multiplicative (ZMod 4 × ZMod 2)) :
    z4z2ActionMatrix g (h • x) * z4z2ActionMatrix h x =
      (z4z2LSymbol x g h : ℂ) • z4z2ActionMatrix (g * h) x := by
  rw [z4z2ActionMatrix_eq_pauliWord, z4z2ActionMatrix_eq_pauliWord, z4z2PauliWord_mul,
    coe_z4z2LSymbol, z4z2ActionMatrix_eq_pauliWord, z4z2XCode_mul, toAdd_mul]
  rfl

/-- **The L-symbols are compatible with the trivial three-cocycle**: the onsite symmetry is not
anomalous (arXiv:2502.20257, lines 4489–4490). -/
theorem z4z2LSymbol_isCompatible : LSymbol.IsCompatible z4z2LSymbol (fun _ _ _ ↦ 1) :=
  LSymbol.isCompatible_one_of_mul_eq_smul z4z2ActionMatrix_ne_zero z4z2ActionMatrix_mul

/-- **The L-symbols are normalized**, `Lˣ_{g,1} = Lˣ_{1,g} = 1` (arXiv:2502.20257,
`eq:triv_Ls`). -/
theorem z4z2LSymbol_isNormalized : LSymbol.IsNormalized z4z2LSymbol :=
  LSymbol.isNormalized_of_mul_eq_smul z4z2ActionMatrix_ne_zero z4z2ActionMatrix_one
    z4z2ActionMatrix_mul

/-- **The L-symbols take values in `{±1, ±i}`** (arXiv:2502.20257, line 4495). -/
theorem z4z2LSymbol_pow_four (x : Fin 2) (g h : Multiplicative (ZMod 4 × ZMod 2)) :
    z4z2LSymbol x g h ^ 4 = 1 := by
  have hI : z4z2IUnit ^ 4 = 1 := Units.ext (by simp [z4z2IUnit, Complex.I_pow_four])
  rw [z4z2LSymbol, ← pow_mul, mul_comm, pow_mul, hI, one_pow]

/-- The generator `u = (1, 0)` of `ℤ₄`. -/
def z4z2U : Multiplicative (ZMod 4 × ZMod 2) := .ofAdd (1, 0)

/-- The generator `v = (0, 1)` of `ℤ₂`. -/
def z4z2V : Multiplicative (ZMod 4 × ZMod 2) := .ofAdd (0, 1)

/-- The L-symbols at the generators of the unbroken subgroup: `L⁰_{u²,v} = -i` and
`L⁰_{v,u²} = i`, since `X Z = -i Y` and `Z X = i Y`. -/
theorem z4z2LSymbol_zero_sq_v :
    (z4z2LSymbol 0 (z4z2U ^ 2) z4z2V : ℂ) = -Complex.I ∧
      (z4z2LSymbol 0 z4z2V (z4z2U ^ 2) : ℂ) = Complex.I := by
  have h1 : z4z2PauliPhase (z4z2XCode (z4z2U ^ 2).toAdd.1 (z4z2V • 0)) (z4z2U ^ 2).toAdd.2
      (z4z2XCode z4z2V.toAdd.1 0) z4z2V.toAdd.2 = 3 := by decide
  have h2 : z4z2PauliPhase (z4z2XCode z4z2V.toAdd.1 ((z4z2U ^ 2) • 0)) z4z2V.toAdd.2
      (z4z2XCode (z4z2U ^ 2).toAdd.1 0) (z4z2U ^ 2).toAdd.2 = 5 := by decide
  rw [coe_z4z2LSymbol, coe_z4z2LSymbol, h1, h2]
  exact ⟨by linear_combination Complex.I * Complex.I_sq,
    by linear_combination (Complex.I ^ 3 - Complex.I) * Complex.I_sq⟩

/-! ### The stabilizer cocycle -/

/-- The unbroken subgroup `H = ⟨(2,0), (0,1)⟩`, the stabilizer of the block `0`. -/
abbrev z4z2Unbroken : Subgroup (Multiplicative (ZMod 4 × ZMod 2)) :=
    MulAction.stabilizer (Multiplicative (ZMod 4 × ZMod 2)) (0 : Fin 2)

/-- **The stabilizer cocycle** `ψ(a, b) = L⁰_{a,b}` on the unbroken subgroup
(arXiv:2502.20257, lines 4489–4490). -/
noncomputable def z4z2StabilizerCocycle : ScalarCocycle z4z2Unbroken :=
  fun p ↦ z4z2LSymbol 0 p.1 p.2

/-- The stabilizer cocycle is a two-cocycle: the compatibility of the L-symbols restricted to
the block `0` and the unbroken subgroup. -/
theorem z4z2StabilizerCocycle_isMulCocycle₂ :
    groupCohomology.IsMulCocycle₂ z4z2StabilizerCocycle := by
  refine (isMulCocycle₂_iff _).mpr fun a b c ↦ ?_
  have h := z4z2LSymbol_isCompatible 0 a b c
  rw [MulAction.mem_stabilizer_iff.mp c.property, one_mul] at h
  exact h.symm

private theorem u_sq_mem : z4z2U ^ 2 ∈ z4z2Unbroken := MulAction.mem_stabilizer_iff.mpr (by decide)

private theorem v_mem : z4z2V ∈ z4z2Unbroken := MulAction.mem_stabilizer_iff.mpr (by decide)

private theorem commPhase_stabilizerCocycle :
    ScalarCocycle.commPhase z4z2StabilizerCocycle ⟨z4z2U ^ 2, u_sq_mem⟩ ⟨z4z2V, v_mem⟩ = -1 := by
  apply Units.ext
  simp only [ScalarCocycle.commPhase, z4z2StabilizerCocycle, Units.val_mul, Units.val_neg,
    Units.val_one, Units.val_inv_eq_inv_val, z4z2LSymbol_zero_sq_v.1, z4z2LSymbol_zero_sq_v.2]
  field_simp

private theorem units_neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := fun h ↦ by
  have := congrArg Units.val h
  norm_num at this

/-- **The stabilizer class is nontrivial**: the class of `ψ` in `H²(H, ℂˣ)` is not zero, since
the action tensors `X` of `(2,0)` and `Z` of `(0,1)` anticommute (arXiv:2502.20257,
lines 4489–4490). -/
theorem z4z2StabilizerCocycle_H2π_ne_zero :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      z4z2StabilizerCocycle_isMulCocycle₂) ≠ 0 :=
  ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one _ (mul_comm _ _)
    (by rw [commPhase_stabilizerCocycle]; exact units_neg_one_ne_one)

/-- **No two-cocycle of `ℤ₄ × ℤ₂` has a commutator phase other than one at `(u², v)`**: the
commutator phase is a bicharacter of the commutative group, so `c(u², v) = c(u, v²) = 1`. -/
theorem commPhase_z4z2U_sq_z4z2V {Ψ : ScalarCocycle (Multiplicative (ZMod 4 × ZMod 2))}
    (hΨ : groupCohomology.IsMulCocycle₂ Ψ) :
    ScalarCocycle.commPhase Ψ (z4z2U ^ 2) z4z2V = 1 := by
  rw [ScalarCocycle.commPhase_pow_left hΨ (mul_comm _ _), sq,
    ← ScalarCocycle.commPhase_mul_right hΨ (mul_comm _ _) (mul_comm _ _),
    show z4z2V * z4z2V = 1 by decide, ScalarCocycle.commPhase_one_right hΨ]

/-- **The stabilizer cocycle does not extend to `ℤ₄ × ℤ₂`**: no two-cocycle of the whole group
restricts to `ψ` on the unbroken subgroup (arXiv:2502.20257, line 4385, citing Blanik,
Garre-Rubio and Schuch). -/
theorem z4z2StabilizerCocycle_not_extends :
    ¬ ∃ Ψ : ScalarCocycle (Multiplicative (ZMod 4 × ZMod 2)), groupCohomology.IsMulCocycle₂ Ψ ∧
      ∀ a b : z4z2Unbroken, Ψ ((a : _), (b : _)) = z4z2StabilizerCocycle (a, b) := by
  rintro ⟨Ψ, hΨ, hext⟩
  have h := commPhase_z4z2U_sq_z4z2V hΨ
  rw [ScalarCocycle.commPhase, hext ⟨_, u_sq_mem⟩ ⟨_, v_mem⟩, hext ⟨_, v_mem⟩ ⟨_, u_sq_mem⟩]
    at h
  have hc := commPhase_stabilizerCocycle
  rw [ScalarCocycle.commPhase] at hc
  exact units_neg_one_ne_one (hc.symm.trans h)

/-- **The stabilizer class is not a restriction**: the class of `ψ` is not in the image of the
restriction map `H²(ℤ₄ × ℤ₂, ℂˣ) → H²(H, ℂˣ)` (arXiv:2502.20257, line 4385). -/
theorem z4z2StabilizerCocycle_H2π_not_mem_range :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
        z4z2StabilizerCocycle_isMulCocycle₂) ∉
      Set.range (groupCohomology.map z4z2Unbroken.subtype
        (scalarRepresentationRes z4z2Unbroken.subtype) 2) := by
  rw [ScalarCocycle.H2π_mem_range_map_subtype_iff]
  exact z4z2StabilizerCocycle_not_extends

/-- **Block independence fails** for the GHZ–cluster state: no joint scalar gauge makes the
factors `ellˣ_{a,b;g}` independent of the block. By the converse direction of `prop:BI_psi`,
block independence would extend the stabilizer cocycle to `ℤ₄ × ℤ₂`
(arXiv:2502.20257, `example:z4z2`, lines 4383–4386 and 4490; `prop:BI_psi`,
lines 7042–7064). -/
theorem z4z2LSymbol_not_isBlockIndependent : ¬ LSymbol.IsBlockIndependent z4z2LSymbol := by
  intro hBI
  obtain ⟨Ψ, hΨ, hext⟩ :=
    LSymbol.exists_extension_of_isBlockIndependent 0 z4z2LSymbol_isCompatible hBI
  exact z4z2StabilizerCocycle_not_extends ⟨Ψ, hΨ, hext⟩

end MPSTensor
