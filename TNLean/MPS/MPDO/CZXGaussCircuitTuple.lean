/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import TNLean.Algebra.GeneralizeDecide
import TNLean.Algebra.HypercubePhasePotential
import TNLean.Algebra.MonomialGaussOperator
import TNLean.MPS.Examples.ZMod2

/-!
# The displayed CZX circuit tuple and its local Gauss operator

The CZX model of FBC25 (arXiv:2502.20257, lines 4503--5183) is the anomalous
$\mathbb Z_2$ matrix product unitary acting on the GHZ state. After blocking,
one site carries two matter qubits, and the fusion operators on two neighboring
blocked sites are $\lambda^R_{e,e}=\lambda^R_{e,g}=\mathrm{id}$,
$\lambda^R_{g,e}=w_R$, and the modified fusion operator
$\tilde\lambda^R_{g,g}=\lambda^R_{g,g}Z_1$ introduced at the end of that
passage. Writing the displayed circuits in elementary-gate form, with the four
matter qubits of two neighboring blocked sites numbered $0,1,2,3$,

$w=(X_0X_1)\,\mathrm{CZ}_{01}\mathrm{CZ}_{12}\,(Z_2Z_3)$,
$\lambda=-i\,(X_0X_1X_2Z_3)\,\mathrm{CZ}_{01}\mathrm{CZ}_{12}\,X_2$,
$\tilde\lambda=\lambda Z_0$,

and the displayed circuit tuple is
$R^{\mathrm{CZX}}=(U_{0,0},U_{0,1},U_{1,0},U_{1,1})=(\mathrm{id},\mathrm{id},w,\tilde\lambda)$.

This file defines the elementary gates by their action on the computational
basis, proves the phase tables

$w\ket{x}=(-1)^{e(x)}\ket{\overline x}$,
$\tilde\lambda\ket{x}=-i(-1)^{f(x)}\ket{\overline x}$,

with $\overline x=(x_0+1,x_1+1,x_2,x_3)$,
$e(x)=x_0x_1+x_1x_2+x_2+x_3$, and $f(x)=x_0x_1+x_1x_2+x_0+x_1+x_3$,
and shows that the local Gauss operator of the tuple is the monomial operator
$G\ket{s}=i^{q(s)}\ket{\sigma(s)}$ with the phase table derived below.

The tuple is a tuple of matrices on the two-site matter space. Whether it
belongs to the full physical completion class of the CZX defect data is not
addressed here; that identification requires the three defect domains and maps
not supplied by the displayed matrices.
-/

noncomputable section

namespace MPOTensor.CZX

open Matrix Complex

/-! ### Elementary gates on four qubits -/

/-- The bit flip $x\mapsto x+e_r$ of qubit `r`. -/
def bitFlip (r : Fin 4) : Equiv.Perm (Fin 4 → ZMod 2) :=
  Equiv.addRight (Pi.single r 1)

/-- The Pauli $X$ gate on qubit `r`, $X_r\ket{x}=\ket{x+e_r}$. -/
def pauliX (r : Fin 4) : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  monomial (bitFlip r) fun _ ↦ 1

/-- The Pauli $Z$ gate on qubit `r`, $Z_r\ket{x}=(-1)^{x_r}\ket{x}$. -/
def pauliZ (r : Fin 4) : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  monomial 1 fun x ↦ (-1) ^ (x r).val

/-- The controlled-$Z$ gate on qubits `r` and `s`,
$\mathrm{CZ}_{rs}\ket{x}=(-1)^{x_rx_s}\ket{x}$. -/
def controlledZ (r s : Fin 4) : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  monomial 1 fun x ↦ (-1) ^ (x r * x s).val

/-- The fusion operator $w=(X_0X_1)\mathrm{CZ}_{01}\mathrm{CZ}_{12}(Z_2Z_3)$ of the CZX
model (arXiv:2502.20257, lines 4503--5183). Operator products act from right to
left. -/
def w : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  pauliX 0 * pauliX 1 * controlledZ 0 1 * controlledZ 1 2 * pauliZ 2 * pauliZ 3

/-- The fusion operator
$\lambda=-i(X_0X_1X_2Z_3)\mathrm{CZ}_{01}\mathrm{CZ}_{12}X_2$ of the CZX model
(arXiv:2502.20257, lines 4503--5183). -/
def lambda : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  (-I) • (pauliX 0 * pauliX 1 * pauliX 2 * pauliZ 3 * controlledZ 0 1 * controlledZ 1 2 *
    pauliX 2)

/-- The modified fusion operator $\tilde\lambda=\lambda Z_0$, the operator
$\tilde\lambda^R_{g,g}=\lambda^R_{g,g}Z_1$ of arXiv:2502.20257 (end of the CZX
passage, lines 4503--5183) in the qubit numbering $0,1,2,3$. -/
def tildeLambda : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  lambda * pauliZ 0

/-! ### Phase tables -/

/-- The permutation $x\mapsto\overline x=(x_0+1,x_1+1,x_2,x_3)$. -/
def barFlip : Equiv.Perm (Fin 4 → ZMod 2) :=
  Equiv.addRight (Pi.single 0 1 + Pi.single 1 1)

/-- The exponent $e(x)=x_0x_1+x_1x_2+x_2+x_3$ of the phase of $w$. -/
def eExponent (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 1 * x 2 + x 2 + x 3

/-- The exponent $h(x)=x_0x_1+x_1x_2+x_1+x_3$ of the phase of $\lambda$. -/
def hExponent (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 1 * x 2 + x 1 + x 3

/-- The exponent $f(x)=x_0x_1+x_1x_2+x_0+x_1+x_3$ of the phase of
$\tilde\lambda$. -/
def fExponent (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 1 * x 2 + x 0 + x 1 + x 3

theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rcases TNLean.Algebra.zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases TNLean.Algebra.zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [show ((1 : ZMod 2) + 1).val = 0 from rfl, show ((1 : ZMod 2)).val = 1 from rfl]

theorem barFlip_apply (x : Fin 4 → ZMod 2) :
    barFlip x = x + (Pi.single 0 1 + Pi.single 1 1) :=
  rfl

theorem barFlip_mul_barFlip : barFlip * barFlip = 1 := by
  ext x k
  simp only [Equiv.Perm.mul_apply, barFlip_apply, Equiv.Perm.coe_one, id_eq, Pi.add_apply,
    add_assoc]
  generalize_decide (Pi.single (0 : Fin 4) 1 : Fin 4 → ZMod 2) k,
    (Pi.single (1 : Fin 4) 1 : Fin 4 → ZMod 2) k, x k

theorem barFlip_symm : barFlip.symm = barFlip := by
  rw [← Equiv.Perm.inv_def]
  exact inv_eq_of_mul_eq_one_right barFlip_mul_barFlip

/-- The phase table of $w$: $w\ket{x}=(-1)^{e(x)}\ket{\overline x}$. -/
theorem w_eq : w = monomial barFlip fun x ↦ (-1) ^ (eExponent x).val := by
  simp only [w, pauliX, pauliZ, controlledZ, monomial_mul_monomial, Equiv.Perm.coe_one, id_eq,
    mul_one, one_mul]
  have hperm : bitFlip 0 * bitFlip 1 = barFlip := by
    ext x k
    simp only [Equiv.Perm.mul_apply, bitFlip, barFlip, Equiv.coe_addRight, Pi.add_apply]
    ring
  rw [hperm]
  congr 1
  funext x
  rw [eExponent, neg_one_pow_val_add, neg_one_pow_val_add, neg_one_pow_val_add]

/-- The phase table of $\lambda$: $\lambda\ket{x}=-i(-1)^{h(x)}\ket{\overline x}$;
the two occurrences of $X_2$ cancel on computational-basis states. -/
theorem lambda_eq : lambda = monomial barFlip fun x ↦ -I * (-1) ^ (hExponent x).val := by
  simp only [lambda, pauliX, pauliZ, controlledZ, monomial_mul_monomial, Equiv.Perm.coe_one,
    id_eq, mul_one, one_mul, smul_monomial]
  have hperm : bitFlip 0 * bitFlip 1 * bitFlip 2 * bitFlip 2 = barFlip := by
    ext x k
    simp only [Equiv.Perm.mul_apply, bitFlip, barFlip, Equiv.coe_addRight, Pi.add_apply,
      add_assoc]
    generalize_decide (Pi.single (0 : Fin 4) 1 : Fin 4 → ZMod 2) k,
      (Pi.single (1 : Fin 4) 1 : Fin 4 → ZMod 2) k,
      (Pi.single (2 : Fin 4) 1 : Fin 4 → ZMod 2) k, x k
  rw [hperm]
  congr 1
  funext x
  have h2 : bitFlip 2 x 2 = x 2 + 1 := by simp [bitFlip]
  have h0 : bitFlip 2 x 0 = x 0 := by simp [bitFlip]
  have h1 : bitFlip 2 x 1 = x 1 := by simp [bitFlip]
  have h3 : bitFlip 2 x 3 = x 3 := by simp [bitFlip]
  have hh : hExponent x = x 3 + x 0 * x 1 + x 1 * (x 2 + 1) := by
    rw [hExponent]
    ring
  rw [Pi.smul_apply, smul_eq_mul, h0, h1, h2, h3, hh, neg_one_pow_val_add, neg_one_pow_val_add]

/-- The phase table of $\tilde\lambda$:
$\tilde\lambda\ket{x}=-i(-1)^{f(x)}\ket{\overline x}$. -/
theorem tildeLambda_eq :
    tildeLambda = monomial barFlip fun x ↦ -I * (-1) ^ (fExponent x).val := by
  rw [tildeLambda, lambda_eq, pauliZ, monomial_mul_monomial, mul_one]
  congr 1
  funext x
  have hf : fExponent x = hExponent x + x 0 := by
    rw [fExponent, hExponent]
    ring
  rw [Equiv.Perm.coe_one, id_eq, hf, neg_one_pow_val_add]
  ring

/-! ### The circuit tuple on the two-site matter space -/

/-- The two matter qubits $(m^{(1)},m^{(2)})$ of one blocked site, read from the
site index in $\{0,1,2,3\}$ with $m^{(1)}$ the leading binary digit. -/
def siteBits : Fin 4 ≃ ZMod 2 × ZMod 2 :=
  (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm

/-- The four matter qubits $(x_0,x_1,x_2,x_3)=(m^{(1)}_j,m^{(2)}_j,m^{(1)}_{j+1},m^{(2)}_{j+1})$
of two neighboring blocked sites, read from the two site indices. -/
def localBits : (Fin 2 → Fin 4) ≃ (Fin 4 → ZMod 2) where
  toFun i := ![(siteBits (i 0)).1, (siteBits (i 0)).2, (siteBits (i 1)).1, (siteBits (i 1)).2]
  invFun x := ![siteBits.symm (x 0, x 1), siteBits.symm (x 2, x 3)]
  left_inv i := by
    ext k
    fin_cases k <;> simp
  right_inv x := by
    ext k
    fin_cases k <;> simp

@[simp]
theorem localBits_apply_zero (i : Fin 2 → Fin 4) : localBits i 0 = (siteBits (i 0)).1 :=
  rfl

@[simp]
theorem localBits_apply_one (i : Fin 2 → Fin 4) : localBits i 1 = (siteBits (i 0)).2 :=
  rfl

@[simp]
theorem localBits_apply_two (i : Fin 2 → Fin 4) : localBits i 2 = (siteBits (i 1)).1 :=
  rfl

@[simp]
theorem localBits_apply_three (i : Fin 2 → Fin 4) : localBits i 3 = (siteBits (i 1)).2 :=
  rfl

/-- A four-qubit operator transported to the two-site matter space. -/
def matterMatrix (M : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ) :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  reindex localBits.symm localBits.symm M

/-- The permutation $\overline{\,\cdot\,}$ transported to the two-site matter
space. -/
def matterBarFlip : Equiv.Perm (Fin 2 → Fin 4) :=
  localBits.trans (barFlip.trans localBits.symm)

theorem matterMatrix_monomial (σ : Equiv.Perm (Fin 4 → ZMod 2))
    (φ : (Fin 4 → ZMod 2) → ℂ) :
    matterMatrix (monomial σ φ) =
      monomial (localBits.trans (σ.trans localBits.symm)) (φ ∘ localBits) := by
  rw [matterMatrix, reindex_monomial, Equiv.symm_symm]

theorem matterBarFlip_symm : matterBarFlip.symm = matterBarFlip := by
  simp only [matterBarFlip, Equiv.symm_trans, Equiv.symm_symm, barFlip_symm, Equiv.trans_assoc]

@[simp]
theorem localBits_matterBarFlip (i : Fin 2 → Fin 4) :
    localBits (matterBarFlip i) = barFlip (localBits i) := by
  simp [matterBarFlip]

theorem w_mem_unitaryGroup : matterMatrix w ∈ Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ := by
  rw [w_eq, matterMatrix_monomial]
  refine monomial_mem_unitaryGroup _ _ fun s ↦ ?_
  rw [Function.comp_apply, star_pow, star_neg, star_one, ← mul_pow]
  simp

theorem tildeLambda_mem_unitaryGroup :
    matterMatrix tildeLambda ∈ Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ := by
  rw [tildeLambda_eq, matterMatrix_monomial]
  refine monomial_mem_unitaryGroup _ _ fun s ↦ ?_
  have hstar : star (-I * (-1 : ℂ) ^ (fExponent (localBits s)).val) =
      I * (-1) ^ (fExponent (localBits s)).val := by
    simp [Complex.star_def]
  rw [Function.comp_apply, hstar]
  calc I * (-1 : ℂ) ^ (fExponent (localBits s)).val *
        (-I * (-1) ^ (fExponent (localBits s)).val)
      = -(I * I) * ((-1) ^ (fExponent (localBits s)).val * (-1) ^ (fExponent (localBits s)).val) :=
        by ring
    _ = 1 := by
        rw [I_mul_I, ← mul_pow]
        simp

/-- The generator $g$ of $\mathbb Z_2=\{e,g\}$. -/
abbrev gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- The displayed CZX circuit tuple
$R^{\mathrm{CZX}}=(U_{0,0},U_{0,1},U_{1,0},U_{1,1})=
(\mathrm{id},\mathrm{id},w,\tilde\lambda)$, indexed by the ordered pair of gauge
labels in $\mathbb Z_2$ with $e\leftrightarrow0$ and $g\leftrightarrow1$.
These are the fusion operators $\lambda^R_{e,e}=\lambda^R_{e,g}=\mathrm{id}$,
$\lambda^R_{g,e}=w_R$, and the modified fusion operator
$\tilde\lambda^R_{g,g}$ of arXiv:2502.20257 (lines 4503--5183).

Whether this tuple belongs to the full physical completion class of the CZX
defect data is not asserted; only the $(1,1)$ defect map is supplied by the
source. -/
def circuitTuple (a b : Multiplicative (ZMod 2)) : Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ :=
  if Multiplicative.toAdd a = 0 then 1
  else if Multiplicative.toAdd b = 0 then ⟨matterMatrix w, w_mem_unitaryGroup⟩
  else ⟨matterMatrix tildeLambda, tildeLambda_mem_unitaryGroup⟩

@[simp]
theorem circuitTuple_one (b : Multiplicative (ZMod 2)) : circuitTuple 1 b = 1 := by
  simp [circuitTuple]

@[simp]
theorem circuitTuple_gen_one :
    (circuitTuple gen 1 : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) = matterMatrix w := by
  simp [circuitTuple]

@[simp]
theorem circuitTuple_gen_gen :
    (circuitTuple gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) =
      matterMatrix tildeLambda := by
  simp [circuitTuple]

/-! ### The local Gauss operator in monomial form -/

/-- The powers $i^q$ of the imaginary unit indexed by exponents modulo four. -/
def iPow (q : ZMod 4) : ℂ :=
  I ^ q.val

theorem iPow_add (a b : ZMod 4) : iPow (a + b) = iPow a * iPow b := by
  rw [iPow, iPow, iPow, ZMod.val_add, ← pow_eq_pow_mod _ I_pow_four, pow_add]

theorem iPow_natCast (n : ℕ) : iPow n = I ^ n := by
  rw [iPow, ZMod.val_natCast, ← pow_eq_pow_mod _ I_pow_four]

@[simp]
theorem iPow_zero : iPow 0 = 1 := by
  simp [iPow]

@[simp]
theorem iPow_two : iPow 2 = -1 := by
  rw [iPow, show (2 : ZMod 4).val = 2 from rfl, I_sq]

@[simp]
theorem iPow_three : iPow 3 = -I := by
  rw [iPow, show (3 : ZMod 4).val = 3 from rfl, pow_succ, I_sq, neg_one_mul]

theorem iPow_two_mul_val (m : ZMod 2) : iPow (2 * (m.val : ZMod 4)) = (-1) ^ m.val := by
  rw [show (2 : ZMod 4) * (m.val : ZMod 4) = ((2 * m.val : ℕ) : ZMod 4) by push_cast; ring,
    iPow_natCast, pow_mul, I_sq]

theorem iPow_two_mul_cast (m : ZMod 2) : iPow (2 * (m.cast : ZMod 4)) = (-1) ^ m.val := by
  rw [← ZMod.natCast_val, iPow_two_mul_val]

/-- The exponent $u(x)=2(x_0x_1+x_1x_2+x_3)\pmod 4$ of the phase table. -/
def uExponent (x : Fin 4 → ZMod 2) : ZMod 4 :=
  2 * ((x 0 * x 1 + x 1 * x 2 + x 3).val : ZMod 4)

/-- The phase table $q(s)$ of the local Gauss operator, as a function of the four
matter bits $x$ and the two gauge bits $(a,a')$:

| $(a,a')$ | matter operator | $q(s)\pmod 4$ |
|---|---|---|
| $(0,0)$ | $\tilde\lambda^\dagger$ | $3+u(x)+2x_2$ |
| $(0,1)$ | $w^\dagger$ | $2+u(x)+2x_0+2x_1$ |
| $(1,0)$ | $w$ | $u(x)+2x_2$ |
| $(1,1)$ | $\tilde\lambda$ | $3+u(x)+2x_0+2x_1$ | -/
def phaseExponent (x : Fin 4 → ZMod 2) (a a' : ZMod 2) : ZMod 4 :=
  if a = 0 then
    if a' = 0 then 3 + uExponent x + 2 * ((x 2).val : ZMod 4)
    else 2 + uExponent x + 2 * ((x 0).val : ZMod 4) + 2 * ((x 1).val : ZMod 4)
  else
    if a' = 0 then uExponent x + 2 * ((x 2).val : ZMod 4)
    else 3 + uExponent x + 2 * ((x 0).val : ZMod 4) + 2 * ((x 1).val : ZMod 4)

theorem phaseExponent_zero_zero (x : Fin 4 → ZMod 2) :
    phaseExponent x 0 0 = 3 + 2 * ((eExponent x).val : ZMod 4) := by
  simp only [phaseExponent, uExponent, eExponent, ↓reduceIte]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponent_zero_one (x : Fin 4 → ZMod 2) :
    phaseExponent x 0 1 = 2 + 2 * ((fExponent x).val : ZMod 4) := by
  simp only [phaseExponent, uExponent, fExponent, ↓reduceIte, one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponent_one_zero (x : Fin 4 → ZMod 2) :
    phaseExponent x 1 0 = 2 * ((eExponent x).val : ZMod 4) := by
  simp only [phaseExponent, uExponent, eExponent, ↓reduceIte, one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponent_one_one (x : Fin 4 → ZMod 2) :
    phaseExponent x 1 1 = 3 + 2 * ((fExponent x).val : ZMod 4) := by
  simp only [phaseExponent, uExponent, fExponent, ↓reduceIte, one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

/-- The exponents satisfy $f(\overline x)=e(x)+1$. -/
theorem fExponent_barFlip (x : Fin 4 → ZMod 2) : fExponent (barFlip x) = eExponent x + 1 := by
  simp only [fExponent, eExponent, barFlip_apply, Pi.add_apply, Pi.single_apply]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, add_zero]
  generalize_decide x 0, x 1, x 2, x 3

/-- The exponents satisfy $e(\overline x)=f(x)+1$. -/
theorem eExponent_barFlip (x : Fin 4 → ZMod 2) : eExponent (barFlip x) = fExponent x + 1 := by
  simp only [fExponent, eExponent, barFlip_apply, Pi.add_apply, Pi.single_apply]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, add_zero]
  generalize_decide x 0, x 1, x 2, x 3

/-- The permutation part $\sigma(s)=(\overline x,a+1,a'+1)$ of the local Gauss
operator of the circuit tuple. -/
def localPerm :
    Equiv.Perm ((Fin 2 → Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
  matterBarFlip.prodCongr (TNLean.Algebra.gaussLegAction gen)

/-- The phase $i^{q(s)}$ of the local Gauss operator of the circuit tuple. -/
def localPhase (s : (Fin 2 → Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ℂ :=
  iPow (phaseExponent (localBits s.1) (Multiplicative.toAdd s.2.1) (Multiplicative.toAdd s.2.2))

theorem gen_inv : gen⁻¹ = gen := by decide

theorem gen_mul_gen : gen * gen = 1 := by decide

theorem toAdd_gen_ne_zero : Multiplicative.toAdd gen ≠ 0 := by decide

/-- **Local monomial action of the CZX Gauss operator.** Substituting the displayed
circuit tuple into the local Gauss operator gives the monomial operator
$G\ket{s}=i^{q(s)}\ket{\sigma(s)}$ with $\sigma(s)=(\overline x,a+1,a'+1)$ and
the phase table defined by `phaseExponent`. -/
theorem gaussOperator_circuitTuple_gen :
    TNLean.Algebra.gaussOperator circuitTuple gen = monomial localPerm localPhase := by
  let σ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Equiv.Perm (Fin 2 → Fin 4) :=
    fun a _ ↦ if Multiplicative.toAdd a = 0 then 1 else matterBarFlip
  let φ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → (Fin 2 → Fin 4) → ℂ :=
    fun a b ↦ if Multiplicative.toAdd a = 0 then fun _ ↦ 1
      else if Multiplicative.toAdd b = 0 then fun i ↦ (-1) ^ (eExponent (localBits i)).val
      else fun i ↦ -I * (-1) ^ (fExponent (localBits i)).val
  have hR : ∀ a b, (circuitTuple a b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) =
      monomial (σ a b) (φ a b) := by
    intro a b
    rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
      rcases MPSTensor.zmod2_cases b with rfl | rfl
    · simp [σ, φ, monomial_one]
    · simp [σ, φ, monomial_one]
    · simp only [circuitTuple_gen_one, w_eq, matterMatrix_monomial, σ, φ, toAdd_ofAdd,
        one_ne_zero, ↓reduceIte, toAdd_one]
      rfl
    · simp only [circuitTuple_gen_gen, tildeLambda_eq, matterMatrix_monomial, σ, φ, toAdd_ofAdd,
        one_ne_zero, ↓reduceIte]
      rfl
  rw [TNLean.Algebra.gaussOperator_eq_monomial circuitTuple σ φ hR gen]
  congr 1
  · ext ⟨i, a, b⟩ : 1
    rcases MPSTensor.zmod2_cases a with rfl | rfl
    · simp [σ, localPerm, gen_inv, matterBarFlip_symm]
    · simp [σ, localPerm]
      rfl
  · funext ⟨i, a, b⟩
    simp only [TNLean.Algebra.gaussMonomialPhase, localPhase, σ, φ,
      TNLean.Algebra.gaussLegAction_apply]
    rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
      rcases MPSTensor.zmod2_cases b with rfl | rfl
    · simp [gen_inv, matterBarFlip_symm, fExponent_barFlip, phaseExponent_zero_zero,
        iPow_add, iPow_two_mul_cast, neg_one_pow_val_add, Complex.star_def,
        show ((1 : ZMod 2)).val = 1 from rfl]
    · simp [gen_inv, gen_mul_gen, matterBarFlip_symm, eExponent_barFlip, phaseExponent_zero_one,
        iPow_add, iPow_two_mul_cast, neg_one_pow_val_add, show ((1 : ZMod 2)).val = 1 from rfl]
    · simp [gen_inv, gen_mul_gen, phaseExponent_one_zero, iPow_two_mul_cast]
    · simp [gen_inv, gen_mul_gen, phaseExponent_one_one, iPow_add, iPow_two_mul_cast]

end MPOTensor.CZX
