/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
module

public import Mathlib.Algebra.Ring.MinimalAxioms
public import TNLean.MPS.Symmetry.MPOSymmetry.FusionRing
public import TNLean.MPS.Symmetry.MPOSymmetry.IntegerNIMRep

/-!
# Fusion rings on integer combinations

Project construction using the fusion rules, unit and duality of
`IsFusionRing` (arXiv:2203.12563, line 1236). The regular matrix action is
faithful: its column at the unit recovers every coefficient. This realizes
integer convolution as an associative product and supplies its Ring instance.

The carrier depends on the fusion data, so distinct products on the same
label type do not compete as global Ring instances on raw `Finsupp`.
-/

@[expose] public section

noncomputable section

namespace MPOTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The regular multiplicities satisfy the NIM-representation relation by
associativity of the structure constants. -/
theorem IsFusionRing.isNIMRep {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) : IsNIMRep N N :=
  hN.assoc

/-- The unit column of the regular action recovers the coefficients.
Project result. -/
theorem IsFusionRing.integerNIMRepEval_unit_column
    {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) (u : ι →₀ ℤ) (c : ι) :
    integerNIMRepEval N u c e = u c := by
  have hright : ∀ a c, N a e c = if c = a then 1 else 0 :=
    fun a c ↦ (hN.isFusionUnit a c).2
  simp [integerNIMRepEval, integerFusionEval, integerNIMRepMatrix, hright,
    zsmul_eq_mul, mul_ite]

/-- The regular action on integer combinations is faithful. -/
theorem IsFusionRing.integerNIMRepEval_injective
    {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) : Function.Injective (integerNIMRepEval N) := by
  intro u v huv
  ext c
  have h := congrArg (fun A : Matrix ι ι ℤ ↦ A c e) huv
  simpa only [hN.integerNIMRepEval_unit_column] using h

/-- Associativity of integer convolution, transported through the faithful
regular action. Project result. -/
theorem IsFusionRing.integerFusionMul_assoc
    {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) (u v w : ι →₀ ℤ) :
    integerFusionMul N (integerFusionMul N u v) w =
      integerFusionMul N u (integerFusionMul N v w) := by
  apply hN.integerNIMRepEval_injective
  simp only [integerNIMRepEval, integerFusionEval_mul N _
    hN.isNIMRep.integerNIMRepMatrix_mul, mul_assoc]

/-- The distinguished singleton is a left unit for integer convolution. -/
theorem IsFusionRing.integerFusionMul_one_left
    {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) (u : ι →₀ ℤ) :
    integerFusionMul N (Finsupp.single e 1) u = u := by
  apply hN.integerNIMRepEval_injective
  simp only [integerNIMRepEval, integerFusionEval_mul N _
    hN.isNIMRep.integerNIMRepMatrix_mul, integerFusionEval_single, one_smul]
  rw [integerNIMRepMatrix_unit (M := N) (e := e) (fun x y ↦ by
    simpa only [eq_comm] using (hN.isFusionUnit x y).1), one_mul]

/-- The distinguished singleton is a right unit for integer convolution. -/
theorem IsFusionRing.integerFusionMul_one_right
    {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) (u : ι →₀ ℤ) :
    integerFusionMul N u (Finsupp.single e 1) = u := by
  apply hN.integerNIMRepEval_injective
  simp only [integerNIMRepEval, integerFusionEval_mul N _
    hN.isNIMRep.integerNIMRepMatrix_mul, integerFusionEval_single, one_smul]
  rw [integerNIMRepMatrix_unit (M := N) (e := e) (fun x y ↦ by
    simpa only [eq_comm] using (hN.isFusionUnit x y).1), mul_one]

/-- Ring structure on integer combinations for specified fusion data.
This is a constructor, not a global instance on raw finitely supported functions. -/
def IsFusionRing.integerFusionRing {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) : Ring (ι →₀ ℤ) := by
  letI : Mul (ι →₀ ℤ) := ⟨integerFusionMul N⟩
  letI : One (ι →₀ ℤ) := ⟨Finsupp.single e 1⟩
  exact Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    hN.integerFusionMul_assoc hN.integerFusionMul_one_left
    hN.integerFusionMul_one_right (integerFusionMul_add_right N)
    (integerFusionMul_add_left N)

/-- A fusion ring with its finite basis, natural constants, unit and duality.
Source: arXiv:2203.12563, line 1236; the axioms are those of `IsFusionRing`. -/
structure FusionRing (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Natural structure constants. -/
  constants : ι → ι → ι → ℕ
  /-- Distinguished unit label. -/
  unit : ι
  /-- Involutive duality on labels. -/
  dual : ι → ι
  /-- Associativity, the unit identities, and duality identities. -/
  laws : IsFusionRing constants unit dual

namespace FusionRing

/-- Integer combinations with multiplication determined by the chosen fusion data. -/
def Carrier (F : FusionRing ι) := ι →₀ ℤ

instance (F : FusionRing ι) : Ring F.Carrier :=
  F.laws.integerFusionRing

instance (F : FusionRing ι) : CoeFun F.Carrier (fun _ ↦ ι → ℤ) :=
  ⟨fun u ↦ (u : ι →₀ ℤ)⟩

/-- A distinguished basis element of the integer fusion ring. -/
def basis (F : FusionRing ι) (a : ι) : F.Carrier := Finsupp.single a 1

/-- The distinguished unit label is the ring unit. -/
@[simp]
theorem basis_unit (F : FusionRing ι) : F.basis F.unit = 1 := rfl

/-- The coefficient formula for the ring multiplication. -/
theorem mul_apply (F : FusionRing ι) (u v : F.Carrier) (c : ι) :
    (u * v : F.Carrier) c = ∑ a, ∑ b, u a * v b * (F.constants a b c : ℤ) :=
  rfl

/-- A family satisfying the unit and fusion-product identities extends to a
unital ring homomorphism. Project result; the target can be noncommutative. -/
def lift (F : FusionRing ι) {R : Type*} [Ring R] (f : ι → R)
    (hunit : f F.unit = 1)
    (hmul : ∀ a b, f a * f b = ∑ c, (F.constants a b c : ℤ) • f c) :
    F.Carrier →+* R where
  toFun := integerFusionEval f
  map_zero' := (integerFusionEval f).map_zero
  map_add' := (integerFusionEval f).map_add
  map_one' := by
    change integerFusionEval f (Finsupp.single F.unit 1) = 1
    simpa only [integerFusionEval_single, one_smul] using hunit
  map_mul' := integerFusionEval_mul F.constants f hmul

/-- The extension takes each distinguished basis element to its prescribed image. -/
@[simp]
theorem lift_basis (F : FusionRing ι) {R : Type*} [Ring R] (f : ι → R)
    (hunit : f F.unit = 1)
    (hmul : ∀ a b, f a * f b = ∑ c, (F.constants a b c : ℤ) • f c) (a : ι) :
    F.lift f hunit hmul (F.basis a) = f a := by
  change integerFusionEval f (Finsupp.single a 1) = f a
  simp only [integerFusionEval_single, one_smul]

/-- Forward NIM-representation bridge, with the additional unit condition
explicit. The matrix images use output rows and input columns. -/
def nimRepHom (F : FusionRing ι) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : ι → κ → κ → ℕ) (hM : IsNIMRep F.constants M)
    (hunit : ∀ x y, M F.unit x y = if x = y then 1 else 0) :
    F.Carrier →+* Matrix κ κ ℤ :=
  F.lift (integerNIMRepMatrix M)
    (integerNIMRepMatrix_unit (M := M) (e := F.unit) hunit)
    hM.integerNIMRepMatrix_mul

/-- A NIM-representation's extension has exactly the prescribed nonnegative
integer basis images. -/
@[simp]
theorem nimRepHom_basis (F : FusionRing ι) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : ι → κ → κ → ℕ) (hM : IsNIMRep F.constants M)
    (hunit : ∀ x y, M F.unit x y = if x = y then 1 else 0) (a : ι) :
    F.nimRepHom M hM hunit (F.basis a) = integerNIMRepMatrix M a :=
  F.lift_basis _ _ _ a

/-- Each basis image of the NIM-representation homomorphism has nonnegative entries. -/
theorem nimRepHom_basis_nonneg (F : FusionRing ι) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (M : ι → κ → κ → ℕ)
    (hM : IsNIMRep F.constants M)
    (hunit : ∀ x y, M F.unit x y = if x = y then 1 else 0) (a : ι) (x y : κ) :
    0 ≤ F.nimRepHom M hM hunit (F.basis a) y x := by
  rw [nimRepHom_basis]
  exact Int.natCast_nonneg _

/-- A ring-valued fusion character extends to a RingHom on integer combinations.
The ring target is explicit: the old predicate also permits semiring targets. -/
def characterHom (F : FusionRing ι) {R : Type*} [Ring R] (χ : ι → R)
    (hχ : IsFusionCharacter F.constants F.unit χ) : F.Carrier →+* R :=
  F.lift χ hχ.1 (by
    intro a b
    simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_natCast, smul_eq_mul]
      using hχ.2 a b)

/-- The ring-valued character extension has the prescribed basis values. -/
@[simp]
theorem characterHom_basis (F : FusionRing ι) {R : Type*} [Ring R] (χ : ι → R)
    (hχ : IsFusionCharacter F.constants F.unit χ) (a : ι) :
    F.characterHom χ hχ (F.basis a) = χ a :=
  F.lift_basis _ _ _ a

end FusionRing

end MPOTensor
