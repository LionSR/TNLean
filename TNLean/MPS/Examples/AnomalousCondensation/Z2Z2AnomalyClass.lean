/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KleinCocycleCompleteness
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Exact
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2NonSplit
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Split
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorComap
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorOrderTwo
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# The anomaly class of the anomalous `ℤ₂ × ℤ₂` symmetry

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsection "MPO algebras
representing `ℤ₂ × ℤ₂`", `Papers/2203.12563/REsubmission.tex` lines 1845--1888:
`H³(ℤ₂ × ℤ₂, U(1)) = ℤ₂³`, and the eight classes are distinguished by the values
`ω_g = ω(g,g,g)` in a normalized gauge at the three elements of order two. The type-II class
`(−1)^{a₁ b₂ c₂}` (line 1848) has `(ω_a, ω_b, ω_ab) = (+1, +1, −1)`, row `(0,0,1)` of the table
of lines 1856--1872. The anomaly three-cochain `ω` of a group of matrix product operators is
that of Franco Rubio, Bochniak, Cirac (arXiv:2502.20257), display preceding `eq:3-cocycle`.

**Formalized here.** The dressed two-qubit tensors `M'_g` of
`AnomalousCondensationZ2Z2Exact` form an exact representation of `ℤ₂ × ℤ₂` by normal tensors
(`Z2Z2Condensation.kleinFamily_isNormalRepresentation`), so the anomaly three-cochain is
defined for the full group. For every choice of fusion tensors and every `g`, its cyclic
invariant `ω(g,e,g) ω(g,g,g)` equals that of `(−1)^{a₁ b₂ c₂}`: `+1` at `x = (1,0)` and
`y = (0,1)`, and `−1` at `xy = (1,1)`. In a normalized gauge `ω(g,e,g) = 1`, so these are the
values `(ω_a, ω_b, ω_ab) = (+1, +1, −1)` of the table. The complete Klein classification
identifies the class with `kleinCocycle` for every choice of fusion tensors.

The cyclic invariant at `f a` is computed on the restriction along a homomorphism
`f : ℤ₂ →* ℤ₂ × ℤ₂` (`MPOTensor.GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq`).
Each of the three restrictions is written as a family indexed by `ℤ₂` with explicit fusion
tensors: the identity whenever a factor is `e`, and for the square of the generator the
compression witnesses of the blocks `(x, x)` and `(xy, xy)` of
`AnomalousCondensationZ2Z2NonSplit`. The stacked square of the dressed tensor of `x` is the
stacked square of `M_x`, and that of `xy` is minus the stacked square of `M_xy`. The two fusion
trees of the triple product of the generator then agree against every nonempty word up to the
sign `+1` for `x` and `−1` for `xy`; the restriction to `{e, y}` has bond dimension one and
trivial three-cochain.

**Scope restriction (dressed family):** the class identification concerns the exact dressed
family `kleinFamily`. It does not assign a class to the original odd-ring projective family,
or compare its even-ring restriction with the dressed representation. The detector-separation
step is resolved in `docs/paper-gaps/glm23_z2z2_anomaly_detector_scope.tex`.

## Main definitions

* `Z2Z2Condensation.xHom`, `Z2Z2Condensation.yHom`, `Z2Z2Condensation.xyHom`: the three
  embeddings of `ℤ₂` onto the subgroups of order two.
* `Z2Z2Condensation.xFusionData`, `Z2Z2Condensation.xyFusionData`: fusion tensors of the
  restrictions to `{e, x}` and `{e, xy}`, as instances of
  `MPOTensor.GroupFamily.FusionData.orderTwo`.

## Main results

* `Z2Z2Condensation.omega_cohomologousTo_kleinCocycle`: every fusion choice has the type-II class.
* `Z2Z2Condensation.cyclicInvariant_omega_kleinFamily`: for every choice of fusion tensors,
  the cyclic invariant at every `g` equals that of `kleinCocycle`.
* `Z2Z2Condensation.cyclicInvariant_omega_kleinFamily_x`, `_y`, `_xy`: the values `+1`, `+1`,
  `−1`.
* `Z2Z2Condensation.not_isTrivialGaugeClass_omega_kleinFamily`: the anomaly class of the full
  `ℤ₂ × ℤ₂` symmetry is nontrivial for every choice of fusion tensors.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- Franco Rubio, Bochniak, Cirac,
  *Symmetry defects and gauging for quantum states with matrix product unitary symmetries*

## Provenance
The tensors `M_g` and the compression witnesses are representatives constructed in this
development, recorded with their exact checks in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1--5; these are verification
records, not the source.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPSTensor MPOTensor.GroupCocycle

namespace Z2Z2Condensation

/-! ### The dressed tensors as integer tensors -/

/-- The integer letters of the dressed tensor of `x`: the letter of `M_x` with input label `i`
multiplied by `(−1)^{i₂}`. -/
def kxIntTensor (o i : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ := (-1) ^ (i.val % 2) • xIntTensor o i

/-- The integer letters of the dressed tensor of `xy`. -/
def kxyIntTensor (o i : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ := (-1) ^ (i.val % 2) • xyIntTensor o i

/-- The dressed tensor of `x` from its integer letters. -/
def kxTensor : MPOTensor 4 2 := fun o i ↦ complexOfInt (kxIntTensor o i)

/-- The dressed tensor of `xy` from its integer letters. -/
def kxyTensor : MPOTensor 4 2 := fun o i ↦ complexOfInt (kxyIntTensor o i)

private theorem secondZSign_eq (g : Multiplicative (ZMod 2 × ZMod 2)) (i : Fin 4) :
    secondZSign g i = (((-1 : ℤ) ^ ((Multiplicative.toAdd g).1.val * (i.val % 2)) : ℤ) : ℂ) := by
  simp [secondZSign]

/-- The dressing of the identity element is trivial. -/
theorem kleinTensor_one : kleinTensor 1 = eTensor := by
  funext o i
  simp [kleinTensor, secondZSign, symTensor, kleinEquiv]
  rfl

/-- The dressing of `y = (0,1)` is trivial. -/
theorem kleinTensor_y : kleinTensor (Multiplicative.ofAdd (0, 1)) = yTensor := by
  funext o i
  simp [kleinTensor, secondZSign]
  rfl

/-- The dressed tensor of `x = (1,0)`. -/
theorem kleinTensor_x : kleinTensor (Multiplicative.ofAdd (1, 0)) = kxTensor := by
  have hs : symTensor (kleinEquiv (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2))) = xTensor :=
    rfl
  funext o i
  rw [kleinTensor, hs]
  change secondZSign (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) i •
      complexOfInt (xIntTensor o i) = complexOfInt ((-1) ^ (i.val % 2) • xIntTensor o i)
  rw [complexOfInt_zsmul, secondZSign_eq]
  norm_num [ZMod.val_one]

/-- The dressed tensor of `xy = (1,1)`. -/
theorem kleinTensor_xy : kleinTensor (Multiplicative.ofAdd (1, 1)) = kxyTensor := by
  have hs : symTensor (kleinEquiv (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2))) = xyTensor :=
    rfl
  funext o i
  rw [kleinTensor, hs]
  change secondZSign (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) i •
      complexOfInt (xyIntTensor o i) = complexOfInt ((-1) ^ (i.val % 2) • xyIntTensor o i)
  rw [complexOfInt_zsmul, secondZSign_eq]
  norm_num [ZMod.val_one]

/-! ### The three subgroups of order two -/

/-- The embedding of `ℤ₂` onto `{e, x}`, `x = (1,0)`. -/
def xHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.inl (ZMod 2) (ZMod 2))

/-- The embedding of `ℤ₂` onto `{e, y}`, `y = (0,1)`. -/
def yHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.inr (ZMod 2) (ZMod 2))

/-- The embedding of `ℤ₂` onto the diagonal `{e, xy}`, `xy = (1,1)`. -/
def xyHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative ((AddMonoidHom.id (ZMod 2)).prod (AddMonoidHom.id (ZMod 2)))

/-- A family `1 ↦ M_e`, `g ↦ A` equal to a restriction of the dressed family: bond dimensions
agree by computation, and the tensors by `kleinTensor_one` and `hA`. -/
private theorem comap_eq_orderTwoFamily
    (f : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2))
    (hb0 : bondDim (kleinEquiv (f 1)) = 1)
    (hb1 : bondDim (kleinEquiv (f GroupFamily.orderTwoGen)) = 2)
    (h1 : f 1 = 1) {A : MPOTensor 4 2}
    (hA : HEq (kleinTensor (f GroupFamily.orderTwoGen)) A) :
    kleinFamily.comap f = GroupFamily.orderTwoFamily eTensor A := by
  refine GroupFamily.ext_of_heq ?_ ?_
  · funext x
    revert x
    refine Multiplicative.forall_zmod_two ?_ ?_
    · exact hb0
    · exact hb1
  · refine Multiplicative.forall_zmod_two ?_ hA
    change HEq (kleinTensor (f 1)) eTensor
    rw [h1, kleinTensor_one]
    exact HEq.rfl

/-! ### The integer data of the two nontrivial blocks -/

private theorem eKx_int (b : Fin (4 * 4)) :
    stackedInt eIntTensor kxIntTensor b = kxIntTensor b.divNat b.modNat := by
  revert_decide_kernel b

private theorem kxE_int (b : Fin (4 * 4)) :
    stackedInt kxIntTensor eIntTensor b = kxIntTensor b.divNat b.modNat := by
  revert_decide_kernel b

private theorem kxKx_int (b : Fin (4 * 4)) : stackedInt kxIntTensor kxIntTensor b = xXInt b := by
  revert_decide_kernel b

private theorem eKxy_int (b : Fin (4 * 4)) :
    stackedInt eIntTensor kxyIntTensor b = kxyIntTensor b.divNat b.modNat := by
  revert_decide_kernel b

private theorem kxyE_int (b : Fin (4 * 4)) :
    stackedInt kxyIntTensor eIntTensor b = kxyIntTensor b.divNat b.modNat := by
  revert_decide_kernel b

private theorem kxyKxy_int (b : Fin (4 * 4)) :
    stackedInt kxyIntTensor kxyIntTensor b = -xyXyInt b := by
  revert_decide_kernel b

/-- Stacking `M_e` with the dressed tensor of `x` gives that tensor. -/
theorem mulTensor_eTensor_kxTensor :
    (mulTensor eTensor kxTensor).toMPSTensor = kxTensor.toMPSTensor := by
  funext a
  rw [show (mulTensor eTensor kxTensor).toMPSTensor a = _ from
    toMPSTensor_mulTensor_complexOfInt eIntTensor kxIntTensor a, eKx_int]
  rfl

/-- Stacking the dressed tensor of `x` with `M_e` gives that tensor. -/
theorem mulTensor_kxTensor_eTensor :
    (mulTensor kxTensor eTensor).toMPSTensor = kxTensor.toMPSTensor := by
  funext a
  rw [show (mulTensor kxTensor eTensor).toMPSTensor a = _ from
    toMPSTensor_mulTensor_complexOfInt kxIntTensor eIntTensor a, kxE_int]
  rfl

/-- Stacking `M_e` with the dressed tensor of `xy` gives that tensor. -/
theorem mulTensor_eTensor_kxyTensor :
    (mulTensor eTensor kxyTensor).toMPSTensor = kxyTensor.toMPSTensor := by
  funext a
  rw [show (mulTensor eTensor kxyTensor).toMPSTensor a = _ from
    toMPSTensor_mulTensor_complexOfInt eIntTensor kxyIntTensor a, eKxy_int]
  rfl

/-- Stacking the dressed tensor of `xy` with `M_e` gives that tensor. -/
theorem mulTensor_kxyTensor_eTensor :
    (mulTensor kxyTensor eTensor).toMPSTensor = kxyTensor.toMPSTensor := by
  funext a
  rw [show (mulTensor kxyTensor eTensor).toMPSTensor a = _ from
    toMPSTensor_mulTensor_complexOfInt kxyIntTensor eIntTensor a, kxyE_int]
  rfl

/-- Stacking `M_e` with itself gives `M_e`. -/
theorem mulTensor_eTensor_eTensor :
    (mulTensor eTensor eTensor).toMPSTensor = eTensor.toMPSTensor :=
  funext eEStacked_eq

/-- **The square of the dressed tensor of `x` is the square of `M_x`**, so the compression
witnesses of the block `(x, x)` are fusion tensors onto `M_e`. -/
theorem kx_isReduction :
    MPSTensor.IsReduction (mulTensor kxTensor kxTensor).toMPSTensor eTensor.toMPSTensor xXLeft
      xXRight := by
  have h : (mulTensor kxTensor kxTensor).toMPSTensor = xXStacked := by
    funext a
    rw [xXStacked_eq, ← kxKx_int]
    exact toMPSTensor_mulTensor_complexOfInt kxIntTensor kxIntTensor a
  rw [h]
  exact xX_isReduction

/-- **The square of the dressed tensor of `xy` is minus the square of `M_xy`**, so the
compression witnesses of the block `(xy, xy)` are fusion tensors onto `M_e`: the sign cancels
the weight `−1` of the target of that block. -/
theorem kxy_isReduction :
    MPSTensor.IsReduction (mulTensor kxyTensor kxyTensor).toMPSTensor eTensor.toMPSTensor
      xyXyLeft xyXyRight := by
  have h : (mulTensor kxyTensor kxyTensor).toMPSTensor = fun i ↦ (-1 : ℂ) • xyXyStacked i := by
    funext a
    rw [xyXyStacked_eq, show (mulTensor kxyTensor kxyTensor).toMPSTensor a = _
      from toMPSTensor_mulTensor_complexOfInt kxyIntTensor kxyIntTensor a, kxyKxy_int,
      complexOfInt_neg, neg_one_smul]
  rw [h]
  convert xyXy_isReduction.smul (-1) using 1
  funext i
  simp [eMPS]

/-- The restriction of the dressed family to `{e, x}`. -/
def xFusionData : (GroupFamily.orderTwoFamily eTensor kxTensor).FusionData :=
  GroupFamily.FusionData.orderTwo eTensor kxTensor xXLeft xXRight mulTensor_eTensor_eTensor
    mulTensor_eTensor_kxTensor mulTensor_kxTensor_eTensor kx_isReduction

/-- The restriction of the dressed family to `{e, xy}`. -/
def xyFusionData : (GroupFamily.orderTwoFamily eTensor kxyTensor).FusionData :=
  GroupFamily.FusionData.orderTwo eTensor kxyTensor xyXyLeft xyXyRight mulTensor_eTensor_eTensor
    mulTensor_eTensor_kxyTensor mulTensor_kxyTensor_eTensor kxy_isReduction

/-- The restriction of the dressed family to `{e, x}` is the family `1 ↦ M_e`, `g ↦ M'_x`. -/
theorem comap_xHom : kleinFamily.comap xHom = GroupFamily.orderTwoFamily eTensor kxTensor :=
  comap_eq_orderTwoFamily xHom rfl rfl rfl (heq_of_eq kleinTensor_x)

/-- The restriction of the dressed family to `{e, xy}` is the family `1 ↦ M_e`,
`g ↦ M'_xy`. -/
theorem comap_xyHom : kleinFamily.comap xyHom = GroupFamily.orderTwoFamily eTensor kxyTensor :=
  comap_eq_orderTwoFamily xyHom rfl rfl rfl (heq_of_eq kleinTensor_xy)

/-- The family `1 ↦ M_e`, `g ↦ M'_x` is an exact representation of `ℤ₂` by normal tensors,
as a restriction of the dressed family. -/
theorem orderTwoFamily_kx_isNormalRepresentation :
    (GroupFamily.orderTwoFamily eTensor kxTensor).IsNormalRepresentation :=
  comap_xHom ▸ kleinFamily_isNormalRepresentation.comap xHom

/-- The family `1 ↦ M_e`, `g ↦ M'_xy` is an exact representation of `ℤ₂` by normal tensors,
as a restriction of the dressed family. -/
theorem orderTwoFamily_kxy_isNormalRepresentation :
    (GroupFamily.orderTwoFamily eTensor kxyTensor).IsNormalRepresentation :=
  comap_xyHom ▸ kleinFamily_isNormalRepresentation.comap xyHom

/-! ### The two fusion trees of three generators -/

/-- The `8 × 8` integer matrix whose only nonzero column is `k`, with entries `v`. -/
def columnInt (k : Fin (2 * 2 * 2)) (v : Fin (2 * 2 * 2) → ℤ) :
    Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ :=
  Matrix.of fun r c ↦ if c = k then v r else 0

/-- The integer letters of the triple product of the dressed tensor of `x`, bond ordered
((first, second), third). -/
def kxCubeInt : Fin 16 → Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ
  | 2 => columnInt 0 ![1, 1, 1, 1, 1, 1, 1, 1]
  | 7 => columnInt 7 ![-1, 1, 1, -1, 1, -1, -1, 1]
  | 8 => columnInt 0 ![1, 1, 1, 1, 1, 1, 1, 1]
  | 13 => columnInt 7 ![-1, 1, 1, -1, 1, -1, -1, 1]
  | _ => 0

/-- The integer letters of the triple product of the dressed tensor of `xy`. -/
def kxyCubeInt : Fin 16 → Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ
  | 3 => columnInt 5 ![1, -1, 1, -1, -1, 1, -1, 1]
  | 6 => columnInt 2 ![-1, -1, 1, 1, -1, -1, 1, 1]
  | 9 => columnInt 5 ![1, -1, 1, -1, -1, 1, -1, 1]
  | 12 => columnInt 2 ![-1, -1, 1, 1, -1, -1, 1, 1]
  | _ => 0

private theorem kxCube_int (a : Fin 16) :
    mulIntTensor (mulIntTensor kxIntTensor kxIntTensor) kxIntTensor (@Fin.divNat 4 4 a)
      (@Fin.modNat 4 4 a) = kxCubeInt a := by
  revert_decide_kernel a

private theorem kxyCube_int (a : Fin 16) :
    mulIntTensor (mulIntTensor kxyIntTensor kxyIntTensor) kxyIntTensor (@Fin.divNat 4 4 a)
      (@Fin.modNat 4 4 a) = kxyCubeInt a := by
  revert_decide_kernel a

/-- The triple product of an integer tensor is the image of its integer triple product. -/
private theorem triple_complexOfInt (M : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℤ)
    (a : Fin 16) :
    (mulTensor (mulTensor (fun o i ↦ complexOfInt (M o i)) (fun o i ↦ complexOfInt (M o i)))
        (fun o i ↦ complexOfInt (M o i))).toMPSTensor a =
      complexOfInt (mulIntTensor (mulIntTensor M M) M (@Fin.divNat 4 4 a)
        (@Fin.modNat 4 4 a)) := by
  have h2 : mulTensor (fun o i ↦ complexOfInt (M o i)) (fun o i ↦ complexOfInt (M o i)) =
      fun o i ↦ complexOfInt (mulIntTensor M M o i) :=
    funext₂ fun o i ↦ mulTensor_complexOfRing _ M M o i
  change mulTensor _ _ (@Fin.divNat 4 4 a) (@Fin.modNat 4 4 a) = _
  rw [h2]
  exact mulTensor_complexOfRing _ _ M _ _

/-- The integer letters of the dressed tensor of `x` over the pair alphabet. -/
def kxIntMPS (a : Fin 16) : Matrix (Fin 2) (Fin 2) ℤ :=
  kxIntTensor (@Fin.divNat 4 4 a) (@Fin.modNat 4 4 a)

/-- The integer letters of the dressed tensor of `xy` over the pair alphabet. -/
def kxyIntMPS (a : Fin 16) : Matrix (Fin 2) (Fin 2) ℤ :=
  kxyIntTensor (@Fin.divNat 4 4 a) (@Fin.modNat 4 4 a)

/-- **The associator of three copies of `x` is `+1`**: with the fusion tensors of
`xFusionData`, the two fusion trees agree against every nonempty word of the triple product.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`; the value is `ω_a = +1` of the
type-II row of arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1856--1872. -/
theorem xFusionData_isAssociator_gen_gen_gen :
    xFusionData.IsAssociator GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen ((1 : ℤ) : ℂ) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [xFusionData]
  rw [GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen,
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen]
  rw [xXLeft, kronId_complexOfRing,
    idKron_complexOfRing]
  have hT : (GroupFamily.tripleTensor (GroupFamily.orderTwoFamily eTensor kxTensor)
      GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen).toMPSTensor =
      fun a ↦ complexOfInt (kxCubeInt a) := by
    funext a
    rw [← kxCube_int]
    exact triple_complexOfInt kxIntTensor a
  rw [hT]
  refine MPSTensor.isDressedProportional_complexOfInt_of_mem (A := kxIntMPS)
    [(kxCubeInt 2, kxIntMPS 2), (kxCubeInt 7, kxIntMPS 7), (0, 0)] (by decide +kernel) ?_ ?_ ?_ <;>
    decide +kernel

/-- **The associator of three copies of `xy` is `−1`**.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`; the value is `ω_ab = −1` of the
type-II row of arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1856--1872. -/
theorem xyFusionData_isAssociator_gen_gen_gen :
    xyFusionData.IsAssociator GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen ((-1 : ℤ) : ℂ) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [xyFusionData]
  rw [GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen,
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen]
  rw [xyXyLeft, kronId_complexOfRing,
    idKron_complexOfRing]
  have hT : (GroupFamily.tripleTensor (GroupFamily.orderTwoFamily eTensor kxyTensor)
      GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen).toMPSTensor =
      fun a ↦ complexOfInt (kxyCubeInt a) := by
    funext a
    rw [← kxyCube_int]
    exact triple_complexOfInt kxyIntTensor a
  rw [hT]
  refine MPSTensor.isDressedProportional_complexOfInt_of_mem (A := kxyIntMPS)
    [(kxyCubeInt 3, kxyIntMPS 3), (kxyCubeInt 6, kxyIntMPS 6), (0, 0)] (by decide +kernel)
    ?_ ?_ ?_ <;>
    decide +kernel

/-! ### The restriction to `{e, y}` -/

/-- The bond-one tensors of the restriction to `{e, y}`. -/
def yLabelTensor : Fin 2 → MPOTensor 4 1
  | ⟨0, _⟩ => eTensor
  | ⟨1, _⟩ => yTensor
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- Fusion tensors of the restriction to `{e, y}`: all one-by-one identities. -/
def yFusionData :
    (GroupFamily.ofBondOne fun x : Multiplicative (ZMod 2) ↦ yLabelTensor x.toAdd).FusionData :=
  GroupFamily.FusionData.ofBondOne _ <| by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_)
    · exact funext eEStacked_eq
    · exact funext eYStacked_eq
    · exact funext yEStacked_eq
    · exact funext yYStacked_eq

/-- The restriction of the dressed family to `{e, y}` is the bond-one family `1 ↦ M_e`,
`g ↦ M_y`. -/
theorem comap_yHom :
    kleinFamily.comap yHom =
      GroupFamily.ofBondOne fun x : Multiplicative (ZMod 2) ↦ yLabelTensor x.toAdd := by
  refine GroupFamily.ext_of_heq ?_ ?_
  · funext x
    revert x
    exact Multiplicative.forall_zmod_two rfl rfl
  · refine Multiplicative.forall_zmod_two ?_ ?_
    · change HEq (kleinTensor 1) eTensor
      rw [kleinTensor_one]
      exact HEq.rfl
    · exact heq_of_eq kleinTensor_y

/-! ### The anomaly class of the full group -/

/-- The cyclic invariant `ω(x,e,x) ω(x,x,x)` at `x = (1,0)` is `+1`. -/
theorem cyclicInvariant_omega_kleinFamily_x (fd : kleinFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 0)) 2 = 1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (xHom GroupFamily.orderTwoGen) 2 = 1
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd xHom
    kleinFamily_isNormalRepresentation comap_xHom xFusionData GroupFamily.orderTwoGen_pow_two]
  apply Units.ext
  rw [xFusionData, GroupFamily.FusionData.cyclicInvariant_orderTwo_of_isAssociator
    orderTwoFamily_kx_isNormalRepresentation xFusionData_isAssociator_gen_gen_gen]
  simp

/-- The cyclic invariant `ω(xy,e,xy) ω(xy,xy,xy)` at `xy = (1,1)` is `−1`. -/
theorem cyclicInvariant_omega_kleinFamily_xy (fd : kleinFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 1)) 2 = -1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (xyHom GroupFamily.orderTwoGen) 2 = -1
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd xyHom
    kleinFamily_isNormalRepresentation comap_xyHom xyFusionData GroupFamily.orderTwoGen_pow_two]
  apply Units.ext
  rw [xyFusionData, GroupFamily.FusionData.cyclicInvariant_orderTwo_of_isAssociator
    orderTwoFamily_kxy_isNormalRepresentation xyFusionData_isAssociator_gen_gen_gen]
  simp

/-- The cyclic invariants on the restriction to `{e, y}` are one. -/
private theorem cyclicInvariant_omega_kleinFamily_yHom (fd : kleinFamily.FusionData)
    (a : Multiplicative (ZMod 2)) :
    ScalarThreeCochain.cyclicInvariant fd.omega (yHom a) 2 = 1 := by
  have ha : a ^ 2 = 1 := by revert a; decide
  have h1 : yFusionData.omega = 1 := GroupFamily.FusionData.omega_ofBondOne
    (comap_yHom ▸ kleinFamily_isNormalRepresentation.comap yHom)
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd yHom
      kleinFamily_isNormalRepresentation comap_yHom yFusionData ha, h1]
  simp [ScalarThreeCochain.cyclicInvariant]

/-- The cyclic invariant `ω(y,e,y) ω(y,y,y)` at `y = (0,1)` is `+1`. -/
theorem cyclicInvariant_omega_kleinFamily_y (fd : kleinFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (0, 1)) 2 = 1 :=
  cyclicInvariant_omega_kleinFamily_yHom fd GroupFamily.orderTwoGen

/-- The cyclic invariant `ω(g,e,g) ω(g,g,g)` of `(−1)^{a₁ b₂ c₂}` is `(−1)^{g₁ g₂}`: `+1` at
`e, x, y` and `−1` at `xy`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1848 and 1856--1872
(row `(0,0,1)`). -/
theorem cyclicInvariant_kleinCocycle (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ScalarThreeCochain.cyclicInvariant ScalarThreeCochain.kleinCocycle g 2 =
      (-1) ^ ((Multiplicative.toAdd g).1 * (Multiplicative.toAdd g).2).val := by
  simp only [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, pow_zero, pow_one, ScalarThreeCochain.kleinCocycle, toAdd_one, Prod.snd_zero,
    mul_zero, zero_mul, ZMod.val_zero]
  congr 2
  generalize Multiplicative.toAdd g = p
  revert p
  decide

/-- **The anomaly class of the full `ℤ₂ × ℤ₂` symmetry has the detector values of
`(−1)^{a₁ b₂ c₂}`**: for every choice of fusion tensors of the dressed family and every `g`,
the gauge-invariant product `ω(g,e,g) ω(g,g,g)` equals that of `kleinCocycle`, which is `+1` at
`e, x, y` and `−1` at `xy`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1845--1872 (the classes of
`ℤ₂ × ℤ₂`, detected by `ω(g,g,g)`), for the type-II cocycle of line 1848; the three-cochain is
that of arXiv:2502.20257, display preceding `eq:3-cocycle`, and the invariance is
`eq:omegagauge`. -/
theorem cyclicInvariant_omega_kleinFamily (fd : kleinFamily.FusionData)
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ScalarThreeCochain.cyclicInvariant fd.omega g 2 =
      ScalarThreeCochain.cyclicInvariant ScalarThreeCochain.kleinCocycle g 2 := by
  rw [cyclicInvariant_kleinCocycle]
  revert g
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  · exact cyclicInvariant_omega_kleinFamily_yHom fd 1
  · exact cyclicInvariant_omega_kleinFamily_y fd
  · exact cyclicInvariant_omega_kleinFamily_x fd
  · rw [cyclicInvariant_omega_kleinFamily_xy fd]
    simp [ZMod.val_one]

/-- The exact dressed representation has the mixed type-II anomaly class for every choice
of fusion tensors. Source: arXiv:2203.12563, lines 1845–1872. The family distinction is
specified in the module docstring. -/
theorem omega_cohomologousTo_kleinCocycle (fd : kleinFamily.FusionData) :
    ScalarThreeCochain.CohomologousTo fd.omega ScalarThreeCochain.kleinCocycle :=
  (ScalarThreeCochain.cohomologousTo_iff_klein_cyclicInvariant_eq
    (fd.isCocycle_omega kleinFamily_isNormalRepresentation)
    ScalarThreeCochain.kleinCocycle_isCocycle).2 (cyclicInvariant_omega_kleinFamily fd)

/-- **The anomalous `ℤ₂ × ℤ₂` symmetry is anomalous**: for every choice of fusion tensors, the
anomaly three-cocycle of the dressed family is not cohomologous to the trivial one.

Source: arXiv:2502.20257, `eq:omegagauge` and the sentence following it. The detector value
`−1` at `xy` is that of the type-II class of arXiv:2203.12563,
`Papers/2203.12563/REsubmission.tex` lines 1845--1872. -/
theorem not_isTrivialGaugeClass_omega_kleinFamily (fd : kleinFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one
    (g := Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) (n := 2) (by decide) ?_
  rw [cyclicInvariant_omega_kleinFamily_xy]
  intro h
  have := congrArg Units.val h
  norm_num at this

/-- The anomaly class of the dressed family in Mathlib's `H³(ℤ₂ × ℤ₂, ℂˣ)` is nonzero for
every choice of fusion tensors (arXiv:2203.12563, lines 1845–1872). -/
theorem anomalyClass_omega_kleinFamily_ne_zero (fd : kleinFamily.FusionData) :
    ScalarThreeCochain.anomalyClass
      ⟨fd.omega, fd.isCocycle_omega kleinFamily_isNormalRepresentation⟩ ≠ 0 := fun h ↦
  not_isTrivialGaugeClass_omega_kleinFamily fd
    ((ScalarThreeCochain.isTrivialGaugeClass_iff_anomalyClass_eq_zero _).2 h)

end Z2Z2Condensation
