/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.RingEmbedding
import TNLean.MPS.MPDO.CZXActionTensors
import TNLean.MPS.MPDO.CZXFusionTensors
import TNLean.MPS.MPDO.CZXTensorInjectivity
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorCohomology
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorOrderTwo
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks

/-!
# The anomaly and the L-symbols of the blocked CZX matrix product unitary

The once-blocked CZX tensor `MPOTensor.CZX.tensor` of arXiv:2502.20257, `eq:MPU_CZX`
(`main.tex` lines 4503--4547), squares to the identity on every periodic chain, so with the
bond-one identity tensor it represents `ℤ₂ = {e, g}`. With the fusion tensors that are trivial
whenever a factor is the identity and are the printed caps `F^<_{g,g} = Y`,
`F^>_{g,g} = Y / 2` of lines 4671--4689 for two generators, the anomaly is

`ω(h₁,h₂,h₃) = (-1)^(δ_{h₁,g} δ_{h₂,g} δ_{h₃,g})`,

as displayed in lines 4695--4698, and its cohomology class is nonzero for every choice of
fusion tensors.

The two once-blocked GHZ sectors `|00⟩` and `|11⟩` of lines 4660--4670 are exchanged by `g`.
With the action tensors of lines 4690--4694 (the bra dressed by one acted letter, which agrees
with the printed bra against every nonempty word, see `MPOTensor.CZX.dressedActionBra`), every
L-symbol is one except at `(g, g)`, where the two sectors carry opposite signs. For every choice
of fusion and action tensors the ratio `L⁰_{g,g} L⁰_{g,e} / (L¹_{g,g} L⁰_{e,g})` is `ω(g,g,g)`,
the relation of line 5121, and it equals `-1`.

**Local fix (orientation of the fusion caps):** the source states that the only nontrivial
L-symbol is `L⁰_{g,g} = -1` (line 4699). With the printed caps read in the bond order of
`MPOTensor.mulTensor`, the computation of `MPOTensor.CZX.blockActionData_lSymbol` gives
`L⁰_{g,g} = 1` and `L¹_{g,g} = -1`. The two readings of the cap diagram, `Y_{ab}` and
`Y_{ba} = -Y_{ab}`, differ by the scalar fusion gauge `β_{g,g} = -1` of `eq:scalar_fus_ten`,
which leaves `ω` unchanged and multiplies both `Lˣ_{g,g}` by `-1` (`eq:Lsymbgauge`); with the
transposed reading the printed values hold. The gauge-invariant ratio `L⁰_{g,g} / L¹_{g,g} = -1`
is the same for both. Documented in
`docs/paper-gaps/fbc25_czx_fusion_coordinate_compatibility.tex`.

## Main definitions

* `MPOTensor.CZX.family`: the `ℤ₂`-indexed family `e ↦ 1`, `g ↦ CZX`.
* `MPOTensor.CZX.fusionData`: the fusion tensors with the printed caps.
* `MPOTensor.CZX.block`: the two once-blocked GHZ sectors, indexed by `ℤ₂`.
* `MPOTensor.CZX.blockActionData`: the action tensors.

## Main results

* `MPOTensor.CZX.mpo_tensor_mul_self`: the CZX operator squares to the identity.
* `MPOTensor.CZX.family_isNormalRepresentation`: the CZX tensors form a normal representation.
* `MPOTensor.CZX.fusionData_omega`: the displayed anomaly three-cocycle.
* `MPOTensor.CZX.family_anomalyClass_ne_zero`: the anomaly class is nonzero.
* `MPOTensor.CZX.carriesMPV`: the representation permutes the two GHZ sectors.
* `MPOTensor.CZX.blockActionData_lSymbol`: the L-symbols.
* `MPOTensor.CZX.omega_eq_lSymbol_ratio`: `ω(g,g,g)` is the ratio of L-symbols for every choice
  of fusion and action tensors, and `MPOTensor.CZX.lSymbol_ratio_mul_omega_eq_neg_one`: that
  ratio times `ω(g,e,g)` is `-1`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker
open TNLean.Algebra MPSTensor MPOTensor.GroupFamily

namespace MPOTensor.CZX

/-! ### The CZX operator squares to the identity -/

private theorem complementSite_complementSite (i : Fin 4) :
    complementSite (complementSite i) = i := by
  revert i
  decide

private theorem complement_complement {N : ℕ} (t : Fin N → Fin 4) :
    complement N (complement N t) = t :=
  funext fun k ↦ complementSite_complementSite (t k)

/-- The exponents of an edge and of its complement differ by the leading bits of its two
sites, modulo two. -/
private theorem edgeExponent_add_complement_mod_two (i j : Fin 4) :
    (edgeExponent i (siteBits j).1 +
        edgeExponent (complementSite i) (siteBits (complementSite j)).1) % 2 =
      ((siteBits i).1.val + (siteBits j).1.val) % 2 := by
  revert i j
  decide

/-- The cyclic exponents of a configuration and of its complement have the same parity. -/
private theorem cyclicExponent_add_complement_mod_two {N : ℕ} [NeZero N]
    (t : Fin N → Fin 4) :
    (cyclicExponent t + cyclicExponent (complement N t)) % 2 = 0 := by
  have hsum : cyclicExponent t + cyclicExponent (complement N t) =
      ∑ j, (edgeExponent (t j) (siteBits (t (j + 1))).1 +
        edgeExponent (complementSite (t j)) (siteBits (complementSite (t (j + 1)))).1) := by
    rw [cyclicExponent, cyclicExponent, ← Finset.sum_add_distrib]
    rfl
  have hshift : ∑ j : Fin N, (siteBits (t (j + 1))).1.val = ∑ j, (siteBits (t j)).1.val :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl
  rw [hsum, Finset.sum_nat_mod]
  simp only [edgeExponent_add_complement_mod_two]
  rw [← Finset.sum_nat_mod, Finset.sum_add_distrib, hshift]
  omega

/-- **The CZX operator squares to the identity** on every periodic chain: it is the monomial
operator of the complement, and the phases of a configuration and of its complement multiply
to one.

Source: arXiv:2502.20257, `eq:MPU_CZX`, `main.tex` lines 4503--4547, the `ℤ₂` matrix product
unitary representation of the CZX example. -/
theorem mpo_tensor_mul_self {N : ℕ} [NeZero N] : mpo tensor N * mpo tensor N = 1 := by
  rw [mpo_tensor, Matrix.monomial_mul_monomial]
  have hσ : complement N * complement N = 1 := Equiv.ext complement_complement
  rw [hσ, ← Matrix.monomial_one]
  congr 1
  funext t
  rw [complement_complement, ← pow_add,
    neg_one_pow_eq_pow_mod_two, cyclicExponent_add_complement_mod_two, pow_zero]

/-! ### The `ℤ₂` family and its fusion tensors -/

/-- **The CZX representation of `ℤ₂`**: the identity is represented by the bond-one identity
tensor and the generator by the once-blocked CZX tensor.

Source: arXiv:2502.20257, `eq:MPU_CZX`, `main.tex` lines 4503--4547. -/
def family : GroupFamily (Multiplicative (ZMod 2)) 4 :=
  GroupFamily.orderTwoFamily (idTensor 4) tensor

/-- **The CZX tensors form a normal representation of `ℤ₂`**: both tensors are normal, and the
periodic operators satisfy `1 · 1 = 1`, `1 · U = U · 1 = U` and `U U = 1` on every nonempty
chain.

Source: arXiv:2502.20257, `eq:MPU_CZX`, `main.tex` lines 4503--4547, with the representation
law of lines 1403--1407. -/
theorem family_isNormalRepresentation : family.IsNormalRepresentation where
  isNormal := Multiplicative.forall_zmod_two idTensor_isNormal tensor_isInjective.isNormal
  operator_mul := by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_) <;> intro N hN
    · change mpo (idTensor 4) N * mpo (idTensor 4) N = mpo (idTensor 4) N
      rw [mpo_idTensor, Matrix.one_mul]
    · change mpo (idTensor 4) N * mpo tensor N = mpo tensor N
      rw [mpo_idTensor, Matrix.one_mul]
    · change mpo tensor N * mpo (idTensor 4) N = mpo tensor N
      rw [mpo_idTensor, Matrix.mul_one]
    · change mpo tensor N * mpo tensor N = mpo (idTensor 4) N
      have : NeZero N := ⟨by omega⟩
      rw [mpo_idTensor, mpo_tensor_mul_self]

private theorem fusion_isReduction_idTensor :
    IsReduction (mulTensor tensor tensor).toMPSTensor (idTensor 4).toMPSTensor fusionV fusionW :=
  fusion_isReduction

/-- **Fusion tensors of the CZX representation**: the identity whenever a factor is the
identity, and the printed caps `F^<_{g,g} = Y`, `F^>_{g,g} = Y / 2` for two generators.

Source: arXiv:2502.20257, equations `eq:fusion_1`, `eq:fusion_2` and `eq:Fgg`, `main.tex`
lines 1403--1498 and 2000--2037, specialized in lines 4671--4689. -/
def fusionData : family.FusionData :=
  GroupFamily.FusionData.orderTwo (idTensor 4) tensor fusionV fusionW
    (by rw [mulTensor_idTensor_left]; rfl) (by rw [mulTensor_idTensor_left]; rfl)
    (by rw [mulTensor_idTensor_right]; rfl) fusion_isReduction_idTensor

/-! ### The anomaly -/

local notation "o₀" => Multiplicative.ofAdd (0 : ZMod 2)
local notation "o₁" => Multiplicative.ofAdd (1 : ZMod 2)

/-- The integer matrices of the once-blocked CZX tensor, in the coordinates of
`MPOTensor.CZX.tensor_apply`. -/
def tensorInt (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ := fun l r ↦
  if i = complementSite j ∧ l = (show Fin 2 from (siteBits i).1) then
    (-1) ^ edgeExponent i r else 0

theorem tensor_eq_complexOfInt :
    tensor = fun i j ↦ complexOfInt (tensorInt i j) := by
  funext i j
  ext l r
  rw [tensor_apply, complexOfInt_apply, tensorInt]
  split_ifs <;> simp

/-- The integer row `(0, 1, -1, 0)`; the printed cap `F^<_{g,g}` is `-i` times it. -/
def fusionVInt : Matrix (Fin 1) (Fin 4) ℤ := !![0, 1, -1, 0]

theorem fusionV_eq_smul : fusionV = (-Complex.I) • complexOfInt fusionVInt := by
  ext a b
  fin_cases a
  fin_cases b <;> simp [fusionV, fusionVInt]

/-- The stacked square of the CZX tensor is the image of the integer stacked square. -/
theorem mulTensor_tensor_eq_complexOfInt :
    mulTensor tensor tensor = fun i j ↦ complexOfInt (mulTensorR tensorInt tensorInt i j) := by
  rw [tensor_eq_complexOfInt]
  exact funext₂ fun i j ↦ mulTensor_complexOfRing _ tensorInt tensorInt i j

/-- The integer letters of the triple product of the CZX tensor. -/
def cubeInt (a : Fin (4 * 4)) : Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ :=
  mulTensorR (mulTensorR tensorInt tensorInt) tensorInt a.divNat a.modNat

/-- The integer letters of the CZX tensor over the pair alphabet. -/
def tensorIntMPS (a : Fin (4 * 4)) : Matrix (Fin 2) (Fin 2) ℤ :=
  tensorInt a.divNat a.modNat

private theorem kronId_smul {m n : ℕ} (c : ℂ) (X : Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    kronId (c • X) D = c • kronId X D := by
  ext r s
  simp [kronId, Matrix.kroneckerMap_apply, mul_assoc]

private theorem idKron_smul {m n : ℕ} (c : ℂ) (D : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    idKron D (c • X) = c • idKron D X := by
  ext r s
  simp [idKron, Matrix.kroneckerMap_apply, mul_left_comm]

private theorem isDressedProportional_smul {d D m : ℕ} {T : MPSTensor d D}
    {L R : Matrix (Fin m) (Fin D) ℂ} {z : ℂ} (c : ℂ) (h : IsDressedProportional T L R z) :
    IsDressedProportional T (c • L) (c • R) z := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun w hw ↦ by rw [Matrix.smul_mul, Matrix.smul_mul, h w hw, smul_comm]⟩

/-- **The associator of three generators is `-1`**: with the printed fusion caps, the tree
fusing the first two generators first is `-1` times the tree fusing the last two first,
against every nonempty word of the triple product.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535, and
the anomaly of lines 4695--4698. -/
theorem fusionData_isAssociator :
    fusionData.IsAssociator orderTwoGen orderTwoGen orderTwoGen ((-1 : ℤ) : ℂ) := by
  unfold GroupFamily.FusionData.IsAssociator
  have hL : fusionData.leftV orderTwoGen orderTwoGen orderTwoGen = kronId fusionV 2 :=
    GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen
  have hR : fusionData.rightV orderTwoGen orderTwoGen orderTwoGen = idKron 2 fusionV :=
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen
  rw [hL, hR, fusionV_eq_smul, kronId_smul,
    idKron_smul, kronId_complexOfRing, idKron_complexOfRing]
  refine isDressedProportional_smul _ ?_
  have hT : (GroupFamily.tripleTensor family orderTwoGen orderTwoGen
      orderTwoGen).toMPSTensor = fun a ↦ complexOfInt (cubeInt a) := by
    funext a
    change mulTensor (mulTensor tensor tensor) tensor a.divNat a.modNat = _
    rw [mulTensor_tensor_eq_complexOfInt, tensor_eq_complexOfInt]
    exact mulTensor_complexOfRing _ _ tensorInt _ _
  rw [hT]
  refine MPSTensor.isDressedProportional_complexOfInt_of_mem (A := tensorIntMPS)
    [(cubeInt 3, tensorIntMPS 3), (cubeInt 6, tensorIntMPS 6), (cubeInt 9, tensorIntMPS 9),
      (cubeInt 12, tensorIntMPS 12), (0, 0)]
    (by decide +kernel) ?_ ?_ ?_ <;>
    decide +kernel

/-- `ω(g,g,g) = -1` for the printed fusion caps.

Source: arXiv:2502.20257, `main.tex` lines 4695--4698. -/
theorem fusionData_omega_gen_gen_gen :
    fusionData.omega orderTwoGen orderTwoGen orderTwoGen = -1 := by
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator family_isNormalRepresentation
    fusionData_isAssociator]
  simp

private theorem omega_eq_one_aux {h₁ h₂ h₃ : Multiplicative (ZMod 2)}
    (h : fusionData.leftV h₁ h₂ h₃ = fusionData.rightV h₁ h₂ h₃) :
    fusionData.omega h₁ h₂ h₃ = 1 :=
  GroupFamily.FusionData.omega_eq_one_of_leftV_eq_rightV family_isNormalRepresentation h

theorem kronId_fusionV_one : kronId fusionV 1 = fusionV := by
  ext r c
  fin_cases r
  fin_cases c <;> simp [kronId, fusionV, finProdFinEquiv, Fin.divNat, Fin.modNat]

private theorem idKron_one_fusionV : idKron 1 fusionV = fusionV := by
  ext r c
  fin_cases r
  fin_cases c <;> simp [idKron, fusionV, finProdFinEquiv, Fin.divNat, Fin.modNat]

private theorem fusionV_mul_idKron_one :
    fusionV * idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) = fusionV := by
  rw [idKron_one, Matrix.mul_one]

/-- **The displayed anomaly**: with the printed fusion caps,
`ω(h₁,h₂,h₃) = (-1)^(δ_{h₁,g} δ_{h₂,g} δ_{h₃,g})`.

Source: arXiv:2502.20257, `main.tex` lines 4695--4698. -/
theorem fusionData_omega (h₁ h₂ h₃ : Multiplicative (ZMod 2)) :
    fusionData.omega h₁ h₂ h₃ =
      if h₁ = orderTwoGen ∧ h₂ = orderTwoGen ∧ h₃ = orderTwoGen then -1 else 1 := by
  revert h₁ h₂ h₃
  refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two
    (Multiplicative.forall_zmod_two ?_ ?_) (Multiplicative.forall_zmod_two ?_ ?_))
    (Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_))
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₀ o₀ o₀).symm =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) * kronId (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) *
        ((1 : Matrix (Fin 1) (Fin 1) ℂ) * idKron 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) *
          mulTensorAssocInvMatrix 1 1 1)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one]
    simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₀ o₀ o₁).symm =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId (1 : Matrix (Fin 1) (Fin 1) ℂ) 2 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) * idKron 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) *
          mulTensorAssocInvMatrix 1 1 2)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one]
    simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₀ o₁ o₀).symm =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) * idKron 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) *
          mulTensorAssocInvMatrix 1 2 1)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one]
    simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₀ o₁ o₁).symm =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change fusionV * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) *
        ((1 : Matrix (Fin 1) (Fin 1) ℂ) * idKron 1 fusionV * mulTensorAssocInvMatrix 1 2 2)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one, idKron_one_fusionV]
    simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₁ o₀ o₀).symm =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) * idKron 2 (1 : Matrix (Fin 1) (Fin 1) ℂ) *
          mulTensorAssocInvMatrix 2 1 1)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one]
    simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    exact GroupFamily.FusionData.orderTwo_omega_gen_one_gen family_isNormalRepresentation
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide))]
    refine omega_eq_one_aux ?_
    have hc : family.castMat (mul_assoc o₁ o₁ o₀).symm =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [GroupFamily.castMat_eq_finCongr]
      exact finCongr_toMatrix_eq_one _
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) * kronId fusionV 1 =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) *
        (fusionV * idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) * mulTensorAssocInvMatrix 2 2 1)
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one, kronId_fusionV_one,
      fusionV_mul_idKron_one]
    simp
  · rw [ite_eq_left_iff.mpr (fun h ↦ absurd (by decide) h)]
    exact fusionData_omega_gen_gen_gen

/-! ### The anomaly class -/

/-- **For every choice of fusion tensors** of the CZX representation, the gauge-invariant
product `ω(g,e,g) ω(g,g,g)` is `-1`.

Source: arXiv:2502.20257, `eq:omegagauge`, `main.tex` lines 1541--1546, and lines
4695--4698. -/
theorem cyclicInvariant_omega (fd : family.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega orderTwoGen 2 = -1 := by
  apply Units.ext
  have h := GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq_orderTwo fd
    family_isNormalRepresentation (MonoidHom.id _) rfl fusionData_isAssociator
  simpa using h

/-- **The CZX representation is anomalous**: for every choice of fusion tensors, the anomaly
three-cocycle is not cohomologous to the trivial one.

Source: arXiv:2502.20257, `main.tex` lines 4695--4699 and `eq:omegagauge`. -/
theorem not_isTrivialGaugeClass_omega (fd : family.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one
    orderTwoGen_pow_two ?_
  rw [cyclicInvariant_omega]
  intro h
  have := congrArg Units.val h
  norm_num at this

/-- The anomaly class of the CZX representation in `H³(ℤ₂, ℂˣ)` is nonzero.

Source: arXiv:2502.20257, `main.tex` lines 4695--4699. -/
theorem family_anomalyClass_ne_zero : family_isNormalRepresentation.anomalyClass ≠ 0 := fun h ↦
  not_isTrivialGaugeClass_omega family_isNormalRepresentation.nonempty_fusionData.some
    ((GroupFamily.FusionData.isTrivialGaugeClass_omega_iff _ _).2 h)

/-! ### The two blocked GHZ sectors -/

/-- The once-blocked GHZ sectors `|00⟩` and `|11⟩`, indexed by `ℤ₂` acting on itself.

Source: arXiv:2502.20257, `main.tex` lines 4660--4670. -/
def block (x : Multiplicative (ZMod 2)) : MPSTensor 4 1 :=
  blockedSector (Multiplicative.toAdd x)

theorem block_apply (x : Multiplicative (ZMod 2)) (i : Fin 4) :
    block x i = if i = finProdFinEquiv (Multiplicative.toAdd x, Multiplicative.toAdd x) then 1
      else 0 :=
  blockTensor_ghzSectorTensor_apply _ i

/-- Both blocked GHZ sectors are normal: one letter is the identity. -/
theorem block_isNormal (x : Multiplicative (ZMod 2)) : Kraus.IsNormal (block x) := by
  refine ⟨1, one_pos, Submodule.eq_top_of_forall_single_mem _ fun i j ↦ ?_⟩
  have hij : Matrix.single i j (1 : ℂ) = 1 := by
    ext r c
    simp [Subsingleton.elim i r, Subsingleton.elim j c, Subsingleton.elim r c, Matrix.one_apply]
  rw [hij]
  refine Submodule.subset_span ⟨fun _ ↦ finProdFinEquiv (Multiplicative.toAdd x,
    Multiplicative.toAdd x), ?_⟩
  simp [block_apply]

private theorem evalWord_blockedSector (x : Fin 2) (w : List (Fin 4)) :
    Kraus.evalWord (blockedSector x) w =
      if ∀ i ∈ w, i = finProdFinEquiv (x, x) then 1 else 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih, show blockedSector x i = _ from
      blockTensor_ghzSectorTensor_apply x i]
    by_cases hi : i = finProdFinEquiv (x, x) <;> simp [hi]

private theorem mpv_blockedSector (x : Fin 2) {N : ℕ} :
    (fun σ : Fin N → Fin 4 ↦ MPSTensor.mpv (blockedSector x) σ) =
      Pi.single (fun _ ↦ finProdFinEquiv (x, x)) 1 := by
  funext σ
  rw [MPSTensor.mpv, MPSTensor.coeff, evalWord_blockedSector]
  by_cases h : σ = fun _ ↦ finProdFinEquiv (x, x)
  · subst h
    simp
  · have h' : ¬ ∀ a, σ a = finProdFinEquiv (x, x) := fun h' ↦ h (funext h')
    rw [Pi.single_eq_of_ne h]
    simp [h']

private theorem mpo_tensor_mulVec_blockedSector {N : ℕ} [NeZero N] (x : Fin 2) :
    mpo tensor N *ᵥ (fun σ : Fin N → Fin 4 ↦ MPSTensor.mpv (blockedSector x) σ) =
      fun σ ↦ MPSTensor.mpv (blockedSector (1 - x)) σ := by
  rw [mpv_blockedSector, mpv_blockedSector, mpo_tensor, Matrix.monomial_mulVec_single]
  have hc : complement N (fun _ ↦ finProdFinEquiv (x, x)) =
      fun _ ↦ finProdFinEquiv (1 - x, 1 - x) :=
    funext fun _ ↦ (by decide : ∀ y : Fin 2,
      complementSite (finProdFinEquiv (y, y)) = finProdFinEquiv (1 - y, 1 - y)) x
  rw [hc, cyclicPhase_ghz_constant, one_smul]

/-- **The CZX representation permutes the two blocked GHZ sectors**: the identity fixes them,
and the CZX operator exchanges them with phase one at every positive length.

Source: arXiv:2502.20257, `main.tex` lines 4660--4670. -/
theorem carriesMPV (g x : Multiplicative (ZMod 2)) :
    CarriesMPV (family.tensor g) (block x) (block (g • x)) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  revert g x
  refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
    (Multiplicative.forall_zmod_two ?_ ?_)
  · change mpo (idTensor 4) N *ᵥ _ = _
    rw [mpo_idTensor, Matrix.one_mulVec]
    rfl
  · change mpo (idTensor 4) N *ᵥ _ = _
    rw [mpo_idTensor, Matrix.one_mulVec]
    rfl
  · exact mpo_tensor_mulVec_blockedSector 0
  · exact mpo_tensor_mulVec_blockedSector 1

/-! ### The action tensors -/

/-- The action tensor of the CZX tensor on a blocked GHZ sector is the acted sector of
`MPOTensor.CZX.actedSector`. -/
theorem actTensor_tensor_blockedSector (x : Fin 2) :
    actTensor tensor (blockedSector x) = actedSector x := by
  funext i
  ext l r
  fin_cases l <;> fin_cases r <;>
    simp [actTensor_apply, actedSector, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- The left action tensors: the trivial identification for the identity, and the bra of
lines 4690--4694 dressed by one acted letter for the generator. -/
def actionV : (a s : Fin 2) → Matrix (Fin 1) (Fin (orderTwoBondDim a * 1)) ℂ
  | ⟨0, _⟩, _ => (finCongr (one_mul 1)).symm.toPEquiv.toMatrix
  | ⟨1, _⟩, s => dressedActionBra s
  | ⟨n + 2, h⟩, _ => absurd h (by omega)

/-- The right action tensors: the trivial identification for the identity, and the ket of
lines 4690--4694 for the generator. -/
def actionW : (a s : Fin 2) → Matrix (Fin (orderTwoBondDim a * 1)) (Fin 1) ℂ
  | ⟨0, _⟩, _ => (finCongr (one_mul 1)).toPEquiv.toMatrix
  | ⟨1, _⟩, s => printedActionKet s
  | ⟨n + 2, h⟩, _ => absurd h (by omega)

/-- **Action tensors of the CZX representation on the two blocked GHZ sectors.**

Source: arXiv:2502.20257, `eq:action_interior`, `main.tex` lines 1841--1870, with the action
tensors of lines 4690--4694; the bra is dressed by one acted letter
(`MPOTensor.CZX.dressedActionBra`), which agrees with the printed bra against every nonempty
word. -/
def blockActionData : BlockActionData family block where
  V g x := actionV (Multiplicative.toAdd g) (Multiplicative.toAdd x)
  W g x := actionW (Multiplicative.toAdd g) (Multiplicative.toAdd x)
  isReduction := by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_)
    · exact isReduction_actTensor_idTensor (block (Multiplicative.ofAdd 0))
    · exact isReduction_actTensor_idTensor (block (Multiplicative.ofAdd 1))
    · change IsReduction (actTensor tensor (blockedSector 0)) (actionTarget 0)
        (dressedActionBra 0) (printedActionKet 0)
      rw [actTensor_tensor_blockedSector]
      exact dressedAction_isReduction 0
    · change IsReduction (actTensor tensor (blockedSector 1)) (actionTarget 1)
        (dressedActionBra 1) (printedActionKet 1)
      rw [actTensor_tensor_blockedSector]
      exact dressedAction_isReduction 1

/-! ### The L-symbols -/

/-- A dressed identity on every letter is a dressed identity on every nonempty word. -/
private theorem isDressedProportional_of_forall_letter {d D m : ℕ} {B : MPSTensor d D}
    {X Y : Matrix (Fin m) (Fin D) ℂ} {z : ℂ} (h : ∀ a, X * B a = z • (Y * B a)) :
    IsDressedProportional B X Y z :=
  ⟨1, fun w hw ↦ by
    obtain ⟨a, w, rfl⟩ := List.exists_cons_of_length_pos hw
    rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, h a, Matrix.smul_mul, Matrix.mul_assoc]⟩

private theorem castIndex_const {ι : Type*} {n : ℕ} {a b : ι} (e : a = b) :
    castIndex (fun _ : ι ↦ n) e = (1 : Matrix (Fin n) (Fin n) ℂ) :=
  finCongr_toMatrix_eq_one _

private theorem finCongr_one_mul_one_toMatrix :
    ((finCongr (one_mul 1)).symm.toPEquiv.toMatrix : Matrix (Fin 1) (Fin (1 * 1)) ℂ) = 1 := by
  rw [finCongr_symm]
  exact finCongr_toMatrix_eq_one _

/-- The integer letters of a blocked GHZ sector. -/
def blockInt (x : Fin 2) (i : Fin 4) : Matrix (Fin 1) (Fin 1) ℤ :=
  if i = finProdFinEquiv (x, x) then 1 else 0

/-- The integer letters of the stacked square of the CZX tensor acting on a blocked GHZ
sector. -/
def pairActionInt (x : Fin 2) (i : Fin 4) : Matrix (Fin (2 * 2 * 1)) (Fin (2 * 2 * 1)) ℤ :=
  actTensorR (mulTensorR tensorInt tensorInt) (blockInt x) i

theorem actTensor_mulTensor_blockedSector (x : Fin 2) :
    actTensor (mulTensor tensor tensor) (blockedSector x) =
      fun i ↦ complexOfInt (pairActionInt x i) := by
  have hA : blockedSector x = fun i ↦ complexOfInt (blockInt x i) := by
    funext i
    rw [show blockedSector x i = _ from blockTensor_ghzSectorTensor_apply x i]
    ext r c
    fin_cases r
    fin_cases c
    by_cases hi : i = finProdFinEquiv (x, x) <;> simp [blockInt, hi]
  funext i
  rw [mulTensor_tensor_eq_complexOfInt, hA]
  exact actTensor_complexOfRing _ _ _ i

/-- The integer row `(1, -1, 1, -1)` for the sector `|00⟩` and `(1, 1, -1, -1)` for the sector
`|11⟩`; the two successive action bras are `i` times it. -/
def successiveActionInt (x : Fin 2) : Matrix (Fin 1) (Fin 4) ℤ :=
  if x = 0 then !![1, -1, 1, -1] else !![1, 1, -1, -1]

/-- The bra of two successive actions of the generator. -/
theorem actV_gen_gen (x : Fin 2) :
    blockActionData.actV orderTwoGen orderTwoGen (Multiplicative.ofAdd x) =
      Complex.I • complexOfInt (successiveActionInt x) := by
  have h : ∀ x : Fin 2, dressedActionBra (1 - x) * idKron 2 (dressedActionBra x) *
      mulTensorAssocInvMatrix 2 2 1 = Complex.I • complexOfInt (successiveActionInt x) := by
    intro x
    rw [mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one, Matrix.mul_one]
    ext i j
    fin_cases i
    fin_cases x <;> fin_cases j <;>
      simp [dressedActionBra, printedActionBra, actionMatrix_coordinates.1,
        actionMatrix_coordinates.2, idKron, successiveActionInt, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat,
        Matrix.one_apply]
  fin_cases x
  · exact h 0
  · exact h 1

/-- The bra of the fusion of two generators followed by the trivial action. -/
theorem fuseV_gen_gen (x : Multiplicative (ZMod 2)) :
    blockActionData.fuseV fusionData orderTwoGen orderTwoGen x = fusionV := by
  have h : castIndex (fun _ : Multiplicative (ZMod 2) ↦ 1) (mul_smul orderTwoGen orderTwoGen x) *
      (((finCongr (one_mul 1)).symm.toPEquiv.toMatrix : Matrix (Fin 1) (Fin (1 * 1)) ℂ) *
        kronId fusionV 1) = fusionV := by
    rw [castIndex_const, finCongr_one_mul_one_toMatrix, kronId_fusionV_one, Matrix.one_mul,
      Matrix.one_mul]
  exact h

/-- The integer form of the dressed identities of the two generators: on every letter, the
successive action row is `∓` the fusion row. -/
private theorem successiveActionInt_mul_pairActionInt (x : Fin 2) (i : Fin 4) :
    successiveActionInt x * pairActionInt x i =
      (-(if x = 0 then 1 else -1 : ℤ)) • (fusionVInt * pairActionInt x i) := by
  revert x i
  decide +kernel

/-- **The L-symbols of two generators**: against every nonempty word, the two successive
actions of the generator on the sector `x` are `(-1)^x` times the fusion of the two generators
followed by the trivial action.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913, with the fusion and action
tensors of lines 4671--4694. -/
theorem isDressedProportional_actV_fuseV_gen_gen (x : Fin 2) :
    IsDressedProportional
      (actTensor (mulTensor (family.tensor orderTwoGen) (family.tensor orderTwoGen))
        (block (Multiplicative.ofAdd x)))
      (blockActionData.actV orderTwoGen orderTwoGen (Multiplicative.ofAdd x))
      (blockActionData.fuseV fusionData orderTwoGen orderTwoGen (Multiplicative.ofAdd x))
      (if x = 0 then 1 else -1) := by
  rw [actV_gen_gen, fuseV_gen_gen]
  change IsDressedProportional (actTensor (mulTensor tensor tensor) (blockedSector x)) _ _ _
  rw [actTensor_mulTensor_blockedSector]
  refine isDressedProportional_of_forall_letter fun i ↦ ?_
  rw [fusionV_eq_smul, Matrix.smul_mul, Matrix.smul_mul, ← complexOfInt_mul, ← complexOfInt_mul,
    successiveActionInt_mul_pairActionInt, complexOfInt_zsmul, smul_smul, smul_smul]
  congr 1
  fin_cases x <;> simp

/-- The L-symbols at the identity element are one: the bras of the trivial action and of the
trivial fusion agree. -/
theorem lSymbol_one_one (x : Multiplicative (ZMod 2)) :
    blockActionData.lSymbol fusionData x 1 1 = 1 := by
  have h : ((finCongr (one_mul 1)).symm.toPEquiv.toMatrix : Matrix (Fin 1) (Fin (1 * 1)) ℂ) *
      idKron 1 ((finCongr (one_mul 1)).symm.toPEquiv.toMatrix : Matrix (Fin 1) (Fin (1 * 1)) ℂ) *
      mulTensorAssocInvMatrix 1 1 1 =
    castIndex (fun _ : Multiplicative (ZMod 2) ↦ 1)
        (mul_smul (1 : Multiplicative (ZMod 2)) 1 x) *
      (((finCongr (one_mul 1)).symm.toPEquiv.toMatrix : Matrix (Fin 1) (Fin (1 * 1)) ℂ) *
        kronId (1 : Matrix (Fin 1) (Fin 1) ℂ) 1) := by
    rw [castIndex_const, finCongr_one_mul_one_toMatrix, kronId_one, idKron_one,
      mulTensorAssocInvMatrix_eq_finCongr, finCongr_toMatrix_eq_one]
    simp
  have hact : blockActionData.actV 1 1 x = blockActionData.fuseV fusionData 1 1 x := h
  apply Units.ext
  rw [Units.val_one, ← BlockActionData.eq_lSymbol_of_isDressedProportional block_isNormal
    (fun _ ↦ one_pos) carriesMPV (z := 1)]
  rw [hact]
  exact IsDressedProportional.refl _ _

/-- The L-symbols of the CZX representation on the two blocked GHZ sectors are compatible with
its anomaly.

Source: arXiv:2502.20257, `eq:omega_and_Ls`, `main.tex` lines 1920--1923. -/
theorem blockActionData_isCompatible :
    LSymbol.IsCompatible (blockActionData.lSymbol fusionData) fusionData.omega :=
  blockActionData.isCompatible_lSymbol family_isNormalRepresentation block_isNormal
    (fun _ ↦ one_pos) carriesMPV

/-- **The L-symbols of the CZX representation on the two blocked GHZ sectors**: with the
printed fusion caps and the action tensors of lines 4690--4694, every L-symbol is one except at
two generators, where `L⁰_{g,g} = 1` on `|00⟩` and `L¹_{g,g} = -1` on `|11⟩`, with the
orientation of the caps of the module docstring.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913, and lines 4671--4699. -/
theorem blockActionData_lSymbol (x g h : Multiplicative (ZMod 2)) :
    (blockActionData.lSymbol fusionData x g h : ℂ) =
      if g = orderTwoGen ∧ h = orderTwoGen then (-1) ^ (Multiplicative.toAdd x).val else 1 := by
  have hc := blockActionData_isCompatible
  have hω : ∀ a b c : Multiplicative (ZMod 2), ¬ (a = orderTwoGen ∧ b = orderTwoGen ∧
      c = orderTwoGen) → fusionData.omega a b c = 1 := fun a b c habc ↦ by
    rw [fusionData_omega, ite_eq_right_iff.mpr fun h ↦ absurd h habc]
  have hee : ∀ y, blockActionData.lSymbol fusionData y 1 1 = 1 := lSymbol_one_one
  -- The compatibility relation at `(e, e, g)` and at `(g, e, e)` reduces the remaining
  -- L-symbols at the identity to `L^y_{e,e} = 1`.
  have heg : ∀ y, blockActionData.lSymbol fusionData y 1 orderTwoGen = 1 := fun y ↦ by
    have h := hc y 1 1 orderTwoGen
    simp only [one_mul, hee, hω 1 1 orderTwoGen (by decide)] at h
    simpa using h
  have hge : ∀ y, blockActionData.lSymbol fusionData y orderTwoGen 1 = 1 := fun y ↦ by
    have h := hc y orderTwoGen 1 1
    simp only [mul_one, one_mul, one_smul, hee, hω orderTwoGen 1 1 (by decide)] at h
    simpa using h
  have hgg : ∀ y : ZMod 2, (blockActionData.lSymbol fusionData (Multiplicative.ofAdd y)
      orderTwoGen orderTwoGen : ℂ) = if y = 0 then 1 else -1 := fun y ↦
    (BlockActionData.eq_lSymbol_of_isDressedProportional block_isNormal (fun _ ↦ one_pos)
      carriesMPV (isDressedProportional_actV_fuseV_gen_gen y)).symm
  by_cases hgh : g = orderTwoGen ∧ h = orderTwoGen
  · obtain ⟨rfl, rfl⟩ := hgh
    simp only [and_self, ite_true]
    revert x
    refine Multiplicative.forall_zmod_two ?_ ?_
    · exact (hgg 0).trans (by simp)
    · exact (hgg 1).trans (by rw [show (Multiplicative.toAdd (Multiplicative.ofAdd
        (1 : ZMod 2))).val = 1 from rfl]; simp)
  · rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' hgh]
    refine Units.val_eq_one.mpr ?_
    revert hgh
    revert g h
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_) <;> intro hgh
    · exact hee x
    · exact heg x
    · exact hge x
    · exact absurd ⟨rfl, rfl⟩ hgh

/-- **The anomaly as a ratio of L-symbols**: for every choice of fusion tensors and every
choice of action tensors on the two blocked GHZ sectors,
`ω(g,g,g) = Lˣ_{g,g} Lˣ_{g,e} / (L^{g • x}_{g,g} Lˣ_{e,g})`, the relation of line 5121.

Source: arXiv:2502.20257, `eq:omega_and_Ls`, `main.tex` lines 1920--1923, at `(g, g, g)`, as
in line 5121. -/
theorem omega_eq_lSymbol_ratio (fd : family.FusionData) (ad : BlockActionData family block)
    (x : Multiplicative (ZMod 2)) :
    fd.omega orderTwoGen orderTwoGen orderTwoGen =
      ad.lSymbol fd x orderTwoGen orderTwoGen * ad.lSymbol fd x orderTwoGen 1 /
        (ad.lSymbol fd (orderTwoGen • x) orderTwoGen orderTwoGen *
          ad.lSymbol fd x 1 orderTwoGen) :=
  LSymbol.eq_div_of_isCompatible_of_mul_self_eq_one
    (ad.isCompatible_lSymbol family_isNormalRepresentation block_isNormal (fun _ ↦ one_pos)
      carriesMPV)
    x (by decide)

/-- **The L-symbol ratio is the anomaly for every choice**: for every choice of fusion tensors
and action tensors, `(L⁰_{g,g} L⁰_{g,e} / (L¹_{g,g} L⁰_{e,g})) ω(g,e,g) = ω(g,g,g) ω(g,e,g)`,
and this gauge-invariant product is `-1`. With action and fusion tensors trivial at the
identity, this is `L⁰_{g,g} / L¹_{g,g} = -1`; no gauge transformation makes both L-symbols one
(line 4699).

Source: arXiv:2502.20257, `main.tex` lines 4695--4699 and 5121. -/
theorem lSymbol_ratio_mul_omega_eq_neg_one (fd : family.FusionData)
    (ad : BlockActionData family block) :
    ad.lSymbol fd 1 orderTwoGen orderTwoGen * ad.lSymbol fd 1 orderTwoGen 1 /
        (ad.lSymbol fd orderTwoGen orderTwoGen orderTwoGen * ad.lSymbol fd 1 1 orderTwoGen) *
      fd.omega orderTwoGen 1 orderTwoGen = -1 := by
  have hr := omega_eq_lSymbol_ratio fd ad 1
  rw [smul_eq_mul, mul_one] at hr
  rw [← hr, mul_comm]
  have h := cyclicInvariant_omega fd
  simpa [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ] using h

end MPOTensor.CZX
