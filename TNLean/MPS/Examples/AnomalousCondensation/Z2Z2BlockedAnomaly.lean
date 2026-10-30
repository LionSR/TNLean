/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalReindexTransport
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.Examples.AnomalousCondensation.Z2Z2AnomalyClass
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.Wielandt.RectangularSpan.Basic

/-!
# The original condensation symmetry after two-site blocking

The four original two-qubit tensors multiply with the projective factor
`λ(g,h)^N`, where `λ(g,h) = (-1)^(g₁ h₂)`. Blocking two physical sites
removes this factor on every nonempty blocked ring. This is the original
family, rather than the diagonally dressed family of `Z2Z2AnomalyClass`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1845–1886,
especially the type-II row of the table. The explicit two-qubit tensors and
their compression witnesses are constructions of this repository; the source
does not print them. The associator convention is that of arXiv:2502.20257,
the display preceding `eq:3-cocycle`.

The original square-compression witnesses become fusion tensors after
blocking. The raw triple letters directly compare the two fusion trees with
signs `+1` for `x` and `−1` for `xy`; the `y` restriction has bond dimension
one. Restriction and fusion-gauge invariance give these detectors for every
fusion choice, and `KleinCocycleCompleteness` identifies the class.

## Main results

* `blockedFamily_isNormalRepresentation`: exactness of the blocked family.
* `omega_blockedFamily_cohomologousTo_kleinCocycle`: its type-II class for every fusion choice.
* `not_isTrivialGaugeClass_omega_blockedFamily`: nontriviality of that class.
* `raw_odd_square_ne_identity`: the retained obstruction on raw odd rings.
-/

noncomputable section

open scoped Matrix Kronecker
open MPOTensor MPSTensor TNLean.Algebra

namespace Z2Z2Condensation

/-- Two original physical sites per blocked site, with the original bond dimension. -/
def blockedTensor (g : Multiplicative (ZMod 2 × ZMod 2)) :
    MPOTensor (MPSTensor.blockPhysDim 4 2) (bondDim (MPOTensor.GroupCocycle.kleinEquiv g)) :=
  MPOTensor.blockTensor (symTensor (MPOTensor.GroupCocycle.kleinEquiv g)) 2

/-- The two-site-blocked original family. -/
def blockedFamily : GroupFamily (Multiplicative (ZMod 2 × ZMod 2))
    (MPSTensor.blockPhysDim 4 2) where
  bondDim g := bondDim (MPOTensor.GroupCocycle.kleinEquiv g)
  bondDim_pos g := kleinFamily.bondDim_pos g
  tensor := blockedTensor

/-- One blocked ring of length `N` is the original ring of length `2N`, with
its physical configurations regrouped in pairs. -/
theorem mpo_blockedTensor (g : Multiplicative (ZMod 2 × ZMod 2)) (N : ℕ) :
    mpo (blockedTensor g) N =
      Matrix.reindex (MPSTensor.blockedConfigEquiv 4 N 2).symm
        (MPSTensor.blockedConfigEquiv 4 N 2).symm
        (mpo (symTensor (MPOTensor.GroupCocycle.kleinEquiv g)) (N * 2)) :=
  mpo_blockTensor_eq_reindex _ 2 N

/-- The projective factor, in group coordinates. -/
theorem fusionSign_kleinEquiv (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    fusionSign (MPOTensor.GroupCocycle.kleinEquiv g) (MPOTensor.GroupCocycle.kleinEquiv h) =
      (-1 : ℂ) ^ (g.toAdd.1.val * h.toAdd.2.val) := by
  revert g h
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;>
    refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;>
    first | rfl | (change (-1 : ℂ) = (-1) ^ 1; norm_num)

/-- The original operators multiply exactly on every nonempty even ring. -/
theorem mpo_symTensor_mul_even (g h : Fin 4) (N : ℕ) (hN : 0 < N) :
    mpo (symTensor g) (N * 2) * mpo (symTensor h) (N * 2) =
      mpo (symTensor (gmul g h)) (N * 2) := by
  rw [mpo_symTensor_mul g h _ (by omega)]
  have hs : fusionSign g h ^ 2 = 1 := by
    fin_cases g <;> fin_cases h <;> norm_num [fusionSign]
  rw [Nat.mul_comm N 2, pow_mul, hs, one_pow, one_smul]

/-- The blocked tensors are normal. -/
theorem blockedTensor_isNormal (g : Multiplicative (ZMod 2 × ZMod 2)) :
    Kraus.IsNormal (blockedTensor g).toMPSTensor := by
  rw [blockedTensor, toMPSTensor_blockTensor]
  refine (isNormal_reindexPhysical_equiv _ _).2 ?_
  apply MPSTensor.isNormal_blockTensor _ 2 (by omega)
  rw [← symMPS_eq_toMPSTensor]
  exact symMPS_isNormal _

/-- The original family becomes an exact normal representation after blocking
two physical sites; the raw odd-ring family is not asserted to be exact. -/
theorem blockedFamily_isNormalRepresentation : blockedFamily.IsNormalRepresentation where
  isNormal := blockedTensor_isNormal
  operator_mul g h N hN := by
    change mpo (blockedTensor g) N * mpo (blockedTensor h) N = mpo (blockedTensor (g * h)) N
    simp only [mpo_blockedTensor]
    change (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv 4 N 2).symm) _ *
        (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv 4 N 2).symm) _ =
      (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv 4 N 2).symm) _
    rw [← map_mul, mpo_symTensor_mul_even _ _ N hN, gmul_kleinEquiv,
      Equiv.symm_apply_apply]

/-- The blocked identity acts as the identity on every nonempty blocked ring. -/
theorem mpo_blockedTensor_one (N : ℕ) (hN : 0 < N) : mpo (blockedTensor 1) N = 1 := by
  have : NeZero (N * 2) := ⟨by omega⟩
  rw [mpo_blockedTensor]
  change Matrix.reindex _ _ (mpo (symTensor 0) (N * 2)) = _
  rw [mpo_symTensor_zero]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ _

/-- Inverse group elements give inverse blocked operators. -/
theorem mpo_blockedTensor_mul_inv (g : Multiplicative (ZMod 2 × ZMod 2))
    (N : ℕ) (hN : 0 < N) :
    mpo (blockedTensor g) N * mpo (blockedTensor g⁻¹) N = 1 := by
  exact (blockedFamily_isNormalRepresentation.operator_mul g g⁻¹ N hN).trans
    ((congrArg (fun k ↦ mpo (blockedTensor k) N) (mul_inv_cancel g)).trans
      (mpo_blockedTensor_one N hN))

/-- The raw odd-ring obstruction: the diagonal element squares to `−U_e`,
so this family is not an exact group representation on an odd ring. -/
theorem raw_odd_square_ne_identity {N : ℕ} (hN : Odd N) :
    mpo xyTensor N * mpo xyTensor N ≠ mpo eTensor N := by
  have : NeZero N := ⟨hN.pos.ne'⟩
  rw [mpo_xy_mul_xy N hN.pos, hN.neg_one_pow]
  have he : mpo eTensor N = 1 := mpo_symTensor_zero
  rw [he]
  intro h
  have hh := congrArg (fun M ↦ M (fun _ ↦ 0) (fun _ ↦ 0)) h
  norm_num at hh

private abbrev blockedMPS {D : ℕ} (A : MPSTensor 16 D) :=
  Kraus.reindexPhysical (blockedDoubledIndexEquiv 4 2) (MPSTensor.blockTensor A 2)

private theorem block_pair_eq {D₁ D₂ : ℕ} (A : MPOTensor 4 D₁) (B : MPOTensor 4 D₂)
    (C : MPOTensor 4 (D₁ * D₂)) (h : (mulTensor A B).toMPSTensor = C.toMPSTensor) :
    (mulTensor (MPOTensor.blockTensor A 2) (MPOTensor.blockTensor B 2)).toMPSTensor =
      (MPOTensor.blockTensor C 2).toMPSTensor := by
  rw [← blockTensor_mulTensor, toMPSTensor_blockTensor, toMPSTensor_blockTensor, h]

private theorem block_reduction {D₁ D₂ D₃ : ℕ} (A : MPOTensor 4 D₁)
    (B : MPOTensor 4 D₂) (C : MPSTensor 16 D₃)
    {V : Matrix (Fin D₃) (Fin (D₁ * D₂)) ℂ}
    {W : Matrix (Fin (D₁ * D₂)) (Fin D₃) ℂ}
    (h : IsReduction (mulTensor A B).toMPSTensor C V W) :
    IsReduction (mulTensor (MPOTensor.blockTensor A 2)
      (MPOTensor.blockTensor B 2)).toMPSTensor (blockedMPS C) V W := by
  rw [← blockTensor_mulTensor, toMPSTensor_blockTensor]
  exact (h.blockTensor 2).reindexPhysical _

private theorem block_neg (A : MPSTensor 16 1) : blockedMPS ((-1 : ℂ) • A) = blockedMPS A := by
  funext i
  change Kraus.evalWord (fun j ↦ (-1 : ℂ) • A j)
      (Kraus.wordOfBlock 16 2 (blockedDoubledIndexEquiv 4 2 i)) = _
  rw [Kraus.evalWord_smul, Kraus.length_wordOfBlock]
  norm_num
  rfl

/-- Explicit fusion witnesses for the blocked restriction to `{e,x}`. -/
def blockedXFusionData :
    (GroupFamily.orderTwoFamily (MPOTensor.blockTensor eTensor 2)
      (MPOTensor.blockTensor xTensor 2)).FusionData :=
  GroupFamily.FusionData.orderTwo _ _ xXLeft xXRight
    (block_pair_eq _ _ _ mulTensor_eTensor_eTensor)
    (block_pair_eq _ _ _ (funext eXStacked_eq))
    (block_pair_eq _ _ _ (funext xEStacked_eq))
    (by rw [toMPSTensor_blockTensor eTensor]; exact block_reduction _ _ _ xX_isReduction)

/-- Explicit fusion witnesses for the blocked restriction to `{e,xy}`.
The original square reduces to `−M_e`; its two-site block reduces to `M_e`. -/
def blockedXyFusionData :
    (GroupFamily.orderTwoFamily (MPOTensor.blockTensor eTensor 2)
      (MPOTensor.blockTensor xyTensor 2)).FusionData :=
  GroupFamily.FusionData.orderTwo _ _ xyXyLeft xyXyRight
    (block_pair_eq _ _ _ mulTensor_eTensor_eTensor)
    (block_pair_eq _ _ _ (funext eXyStacked_eq))
    (block_pair_eq _ _ _ (funext xyEStacked_eq))
    (by
      rw [toMPSTensor_blockTensor eTensor]
      change IsReduction _ (blockedMPS eMPS) _ _
      simpa only [block_neg] using block_reduction _ _ _ xyXy_isReduction)

-- Only the sixteen raw letters are checked, never the 256 blocked letters.
private theorem raw_x_tree_letter (a : Fin 16) :
    kronId xXLeft 2 * (mulTensor (mulTensor xTensor xTensor) xTensor).toMPSTensor a =
      (1 : ℂ) • (idKron 2 xXLeft *
        (mulTensor (mulTensor xTensor xTensor) xTensor).toMPSTensor a) := by
  rw [show (mulTensor (mulTensor xTensor xTensor) xTensor).toMPSTensor a = _ from
    triple_complexOfInt xIntTensor a, xXLeft, kronId_complexOfRing, idKron_complexOfRing]
  rw [← complexOfInt_mul, ← complexOfInt_mul, one_smul]
  congr 1
  revert_decide_kernel a

private theorem raw_xy_tree_letter (a : Fin 16) :
    kronId xyXyLeft 2 * (mulTensor (mulTensor xyTensor xyTensor) xyTensor).toMPSTensor a =
      (-1 : ℂ) • (idKron 2 xyXyLeft *
        (mulTensor (mulTensor xyTensor xyTensor) xyTensor).toMPSTensor a) := by
  rw [show (mulTensor (mulTensor xyTensor xyTensor) xyTensor).toMPSTensor a = _ from
    triple_complexOfInt xyIntTensor a, xyXyLeft, kronId_complexOfRing, idKron_complexOfRing]
  rw [← complexOfInt_mul, ← complexOfInt_mul, neg_one_smul, ← complexOfInt_neg]
  congr 1
  revert_decide_kernel a

private theorem block_tree {D m : ℕ} (T : MPOTensor 4 D)
    (L R : Matrix (Fin m) (Fin D) ℂ) (z : ℂ)
    (h : ∀ a, L * T.toMPSTensor a = z • (R * T.toMPSTensor a)) :
    IsDressedProportional (MPOTensor.blockTensor T 2).toMPSTensor L R z := by
  have hw : ∀ w : List (Fin 16), w ≠ [] →
      L * Kraus.evalWord T.toMPSTensor w = z • (R * Kraus.evalWord T.toMPSTensor w) := by
    intro w hne
    cases w with
    | nil => exact (hne rfl).elim
    | cons a w => rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, h,
        Matrix.smul_mul, Matrix.mul_assoc]
  rw [toMPSTensor_blockTensor]
  refine ⟨1, fun w hlen ↦ ?_⟩
  rw [Kraus.evalWord_reindexPhysical, MPSTensor.evalWord_blockTensor]
  apply hw
  intro he
  have hh := MPSTensor.length_flattenBlockedWord 16 2
    (w.map (blockedDoubledIndexEquiv 4 2))
  rw [he, List.length_nil, List.length_map] at hh
  omega

/-- The blocked `x` fusion trees have associator `+1`.
Source: arXiv:2203.12563, type-II row, lines 1856–1872. -/
theorem blockedXFusionData_isAssociator :
    blockedXFusionData.IsAssociator GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen 1 := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [blockedXFusionData, GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen,
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen]
  change IsDressedProportional
    (mulTensor (mulTensor (MPOTensor.blockTensor xTensor 2)
      (MPOTensor.blockTensor xTensor 2)) (MPOTensor.blockTensor xTensor 2)).toMPSTensor _ _ _
  rw [← blockTensor_mulTensor, ← blockTensor_mulTensor]
  exact block_tree _ _ _ _ raw_x_tree_letter

/-- The blocked `xy` fusion trees have associator `−1`.
Source: arXiv:2203.12563, type-II row, lines 1856–1872. -/
theorem blockedXyFusionData_isAssociator :
    blockedXyFusionData.IsAssociator GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen (-1) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [blockedXyFusionData, GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen,
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen]
  change IsDressedProportional
    (mulTensor (mulTensor (MPOTensor.blockTensor xyTensor 2)
      (MPOTensor.blockTensor xyTensor 2)) (MPOTensor.blockTensor xyTensor 2)).toMPSTensor _ _ _
  rw [← blockTensor_mulTensor, ← blockTensor_mulTensor]
  exact block_tree _ _ _ _ raw_xy_tree_letter

private theorem twoFamily_ext {d : ℕ}
    {F F' : GroupFamily (Multiplicative (ZMod 2)) d}
    (hb0 : F.bondDim 1 = F'.bondDim 1)
    (hb1 : F.bondDim GroupFamily.orderTwoGen = F'.bondDim GroupFamily.orderTwoGen)
    (ht0 : HEq (F.tensor 1) (F'.tensor 1))
    (ht1 : HEq (F.tensor GroupFamily.orderTwoGen) (F'.tensor GroupFamily.orderTwoGen)) :
    F = F' := by
  apply GroupFamily.ext_of_heq
  · exact funext (Multiplicative.forall_zmod_two hb0 hb1)
  · exact Multiplicative.forall_zmod_two ht0 ht1

/-- Restriction of the blocked family to `{e,x}`. -/
theorem blockedFamily_comap_xHom :
    blockedFamily.comap xHom = GroupFamily.orderTwoFamily
      (MPOTensor.blockTensor eTensor 2) (MPOTensor.blockTensor xTensor 2) :=
  twoFamily_ext rfl rfl HEq.rfl HEq.rfl

/-- Restriction of the blocked family to `{e,xy}`. -/
theorem blockedFamily_comap_xyHom :
    blockedFamily.comap xyHom = GroupFamily.orderTwoFamily
      (MPOTensor.blockTensor eTensor 2) (MPOTensor.blockTensor xyTensor 2) :=
  twoFamily_ext rfl rfl HEq.rfl HEq.rfl

/-- The blocked restriction to `{e,y}` has bond dimension one. -/
def blockedYFamily : GroupFamily (Multiplicative (ZMod 2)) (MPSTensor.blockPhysDim 4 2) :=
  GroupFamily.ofBondOne fun a ↦ MPOTensor.blockTensor (yLabelTensor a.toAdd) 2

/-- The bond-one restriction has identity fusion matrices. -/
def blockedYFusionData : blockedYFamily.FusionData :=
  GroupFamily.FusionData.ofBondOne _ <| by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_)
    · exact block_pair_eq _ _ _ (funext eEStacked_eq)
    · exact block_pair_eq _ _ _ (funext eYStacked_eq)
    · exact block_pair_eq _ _ _ (funext yEStacked_eq)
    · exact block_pair_eq _ _ _ (funext yYStacked_eq)

/-- Restriction of the blocked family to `{e,y}`. -/
theorem blockedFamily_comap_yHom : blockedFamily.comap yHom = blockedYFamily :=
  twoFamily_ext rfl rfl HEq.rfl HEq.rfl

/-- The `x` detector for every fusion choice of the original blocked family is `+1`. -/
theorem cyclicInvariant_omega_blockedFamily_x (fd : blockedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 0)) 2 = 1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (xHom GroupFamily.orderTwoGen) 2 = 1
  apply Units.ext
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq_orderTwo fd
    blockedFamily_isNormalRepresentation xHom blockedFamily_comap_xHom
    blockedXFusionData_isAssociator]
  simp

/-- The `xy` detector for every fusion choice of the original blocked family is `−1`. -/
theorem cyclicInvariant_omega_blockedFamily_xy (fd : blockedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 1)) 2 = -1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (xyHom GroupFamily.orderTwoGen) 2 = -1
  apply Units.ext
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq_orderTwo fd
    blockedFamily_isNormalRepresentation xyHom blockedFamily_comap_xyHom
    blockedXyFusionData_isAssociator]
  norm_num

private theorem cyclicInvariant_blocked_yHom (fd : blockedFamily.FusionData)
    (a : Multiplicative (ZMod 2)) :
    ScalarThreeCochain.cyclicInvariant fd.omega (yHom a) 2 = 1 := by
  have ha : a ^ 2 = 1 := by revert a; decide
  have hy : blockedYFamily.IsNormalRepresentation :=
    blockedFamily_comap_yHom ▸ blockedFamily_isNormalRepresentation.comap yHom
  have h1 : blockedYFusionData.omega = 1 := GroupFamily.FusionData.omega_ofBondOne hy
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd yHom
    blockedFamily_isNormalRepresentation blockedFamily_comap_yHom blockedYFusionData ha, h1]
  simp [ScalarThreeCochain.cyclicInvariant]

/-- The `y` detector for every fusion choice of the original blocked family is `+1`. -/
theorem cyclicInvariant_omega_blockedFamily_y (fd : blockedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (0, 1)) 2 = 1 :=
  cyclicInvariant_blocked_yHom fd GroupFamily.orderTwoGen

/-- Every cyclic detector of the blocked family agrees with the type-II cocycle.
The values are computed from the blocked fusion witnesses above. -/
theorem cyclicInvariant_omega_blockedFamily (fd : blockedFamily.FusionData)
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ScalarThreeCochain.cyclicInvariant fd.omega g 2 =
      ScalarThreeCochain.cyclicInvariant ScalarThreeCochain.kleinCocycle g 2 := by
  rw [cyclicInvariant_kleinCocycle]
  revert g
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  · exact cyclicInvariant_blocked_yHom fd 1
  · exact cyclicInvariant_omega_blockedFamily_y fd
  · exact cyclicInvariant_omega_blockedFamily_x fd
  · rw [cyclicInvariant_omega_blockedFamily_xy fd]
    simp [ZMod.val_one]

/-- The original two-site-blocked family has the mixed type-II class for every
choice of fusion tensors. Source: arXiv:2203.12563, lines 1845–1886. -/
theorem omega_blockedFamily_cohomologousTo_kleinCocycle (fd : blockedFamily.FusionData) :
    ScalarThreeCochain.CohomologousTo fd.omega ScalarThreeCochain.kleinCocycle :=
  (ScalarThreeCochain.cohomologousTo_iff_klein_cyclicInvariant_eq
    (fd.isCocycle_omega blockedFamily_isNormalRepresentation)
    ScalarThreeCochain.kleinCocycle_isCocycle).2 (cyclicInvariant_omega_blockedFamily fd)

/-- The anomaly of the original blocked family is nontrivial for every fusion choice. -/
theorem not_isTrivialGaugeClass_omega_blockedFamily (fd : blockedFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one
    (g := Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) (n := 2) (by decide) ?_
  rw [cyclicInvariant_omega_blockedFamily_xy]
  intro h
  have := congrArg Units.val h
  norm_num at this

end Z2Z2Condensation
