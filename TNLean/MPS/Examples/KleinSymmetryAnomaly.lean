/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KleinCocycleCompleteness
import TNLean.Algebra.LSymbol
import TNLean.Algebra.ScalarThreeCocycleGroupCohomology
import TNLean.MPS.Examples.CZX.CZXAnomalyClass
import TNLean.MPS.Examples.KleinSymmetry
import TNLean.MPS.MPDO.BondOneOperator
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorComap
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorOrderTwo
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# The anomaly of the printed Klein symmetry

The tensors for the operators printed in arXiv:2203.12563, Section 6,
`Papers/2203.12563/REsubmission.tex` lines 1884–1886, form a normal representation of
`ℤ₂ × ℤ₂ = {e, a, b, ab}`. For every choice of fusion tensors, its anomaly three-cochain is
cohomologous to the representative `(ω_I^{(1)})^0 (ω_I^{(2)})^0 (ω_II)^1` of the row `(0,0,1)`
of the table at lines 1856–1872, so every normalized representative has diagonal values
`(ω_a, ω_b, ω_ab) = (+1, +1, -1)`.

The cyclic invariant `ω(g,e,g) ω(g,g,g)` at each element of order two is computed on the
restriction to the subgroup it generates
(`MPOTensor.GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq`):

* on `{e, ab}` the family is the decorated CZX family, with invariant `-1`;
* on `{e, a}` the stacked square of the bond-two diagonal tensor reduces to the identity
  tensor through `⟨00|` and `|00⟩ + |11⟩`, and the two fusion trees of three copies agree, so
  the invariant is `+1`;
* on `{e, b}` all tensors have bond dimension one, so the invariant is `+1`.

The complete classification of Klein three-cocycles then identifies the class. For
normalized L-symbols compatible with a normalized representative, the diagonal values give
`Lˣ_{g,g} = ω_g L^{g·x}_{g,g}` for `g = a, b, ab`.

**Local fix (diagonal reading):** the source states that "the only non-trivial 3-cocycle
element is `ω(ab,ab,ab) = -1`". Read entrywise this fails the cocycle equation; it is read
through the diagonal values `ω_g = ω(g,g,g)` that the source uses to label classes
(line 1852). The source attaches the L-symbol relations for `a` and `b` to the phases
`H = H_a` and `H = H_b`; the relation forced by the cocycle relates the two blocks exchanged
by the generator. Documented in `docs/paper-gaps/glm23_klein_printed_anomaly_scope.tex`.
-/

noncomputable section

open CZXCompression MPOTensor MPSTensor TNLean.Algebra

namespace KleinSymmetry

/-- The diagonal tensor is normal: flipping the input permutes its word alphabet.
Source: arXiv:2203.12563, line 1884. -/
theorem tensorA_isNormal : Kraus.IsNormal tensorA.toMPSTensor := by
  obtain ⟨n, hn, h⟩ := czxDecoratedMPS_isNormal
  refine ⟨n, hn, ?_⟩
  apply top_unique
  rw [← h]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun i ↦ finProdFinEquiv ((w i).divNat, (w i).modNat.rev), ?_⟩
  simp only [MPSTensor.evalWord_ofFn_eq_prod]
  congr 1
  congr 1
  funext i
  generalize w i = a
  fin_cases a <;> rfl

/-- Bond dimension for the printed Klein tensors (arXiv:2203.12563, line 1884). -/
def printedBond (g : Multiplicative (ZMod 2 × ZMod 2)) : ℕ :=
  if g.toAdd.1 = 0 then 1 else 2

/-- The identity, spin-flip, diagonal, and decorated CZX tensors
for arXiv:2203.12563, line 1884. -/
def printedTensor (g : Multiplicative (ZMod 2 × ZMod 2)) : MPOTensor 2 (printedBond g) := by
  unfold printedBond
  split
  · exact if g.toAdd.2 = 0 then idTensor 2 else tensorB
  · exact if g.toAdd.2 = 0 then tensorA else czxDecoratedTensor

/-- The printed family as group-indexed tensors (arXiv:2203.12563, line 1884). -/
def printedFamily : GroupFamily (Multiplicative (ZMod 2 × ZMod 2)) 2 where
  bondDim := printedBond
  bondDim_pos g := by unfold printedBond; split <;> norm_num
  tensor := printedTensor

/-- Each tensor represents the printed operator (arXiv:2203.12563, line 1884). -/
theorem mpo_printedFamily (g : Multiplicative (ZMod 2 × ZMod 2)) (N : ℕ) [NeZero N] :
    mpo (printedFamily.tensor g) N = operator N g := by
  revert g
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  · change mpo (idTensor 2) N = _
    simp [operator, mpo_idTensor]
  · change mpo tensorB N = _
    simp [operator, mpo_tensorB, ZMod.val_one]
  · change mpo tensorA N = _
    simp [operator, mpo_tensorA, ZMod.val_one]
  · change mpo czxDecoratedTensor N = _
    simp [operator, ← generatorA_mul_generatorB, ZMod.val_one]

/-- The printed tensors are a normal representation (arXiv:2203.12563, line 1884). -/
theorem printedFamily_isNormalRepresentation : printedFamily.IsNormalRepresentation where
  isNormal := by
    refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
    · exact idTensor_isNormal
    · exact isNormal_of_bondOne tensorB 0 1 (by simp [tensorB, idTensor])
    · exact tensorA_isNormal
    · exact czxDecoratedMPS_isNormal
  operator_mul g h N hN := by
    have : NeZero N := ⟨Nat.ne_of_gt hN⟩
    simp only [mpo_printedFamily, operator_mul]

/-- The inclusion of the diagonal order-two subgroup. -/
def diagonalHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := Multiplicative.ofAdd (g.toAdd, g.toAdd)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- On the diagonal subgroup the tensors are exactly those of decorated CZX. -/
theorem printedFamily_comap_diagonal : printedFamily.comap diagonalHom = czxFamily := by
  apply GroupFamily.ext_of_heq
  · funext g
    revert g
    exact Multiplicative.forall_zmod_two rfl rfl
  · exact Multiplicative.forall_zmod_two HEq.rfl HEq.rfl

/-- The printed symmetry has cyclic anomaly invariant `-1` at `ab`,
as in arXiv:2203.12563, line 1884. -/
theorem cyclicInvariant_omega_printedFamily (fd : printedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 1)) 2 = -1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (diagonalHom czxGen) 2 = -1
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd diagonalHom
    printedFamily_isNormalRepresentation printedFamily_comap_diagonal czxFusionData
    czxGen_pow_two]
  exact cyclicInvariant_czxFusionData

/-- The printed symmetry has a nontrivial anomaly (arXiv:2203.12563, line 1884). -/
theorem not_isTrivialGaugeClass_omega_printedFamily (fd : printedFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  apply ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one
    (g := Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) (n := 2) (by decide)
  rw [cyclicInvariant_omega_printedFamily]
  intro h
  have := congrArg Units.val h
  norm_num at this

/-- Every fusion choice admits a normalized representative with the printed diagonal sign
`ω(ab,ab,ab) = -1` (arXiv:2203.12563, line 1884). -/
theorem exists_normalized_omega_printedFamily (fd : printedFamily.FusionData) :
    ∃ ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2)),
      ScalarThreeCochain.IsCocycle ν ∧ ScalarThreeCochain.IsNormalized ν ∧
      ScalarThreeCochain.CohomologousTo ν fd.omega ∧
      ν (Multiplicative.ofAdd (1, 1)) (Multiplicative.ofAdd (1, 1))
        (Multiplicative.ofAdd (1, 1)) = -1 := by
  obtain ⟨ν, hv, hn, he⟩ := ScalarThreeCochain.exists_isNormalized_cohomologousTo
    (fd.isCocycle_omega printedFamily_isNormalRepresentation)
  refine ⟨ν, hv, hn, he, ?_⟩
  have hc := he.cyclicInvariant_eq
    (g := Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) (n := 2) (by decide)
  rw [cyclicInvariant_omega_printedFamily] at hc
  simpa [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, hn.2.1] using hc

/-- The anomaly class of the printed symmetry in Mathlib's `H³(ℤ₂ × ℤ₂, ℂˣ)` is nonzero
for every choice of fusion tensors (arXiv:2203.12563, line 1884). -/
theorem anomalyClass_omega_printedFamily_ne_zero (fd : printedFamily.FusionData) :
    ScalarThreeCochain.anomalyClass
      ⟨fd.omega, fd.isCocycle_omega printedFamily_isNormalRepresentation⟩ ≠ 0 := fun h ↦
  not_isTrivialGaugeClass_omega_printedFamily fd
    ((ScalarThreeCochain.isTrivialGaugeClass_iff_anomalyClass_eq_zero _).2 h)

/-! ### The restriction to `{e, a}` -/

/-- The inclusion of the order-two subgroup generated by `a = (1,0)`. -/
def aHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.inl (ZMod 2) (ZMod 2))

/-- The integer letters of the diagonal tensor `A` of `U_a` (arXiv:2203.12563, line 1884). -/
def tensorAInt (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ := czxDecoratedIntTensor i j.rev

/-- On `{e, a}` the tensors are the identity tensor and the diagonal tensor. -/
theorem printedFamily_comap_aHom :
    printedFamily.comap aHom = GroupFamily.orderTwoFamily (idTensor 2) tensorA := by
  apply GroupFamily.ext_of_heq
  · funext g
    revert g
    exact Multiplicative.forall_zmod_two rfl rfl
  · exact Multiplicative.forall_zmod_two HEq.rfl HEq.rfl

/-- The family `1 ↦ δ`, `g ↦ A` is a normal representation, as a restriction of the printed
family. -/
theorem orderTwoFamily_tensorA_isNormalRepresentation :
    (GroupFamily.orderTwoFamily (idTensor 2) tensorA).IsNormalRepresentation :=
  printedFamily_comap_aHom ▸ printedFamily_isNormalRepresentation.comap aHom

/-- The integer row of the left fusion tensor of two copies of `A`, `⟨00|`. -/
def aFusionVInt : Matrix (Fin 1) (Fin (2 * 2)) ℤ := !![1, 0, 0, 0]

/-- The integer column of the right fusion tensor of two copies of `A`, `|00⟩ + |11⟩`. -/
def aFusionWInt : Matrix (Fin (2 * 2)) (Fin 1) ℤ := !![1; 0; 0; 1]

/-- The integer weights `δ_{s t}` of the letters of the identity tensor. -/
def pairDeltaOneInt (a : Fin (2 * 2)) : Matrix (Fin 1) (Fin 1) ℤ :=
  if a.divNat = a.modNat then 1 else 0

private theorem idTensor_toMPSTensor_eq (a : Fin (2 * 2)) :
    (idTensor 2).toMPSTensor a = complexOfInt (pairDeltaOneInt a) := by
  rw [idTensor_toMPSTensor, pairDeltaOneInt]
  split_ifs <;> simp [complexOfInt_one, complexOfInt_zero]

private theorem mulTensor_tensorA_tensorA (a : Fin (2 * 2)) :
    (mulTensor tensorA tensorA).toMPSTensor a =
      complexOfInt (mulTensorR tensorAInt tensorAInt a.divNat a.modNat) :=
  mulTensor_complexOfRing _ tensorAInt tensorAInt _ _

/-- **Fusion tensors of two copies of the diagonal tensor**: `⟨00|` and `|00⟩ + |11⟩` reduce
the stacked square of `A` to the identity tensor. -/
theorem tensorA_isReduction :
    MPSTensor.IsReduction (mulTensor tensorA tensorA).toMPSTensor (idTensor 2).toMPSTensor
      (complexOfInt aFusionVInt) (complexOfInt aFusionWInt) := by
  refine MPSTensor.IsReduction.of_local_compression ?_ (fun i ↦ ?_) (fun i j ↦ ?_)
  · rw [← complexOfInt_mul, ← complexOfInt_one]
    congr 1
    decide
  · rw [mulTensor_tensorA_tensorA, idTensor_toMPSTensor_eq, ← complexOfInt_mul,
      ← complexOfInt_mul]
    congr 1
    revert i
    decide
  · rw [mulTensor_tensorA_tensorA, mulTensor_tensorA_tensorA, ← complexOfInt_mul,
      ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul]
    congr 1
    revert i j
    decide

/-- The fusion tensors of the restriction to `{e, a}`. -/
def aFusionData : (GroupFamily.orderTwoFamily (idTensor 2) tensorA).FusionData :=
  GroupFamily.FusionData.orderTwo (idTensor 2) tensorA (complexOfInt aFusionVInt)
    (complexOfInt aFusionWInt)
    (by rw [mulTensor_idTensor_left]; rfl) (by rw [mulTensor_idTensor_left]; rfl)
    (by rw [mulTensor_idTensor_right]; rfl) tensorA_isReduction

/-- The integer letters of the triple product of `A`. -/
def tensorACubeInt (a : Fin (2 * 2)) : Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ :=
  mulTensorR (mulTensorR tensorAInt tensorAInt) tensorAInt a.divNat a.modNat

/-- The integer letters of `A` over the pair alphabet. -/
def tensorAIntMPS (a : Fin (2 * 2)) : Matrix (Fin 2) (Fin 2) ℤ :=
  tensorAInt a.divNat a.modNat

/-- **The associator of three copies of `a` is `+1`**: with the fusion tensors of
`aFusionData`, the two fusion trees agree against every nonempty word of the triple product.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`; the value is `ω_a = +1` of the
row `(0,0,1)` of arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1856--1872. -/
theorem aFusionData_isAssociator :
    aFusionData.IsAssociator GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen ((1 : ℤ) : ℂ) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [aFusionData, GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen,
    GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen, kronId_complexOfRing,
    idKron_complexOfRing]
  have h2 : mulTensor tensorA tensorA =
      fun i j ↦ complexOfInt (mulTensorR tensorAInt tensorAInt i j) :=
    funext₂ fun i j ↦ mulTensor_complexOfRing _ tensorAInt tensorAInt i j
  have hT : (GroupFamily.tripleTensor (GroupFamily.orderTwoFamily (idTensor 2) tensorA)
      GroupFamily.orderTwoGen GroupFamily.orderTwoGen
      GroupFamily.orderTwoGen).toMPSTensor = fun a ↦ complexOfInt (tensorACubeInt a) := by
    funext a
    change mulTensor (mulTensor tensorA tensorA) tensorA a.divNat a.modNat = _
    rw [h2]
    exact mulTensor_complexOfRing _ _ tensorAInt _ _
  rw [hT]
  refine MPSTensor.isDressedProportional_complexOfInt_of_mem (A := tensorAIntMPS)
    [(tensorACubeInt 0, tensorAIntMPS 0), (tensorACubeInt 3, tensorAIntMPS 3), (0, 0)]
    (by decide +kernel) ?_ ?_ ?_ <;>
    decide +kernel

/-! ### The restriction to `{e, b}` -/

/-- The inclusion of the order-two subgroup generated by `b = (0,1)`. -/
def bHom : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.inr (ZMod 2) (ZMod 2))

/-- The bond-one tensors of the restriction to `{e, b}`. -/
def bLabelTensor : Fin 2 → MPOTensor 2 1
  | ⟨0, _⟩ => idTensor 2
  | ⟨1, _⟩ => tensorB
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- The integer letters of the bond-one tensor `δ_{s, t ⊕ c}`. -/
def shiftDeltaInt (c : Fin 2) (i j : Fin 2) : Matrix (Fin 1) (Fin 1) ℤ :=
  if i = j + c then 1 else 0

private theorem bLabelTensor_eq (c : Fin 2) :
    bLabelTensor c = fun i j ↦ complexOfInt (shiftDeltaInt c i j) := by
  funext i j
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [bLabelTensor, tensorB, idTensor, shiftDeltaInt, complexOfInt_one, complexOfInt_zero]

private theorem bLabelTensor_mul_of {c d e : Fin 2}
    (h : ∀ a : Fin (2 * 2), mulTensorR (shiftDeltaInt c) (shiftDeltaInt d) a.divNat a.modNat =
      shiftDeltaInt e a.divNat a.modNat) :
    (mulTensor (bLabelTensor c) (bLabelTensor d)).toMPSTensor = (bLabelTensor e).toMPSTensor := by
  funext a
  rw [bLabelTensor_eq, bLabelTensor_eq, bLabelTensor_eq]
  exact (mulTensor_complexOfRing _ _ _ _ _).trans (congrArg complexOfInt (h a))

/-- The bond-one tensors of `{e, b}` multiply as the group. -/
theorem bLabelTensor_mul (g h : Multiplicative (ZMod 2)) :
    (mulTensor (bLabelTensor g.toAdd) (bLabelTensor h.toAdd)).toMPSTensor =
      (bLabelTensor (g * h).toAdd).toMPSTensor := by
  revert g h
  refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
    (Multiplicative.forall_zmod_two ?_ ?_)
  · exact bLabelTensor_mul_of (c := 0) (d := 0) (e := 0) (by decide)
  · exact bLabelTensor_mul_of (c := 0) (d := 1) (e := 1) (by decide)
  · exact bLabelTensor_mul_of (c := 1) (d := 0) (e := 1) (by decide)
  · exact bLabelTensor_mul_of (c := 1) (d := 1) (e := 0) (by decide)

/-- The fusion tensors of the restriction to `{e, b}`: all one-by-one identities. -/
def bFusionData :
    (GroupFamily.ofBondOne fun x : Multiplicative (ZMod 2) ↦ bLabelTensor x.toAdd).FusionData :=
  GroupFamily.FusionData.ofBondOne _ bLabelTensor_mul

/-- On `{e, b}` the tensors are the bond-one identity and spin-flip tensors. -/
theorem printedFamily_comap_bHom :
    printedFamily.comap bHom =
      GroupFamily.ofBondOne fun x : Multiplicative (ZMod 2) ↦ bLabelTensor x.toAdd := by
  apply GroupFamily.ext_of_heq
  · funext g
    revert g
    exact Multiplicative.forall_zmod_two rfl rfl
  · exact Multiplicative.forall_zmod_two HEq.rfl HEq.rfl

/-! ### The anomaly class of the full group -/

/-- The printed symmetry has cyclic anomaly invariant `+1` at `a`,
as in arXiv:2203.12563, lines 1865 and 1884. -/
theorem cyclicInvariant_omega_printedFamily_a (fd : printedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (1, 0)) 2 = 1 := by
  change ScalarThreeCochain.cyclicInvariant fd.omega (aHom GroupFamily.orderTwoGen) 2 = 1
  apply Units.ext
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq_orderTwo fd
    printedFamily_isNormalRepresentation aHom printedFamily_comap_aHom aFusionData_isAssociator]
  simp

/-- The printed symmetry has cyclic anomaly invariant `+1` at `b`,
as in arXiv:2203.12563, lines 1865 and 1884. -/
theorem cyclicInvariant_omega_printedFamily_b (fd : printedFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega (Multiplicative.ofAdd (0, 1)) 2 = 1 := by
  have h1 : bFusionData.omega = 1 := GroupFamily.FusionData.omega_ofBondOne
    (printedFamily_comap_bHom ▸ printedFamily_isNormalRepresentation.comap bHom)
  change ScalarThreeCochain.cyclicInvariant fd.omega (bHom GroupFamily.orderTwoGen) 2 = 1
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd bHom
    printedFamily_isNormalRepresentation printedFamily_comap_bHom bFusionData
    GroupFamily.orderTwoGen_pow_two, h1]
  simp [ScalarThreeCochain.cyclicInvariant]

/-- **The anomaly class of the printed symmetry is the class `(0,0,1)` of the source table**:
for every choice of fusion tensors, `ω` is cohomologous to
`(ω_I^{(1)})^0 (ω_I^{(2)})^0 (ω_II)^1`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1845--1872 (the classes
and the table) and line 1884 (the printed realization). -/
theorem omega_printedFamily_cohomologousTo (fd : printedFamily.FusionData) :
    ScalarThreeCochain.CohomologousTo fd.omega
      (ScalarThreeCochain.kleinCocycleFamily 0 0 1) := by
  refine (ScalarThreeCochain.cohomologousTo_iff_klein_three_cyclicInvariants
    (fd.isCocycle_omega printedFamily_isNormalRepresentation)
    (ScalarThreeCochain.kleinCocycleFamily_isCocycle 0 0 1)).2
    ⟨?_, ?_, ?_⟩
  · rw [cyclicInvariant_omega_printedFamily_a]
    simp [ScalarThreeCochain.cyclicInvariant, ScalarThreeCochain.kleinCocycleFamily]
  · rw [cyclicInvariant_omega_printedFamily_b]
    simp [ScalarThreeCochain.cyclicInvariant, ScalarThreeCochain.kleinCocycleFamily]
  · rw [cyclicInvariant_omega_printedFamily]
    simp [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ,
      ScalarThreeCochain.kleinCocycleFamily]

/-- **The printed diagonal values**: every normalized cocycle `ν` cohomologous to the anomaly
three-cochain of the printed symmetry has `(ν(a,a,a), ν(b,b,b), ν(ab,ab,ab)) = (+1, +1, -1)`,
the row `(0,0,1)` of the source table. This is the reading of the sentence "the only
non-trivial 3-cocycle element is `ω(ab,ab,ab) = -1`" through the diagonal values
`ω_g = ω(g,g,g)` that the source uses to label classes; a normalized cochain whose only
nontrivial value is at `(ab,ab,ab)` is not a cocycle.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1852, 1865 and 1884. -/
theorem diagonal_of_cohomologousTo_omega_printedFamily (fd : printedFamily.FusionData)
    {ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hn : ScalarThreeCochain.IsNormalized ν) (he : ScalarThreeCochain.CohomologousTo ν fd.omega) :
    ν (Multiplicative.ofAdd (1, 0)) (Multiplicative.ofAdd (1, 0)) (Multiplicative.ofAdd (1, 0)) =
        1 ∧
      ν (Multiplicative.ofAdd (0, 1)) (Multiplicative.ofAdd (0, 1))
        (Multiplicative.ofAdd (0, 1)) = 1 ∧
      ν (Multiplicative.ofAdd (1, 1)) (Multiplicative.ofAdd (1, 1))
        (Multiplicative.ofAdd (1, 1)) = -1 := by
  have hd (g : Multiplicative (ZMod 2 × ZMod 2)) :
      ScalarThreeCochain.cyclicInvariant ν g 2 = ν g g g := by
    simp [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, hn.2.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hd, he.cyclicInvariant_eq (by decide), cyclicInvariant_omega_printedFamily_a]
  · rw [← hd, he.cyclicInvariant_eq (by decide), cyclicInvariant_omega_printedFamily_b]
  · rw [← hd, he.cyclicInvariant_eq (by decide), cyclicInvariant_omega_printedFamily]

/-- The anomaly class of the printed symmetry in Mathlib's `H³(ℤ₂ × ℤ₂, ℂˣ)` corresponds to
the parameter triple `(0,0,1)` under the isomorphism `H³(ℤ₂ × ℤ₂, ℂˣ) ≃ ℤ₂³`, for every
choice of fusion tensors (arXiv:2203.12563, lines 1845--1872 and 1884). -/
theorem kleinH3Equiv_anomalyClass_omega_printedFamily (fd : printedFamily.FusionData) :
    ScalarThreeCochain.kleinH3Equiv (ScalarThreeCochain.anomalyClass
      ⟨fd.omega, fd.isCocycle_omega printedFamily_isNormalRepresentation⟩) = (0, 0, 1) := by
  rw [ScalarThreeCochain.kleinH3Equiv, AddEquiv.symm_apply_eq]
  exact (ScalarThreeCochain.cohomologousTo_iff_anomalyClass_eq _
    ⟨_, ScalarThreeCochain.kleinCocycleFamily_isCocycle 0 0 1⟩).1
    (omega_printedFamily_cohomologousTo fd)

/-- **The L-symbol sign relations of the printed symmetry**: for normalized L-symbols
compatible with a normalized cocycle `ν` cohomologous to the anomaly three-cochain of the
printed symmetry, `Lˣ_{ab,ab} = -L^{ab·x}_{ab,ab}`, `Lˣ_{a,a} = L^{a·x}_{a,a}` and
`Lˣ_{b,b} = L^{b·x}_{b,b}` for every block `x`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` line 1886, with the
compatibility relation of arXiv:2502.20257, `eq:omega_and_Ls`. -/
theorem lSymbol_signs_printedFamily (fd : printedFamily.FusionData)
    {ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hn : ScalarThreeCochain.IsNormalized ν) (he : ScalarThreeCochain.CohomologousTo ν fd.omega)
    {X : Type*} [MulAction (Multiplicative (ZMod 2 × ZMod 2)) X]
    {L : LSymbol (Multiplicative (ZMod 2 × ZMod 2)) X} (hL : LSymbol.IsCompatible L ν)
    (hLn : LSymbol.IsNormalized L) (x : X) :
    L x (Multiplicative.ofAdd (1, 1)) (Multiplicative.ofAdd (1, 1)) =
        -L (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2) • x) (Multiplicative.ofAdd (1, 1))
          (Multiplicative.ofAdd (1, 1)) ∧
      L x (Multiplicative.ofAdd (1, 0)) (Multiplicative.ofAdd (1, 0)) =
        L (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2) • x) (Multiplicative.ofAdd (1, 0))
          (Multiplicative.ofAdd (1, 0)) ∧
      L x (Multiplicative.ofAdd (0, 1)) (Multiplicative.ofAdd (0, 1)) =
        L (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2) • x) (Multiplicative.ofAdd (0, 1))
          (Multiplicative.ofAdd (0, 1)) := by
  obtain ⟨ha, hb, hab⟩ := diagonal_of_cohomologousTo_omega_printedFamily fd hn he
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.apply_involution hLn x (by decide), hab, neg_one_mul]
  · rw [hL.apply_involution hLn x (by decide), ha, one_mul]
  · rw [hL.apply_involution hLn x (by decide), hb, one_mul]

end KleinSymmetry
