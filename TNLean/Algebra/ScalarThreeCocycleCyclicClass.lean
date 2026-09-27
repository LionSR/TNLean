/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import TNLean.Algebra.ScalarThreeCocycleCyclicDomainWall
import TNLean.Algebra.ScalarThreeCocycleGroupCohomology

/-!
# The classes of the cyclic three-cocycles in `H³(ℤ_n, ℂˣ)`

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.D,
`Papers/2405.00439/MPU-DW.tex` line 2040: `H³(ℤ_n, U(1)) = ℤ_n`, and the cocycles
`ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}`, `j = 0, …, n − 1`, label the different
cocycle classes, `j = 0` being the trivial one.

**Formalized here.** In Mathlib's group cohomology `H³(ℤ_n, ℂˣ)` of the trivial representation,
the class of `ω_j` vanishes exactly when `n ∣ j`, and the classes of `ω_j` and `ω_{j'}` agree
exactly when `j ≡ j' mod n`. The group `H³(ℤ_n, ℂˣ)` has `n` elements, by Mathlib's periodic
computation of the cohomology of a finite cyclic group, so the `n` classes of
`ω_0, …, ω_{n−1}` exhaust it: every scalar three-cocycle of `ℤ_n` is cohomologous to some
`ω_j`. Consequently the domain-wall phase at the generator determines the class of a
three-cocycle of `ℤ_n`.

## Main results

* `TNLean.Algebra.ScalarThreeCochain.isTrivialGaugeClass_cyclicCocycle_iff`,
  `TNLean.Algebra.ScalarThreeCochain.anomalyClass_cyclicCocycle_eq_zero_iff`: `ω_j` is trivial
  exactly when `n ∣ j`.
* `TNLean.Algebra.ScalarThreeCochain.anomalyClass_cyclicCocycle_eq_iff`: the classes of `ω_j`
  and `ω_{j'}` agree exactly when `j ≡ j' mod n`.
* `TNLean.Algebra.ScalarThreeCochain.nat_card_groupCohomology_three_cyclic`: `H³(ℤ_n, ℂˣ)` has
  `n` elements.
* `TNLean.Algebra.ScalarThreeCochain.exists_cohomologousTo_cyclicCocycle`: every three-cocycle
  of `ℤ_n` is cohomologous to some `ω_j` with `j < n`.
* `TNLean.Algebra.ScalarThreeCochain.cohomologousTo_iff_domainWallPhase_eq`: two three-cocycles
  of `ℤ_n` are cohomologous exactly when their domain-wall phases at the generator agree.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open CategoryTheory groupCohomology

namespace TNLean.Algebra.ScalarThreeCochain

variable {n : ℕ} [NeZero n]

/-- `ζ = exp(2πi/n)` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_rootOfUnity : IsPrimitiveRoot (rootOfUnity n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

/-- The cocycle `ω_j` of `ℤ_n` as an element of the subtype of three-cocycles. -/
abbrev cyclicCocycleSubtype (n j : ℕ) [NeZero n] :
    {ω : ScalarThreeCochain (Multiplicative (ZMod n)) // IsCocycle ω} :=
  ⟨cyclicCocycle n j, cyclicCocycle_isCocycle n j⟩

/-- `ω_j` depends on `j` only modulo `n`. -/
theorem cyclicCocycle_eq_of_modEq {j j' : ℕ} (h : j ≡ j' [MOD n]) :
    cyclicCocycle n j = cyclicCocycle n j' := by
  funext a b c
  apply Units.ext
  rw [cyclicCocycle_val, cyclicCocycle_val, pow_eq_pow_mod _ (rootOfUnity_pow n),
    pow_eq_pow_mod (j' * _ * _) (rootOfUnity_pow n)]
  exact congrArg _ ((h.mul_right _).mul_right _)

/-- `ω_0` is the constant cochain one. -/
theorem cyclicCocycle_zero : cyclicCocycle n 0 = fun _ _ _ ↦ 1 := by
  funext a b c
  apply Units.ext
  rw [cyclicCocycle_val, zero_mul, zero_mul, pow_zero, Units.val_one]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040: `ω_j` has trivial
class exactly when `n ∣ j`; `j = 0` is the trivial cocycle. -/
theorem isTrivialGaugeClass_cyclicCocycle_iff (hn : 1 < n) (j : ℕ) :
    IsTrivialGaugeClass (cyclicCocycle n j) ↔ n ∣ j := by
  constructor
  · intro h
    by_contra hj
    refine not_isTrivialGaugeClass_of_cyclicInvariant_ne_one (g := Multiplicative.ofAdd 1)
      (n := n) (by rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero])
      ?_ h
    intro h1
    have h1 := congrArg Units.val h1
    rw [cyclicInvariant_cyclicCocycle_one hn, Units.val_one,
      isPrimitiveRoot_rootOfUnity.pow_eq_one_iff_dvd] at h1
    exact hj h1
  · intro h
    rw [IsTrivialGaugeClass, cyclicCocycle_eq_of_modEq (j' := 0) (Nat.modEq_zero_iff_dvd.2 h),
      cyclicCocycle_zero]
    exact CohomologousTo.refl _

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040: the class of `ω_j`
in `H³(ℤ_n, ℂˣ)` vanishes exactly when `n ∣ j`. -/
theorem anomalyClass_cyclicCocycle_eq_zero_iff (hn : 1 < n) (j : ℕ) :
    anomalyClass (cyclicCocycleSubtype n j) = 0 ↔ n ∣ j := by
  rw [← isTrivialGaugeClass_iff_anomalyClass_eq_zero, isTrivialGaugeClass_cyclicCocycle_iff hn]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040: the classes of `ω_j`
and `ω_{j'}` in `H³(ℤ_n, ℂˣ)` agree exactly when `j ≡ j' mod n`. -/
theorem anomalyClass_cyclicCocycle_eq_iff (hn : 1 < n) (j j' : ℕ) :
    anomalyClass (cyclicCocycleSubtype n j) = anomalyClass (cyclicCocycleSubtype n j') ↔
      j ≡ j' [MOD n] := by
  rw [← cohomologousTo_iff_anomalyClass_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hj
    exact not_cohomologousTo_cyclicCocycle hn hj h
  · change CohomologousTo (cyclicCocycle n j) (cyclicCocycle n j')
    rw [cyclicCocycle_eq_of_modEq h]
    exact CohomologousTo.refl _

/-! ### The order of `H³(ℤ_n, ℂˣ)` -/

/-- The generator `1` of `ℤ_n` generates `ℤ_n`. -/
theorem mem_zpowers_ofAdd_one (x : Multiplicative (ZMod n)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  refine ⟨(Multiplicative.toAdd x).val, ?_⟩
  change Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℤ) = x
  rw [zpow_natCast, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

/-- The norm map of the trivial representation of `ℤ_n` on `ℂˣ` is `x ↦ n • x`, that is,
`z ↦ z^n` multiplicatively. -/
theorem norm_scalarH2Representation_apply (x : scalarH2Representation (Multiplicative (ZMod n))) :
    (scalarH2Representation (Multiplicative (ZMod n))).norm.hom x = n • x := by
  rw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply]
  simp only [scalarH2Representation_ρ_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_multiplicative, ZMod.card]

omit [NeZero n] in
/-- The generator acts trivially on the scalar representation: `ρ(1) − 1 = 0`. -/
theorem applyAsHom_ofAdd_one_sub_id :
    Rep.applyAsHom (scalarH2Representation (Multiplicative (ZMod n))) (Multiplicative.ofAdd 1) -
      𝟙 _ = 0 := by
  ext x
  simp [Rep.applyAsHom, Rep.sub_hom, scalarH2Representation_ρ_apply]

/-- The kernel of the norm map of the trivial representation of `ℤ_n` on `ℂˣ` is the group
of `n`-th roots of unity. -/
def normKerEquivRootsOfUnity :
    LinearMap.ker (scalarH2Representation (Multiplicative (ZMod n))).norm.hom.toLinearMap ≃
      rootsOfUnity n ℂ where
  toFun x := ⟨Additive.toMul ((scalarRepresentationEquiv _).symm x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    change (scalarH2Representation (Multiplicative (ZMod n))).norm.hom x.1 = 0 at hx
    rw [norm_scalarH2Representation_apply] at hx
    rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hx, map_zero, toMul_zero]⟩
  invFun z := ⟨scalarRepresentationEquiv _ (Additive.ofMul z.1), by
    rw [LinearMap.mem_ker]
    change (scalarH2Representation (Multiplicative (ZMod n))).norm.hom _ = 0
    rw [norm_scalarH2Representation_apply, ← map_nsmul, ← ofMul_pow,
      (mem_rootsOfUnity _ _).1 z.2, ofMul_one, map_zero]⟩
  left_inv x := by simp
  right_inv z := by simp

/-- Project result: **`H³(ℤ_n, ℂˣ)` has `n` elements**. Mathlib's periodic resolution of a
finite cyclic group identifies `H³(ℤ_n, ℂˣ)` with the kernel of the norm modulo the image of
`ρ(1) − 1`, which for the trivial action is the group of `n`-th roots of unity. -/
theorem nat_card_groupCohomology_three_cyclic :
    Nat.card (groupCohomology (scalarH2Representation (Multiplicative (ZMod n))) 3) = n := by
  have h3 : Odd 3 := by decide
  have hπ : Epi (Rep.FiniteCyclicGroup.subCompNormHom
      (scalarH2Representation (Multiplicative (ZMod n))) (Multiplicative.ofAdd 1)).homologyπ :=
    inferInstance
  have hinj : Function.Injective (Rep.FiniteCyclicGroup.groupCohomologyπOdd
      (scalarH2Representation (Multiplicative (ZMod n))) (Multiplicative.ofAdd 1)
      mem_zpowers_ofAdd_one 3 h3) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff, applyAsHom_ofAdd_one_sub_id] at hx
    obtain ⟨y, hy⟩ := hx
    exact Subtype.ext (hy.symm.trans (by simp))
  have hsurj : Function.Surjective (Rep.FiniteCyclicGroup.groupCohomologyπOdd
      (scalarH2Representation (Multiplicative (ZMod n))) (Multiplicative.ofAdd 1)
      mem_zpowers_ofAdd_one 3 h3) :=
    (ModuleCat.epi_iff_surjective _).1 (by
      unfold Rep.FiniteCyclicGroup.groupCohomologyπOdd
      exact epi_comp' (Iso.isIso_inv _).epi_of_iso (epi_comp' hπ (Iso.isIso_inv _).epi_of_iso))
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩),
    Nat.card_congr normKerEquivRootsOfUnity, Complex.card_rootsOfUnity]

/-! ### The cyclic cocycles exhaust `H³(ℤ_n, ℂˣ)` -/

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040:
**`H³(ℤ_n, ℂˣ) = {[ω_0], …, [ω_{n−1}]}`**; every class is the class of some `ω_j`, `j < n`. -/
theorem exists_anomalyClass_cyclicCocycle_eq (hn : 1 < n)
    (c : groupCohomology (scalarH2Representation (Multiplicative (ZMod n))) 3) :
    ∃ j < n, anomalyClass (cyclicCocycleSubtype n j) = c := by
  have hcard := nat_card_groupCohomology_three_cyclic (n := n)
  have : Finite (groupCohomology (scalarH2Representation (Multiplicative (ZMod n))) 3) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne n)
  have hinj : Function.Injective fun j : Fin n ↦ anomalyClass (cyclicCocycleSubtype n j) :=
    fun j j' h ↦ Fin.ext (((anomalyClass_cyclicCocycle_eq_iff hn j j').1 h).eq_of_lt_of_lt j.2 j'.2)
  obtain ⟨j, hj⟩ := (hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card,
    Fintype.card_fin])).2 c
  exact ⟨j, j.2, hj⟩

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040: **every three-cocycle
of `ℤ_n` is cohomologous to some `ω_j`**, `j < n`. -/
theorem exists_cohomologousTo_cyclicCocycle (hn : 1 < n)
    {ω : ScalarThreeCochain (Multiplicative (ZMod n))} (hω : IsCocycle ω) :
    ∃ j < n, CohomologousTo ω (cyclicCocycle n j) := by
  obtain ⟨j, hj, h⟩ := exists_anomalyClass_cyclicCocycle_eq hn (anomalyClass ⟨ω, hω⟩)
  exact ⟨j, hj, (cohomologousTo_iff_anomalyClass_eq ⟨ω, hω⟩ (cyclicCocycleSubtype n j)).2 h.symm⟩

omit [NeZero n] in
/-- The generator `1` of `ℤ_n` satisfies `1^n = 1`. -/
theorem ofAdd_one_pow_self : Multiplicative.ofAdd (1 : ZMod n) ^ n = 1 := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]

/-- Project result: **the cyclic invariant at the generator determines the class**: two
three-cocycles of `ℤ_n` with the same invariant `∏_{k<n} ω(1, k, 1)` are cohomologous. -/
theorem cohomologousTo_of_cyclicInvariant_eq (hn : 1 < n)
    {ω η : ScalarThreeCochain (Multiplicative (ZMod n))} (hω : IsCocycle ω) (hη : IsCocycle η)
    (h : cyclicInvariant ω (Multiplicative.ofAdd 1) n =
      cyclicInvariant η (Multiplicative.ofAdd 1) n) :
    CohomologousTo ω η := by
  obtain ⟨j, -, hj⟩ := exists_cohomologousTo_cyclicCocycle hn hω
  obtain ⟨j', -, hj'⟩ := exists_cohomologousTo_cyclicCocycle hn hη
  have h' := congrArg Units.val h
  rw [hj.cyclicInvariant_eq ofAdd_one_pow_self, hj'.cyclicInvariant_eq ofAdd_one_pow_self,
    cyclicInvariant_cyclicCocycle_one hn, cyclicInvariant_cyclicCocycle_one hn,
    pow_eq_pow_mod j (rootOfUnity_pow n), pow_eq_pow_mod j' (rootOfUnity_pow n)] at h'
  have hjj : j ≡ j' [MOD n] := isPrimitiveRoot_rootOfUnity.pow_inj (Nat.mod_lt _ (NeZero.pos n))
    (Nat.mod_lt _ (NeZero.pos n)) h'
  rw [cyclicCocycle_eq_of_modEq hjj] at hj
  exact hj.trans hj'.symm

omit [NeZero n] in
/-- The generator `1` of `ℤ_n` has order `n`. -/
theorem orderOf_ofAdd_one : orderOf (Multiplicative.ofAdd (1 : ZMod n)) = n := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2013–2021 and 2040:
**the domain-wall phase at the generator determines the class**: two three-cocycles of `ℤ_n`
are cohomologous exactly when `∏_{k=1}^{n} ω⁻¹(1, k, 1)` agree. -/
theorem cohomologousTo_iff_domainWallPhase_eq (hn : 1 < n)
    {ω η : ScalarThreeCochain (Multiplicative (ZMod n))} (hω : IsCocycle ω) (hη : IsCocycle η) :
    CohomologousTo ω η ↔
      domainWallPhase ω (Multiplicative.ofAdd 1) = domainWallPhase η (Multiplicative.ofAdd 1) := by
  refine ⟨fun h ↦ h.domainWallPhase_eq _, fun h ↦ cohomologousTo_of_cyclicInvariant_eq hn hω hη ?_⟩
  rw [domainWallPhase_eq_inv_cyclicInvariant, domainWallPhase_eq_inv_cyclicInvariant,
    orderOf_ofAdd_one] at h
  exact inv_injective h

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2013–2021 and 2040: two
three-cocycles of `ℤ_n` have the same class in `H³(ℤ_n, ℂˣ)` exactly when their domain-wall
phases at the generator agree. -/
theorem anomalyClass_eq_iff_domainWallPhase_eq (hn : 1 < n)
    (ω η : {ω : ScalarThreeCochain (Multiplicative (ZMod n)) // IsCocycle ω}) :
    anomalyClass ω = anomalyClass η ↔
      domainWallPhase ω.1 (Multiplicative.ofAdd 1) =
        domainWallPhase η.1 (Multiplicative.ofAdd 1) := by
  rw [← cohomologousTo_iff_anomalyClass_eq, cohomologousTo_iff_domainWallPhase_eq hn ω.2 η.2]

end TNLean.Algebra.ScalarThreeCochain
