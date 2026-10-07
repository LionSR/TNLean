/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cyclic insertion into a stack of copies of a unit vector

Let `η` be a unit vector of a finite-dimensional Hilbert space `ℂ^ι`.  The cyclic insertion
map `T_m : ℂ^ι → (ℂ^ι)^{⊗ m}` places its input at one of `m` positions among `m - 1`
prepared copies of `η` and averages over the `m` positions.  It is a contraction, it sends
`η` to `η^{⊗ m}`, and it differs from the ideal map `|η^{⊗ m}⟩⟨η|` by exactly `m^{-1/2}` in
operator norm, unless the orthogonal complement of `η` is zero, in which case the two maps
agree.  The estimate is unchanged when the map is tensored with the identity on a spectator
space.

Product vectors on the configurations `κ → ι` represent the tensor power `(ℂ^ι)^{⊗ κ}`
coordinatewise; `EuclideanSpace.piTensor` is the `EuclideanSpace` form, over an arbitrary
finite alphabet, of the coordinate formula of `QuantumCircuit.productVector`.  Moving the
insertion position is a permutation of the registers.  For a pair space `ι = α × β`, the index
map of a register permutation is the same permutation of the `α` indices together with the
same permutation of the `β` indices (`CyclicInsertion.registerPerm_pair_index`); the operator
factorization through `(ℂ^{α × β})^{⊗ κ} ≅ (ℂ^α)^{⊗ κ} ⊗ (ℂ^β)^{⊗ κ}` is not formalized.

This generic finite-dimensional statement is a candidate for QICLean.

## Main definitions

* `EuclideanSpace.piTensor` : the product vector `⊗ⱼ vⱼ` on configurations `κ → ι`.
* `EuclideanSpace.tensorPower` : the tensor power `η^{⊗ κ}`.
* `CyclicInsertion.insertAt` : insertion of a vector at one position among copies of `η`.
* `CyclicInsertion.registerPerm` : a permutation of the registers of `(ℂ^ι)^{⊗ κ}`.
* `CyclicInsertion.cyclicInsertion` : the average `T_m` of the `m` insertions.
* `CyclicInsertion.idealInsertion` : the ideal map `|η^{⊗ m}⟩⟨η|`.

## Main results

* `EuclideanSpace.inner_piTensor` : `⟪⊗ⱼ vⱼ, ⊗ⱼ wⱼ⟫ = ∏ⱼ ⟪vⱼ, wⱼ⟫`.
* `CyclicInsertion.inner_insertAt_insertAt` : insertions of one vector at two positions are
  orthogonal when the vector is orthogonal to `η`.
* `CyclicInsertion.insertAt_perm` : moving the insertion position is a register permutation.
* `CyclicInsertion.norm_cyclicInsertion_le_one` : `T_m` is a contraction.
* `CyclicInsertion.cyclicInsertion_self` : `T_m η = η^{⊗ m}`.
* `CyclicInsertion.norm_cyclicInsertion_sub_ideal_le` : `‖T_m - |η^{⊗ m}⟩⟨η|‖ ≤ m^{-1/2}`.
* `CyclicInsertion.norm_cyclicInsertion_sub_ideal_eq` : equality when `η⊥ ≠ 0`.
* `CyclicInsertion.cyclicInsertion_sub_ideal_eq_zero` : the difference vanishes when
  `η⊥ = 0`.
* `CyclicInsertion.norm_rTensor_cyclicInsertion_sub_ideal_le` : the same estimate with a
  spectator space.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, proof of the
  one-effect estimate `eq:compression-one-effect`, `04-compression.tex`, lines 73–98.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The product vector `⊗ⱼ vⱼ` in `(ℂ^ι)^{⊗ κ}`, written on configurations `κ → ι`: its
coefficient on `f` is `∏ⱼ vⱼ (f j)`.  The vector depends multilinearly on the family `v`.
For `ι = Fin d` this is the coordinate formula of `QuantumCircuit.productVector`. -/
def piTensorMultilinear :
    MultilinearMap ℂ (fun _ : κ => EuclideanSpace ℂ ι) (EuclideanSpace ℂ (κ → ι)) :=
  (WithLp.linearEquiv 2 ℂ ((κ → ι) → ℂ)).symm.toLinearMap.compMultilinearMap
    (MultilinearMap.pi fun f =>
      (MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap fun j =>
        (EuclideanSpace.proj (f j) : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap)

/-- The product vector `⊗ⱼ vⱼ` on configurations `κ → ι`. -/
def piTensor (v : κ → EuclideanSpace ℂ ι) : EuclideanSpace ℂ (κ → ι) :=
  piTensorMultilinear v

omit [Fintype ι] [DecidableEq κ] in
@[simp]
theorem piTensor_apply (v : κ → EuclideanSpace ℂ ι) (f : κ → ι) :
    piTensor v f = ∏ j, v j (f j) := by
  simp [piTensor, piTensorMultilinear, MultilinearMap.mkPiAlgebra_apply]

/-- The tensor power `η^{⊗ κ}`. -/
def tensorPower (κ : Type*) [Fintype κ] [DecidableEq κ] (η : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (κ → ι) :=
  piTensor fun _ : κ => η

/-- The inner product of two product vectors is the product of the inner products of their
factors. -/
theorem inner_piTensor (v w : κ → EuclideanSpace ℂ ι) :
    ⟪piTensor v, piTensor w⟫_ℂ = ∏ j, ⟪v j, w j⟫_ℂ := by
  simp only [PiLp.inner_apply, piTensor_apply, RCLike.inner_apply, map_prod]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [Finset.prod_mul_distrib]

theorem norm_piTensor (v : κ → EuclideanSpace ℂ ι) : ‖piTensor v‖ = ∏ j, ‖v j‖ := by
  have h : ‖piTensor v‖ ^ 2 = (∏ j, ‖v j‖) ^ 2 := by
    have := inner_piTensor v v
    simp only [inner_self_eq_norm_sq_to_K] at this
    rw [← Finset.prod_pow]
    exact_mod_cast this
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    two_ne_zero).1 h

theorem norm_tensorPower {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) :
    ‖tensorPower κ η‖ = 1 := by
  simp [tensorPower, norm_piTensor, hη]

section PairCombine

variable {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

/-- Two pair vectors `η ∈ ℂ^α ⊗ ℂ^β` and `η' ∈ ℂ^α' ⊗ ℂ^β'` on the same two parties combine
into one pair vector `η ⊗ η'` on the tensor products `ℂ^α ⊗ ℂ^α'` and `ℂ^β ⊗ ℂ^β'` of their
respective half-spaces. -/
def pairCombine (η : EuclideanSpace ℂ (α × β)) (η' : EuclideanSpace ℂ (α' × β')) :
    EuclideanSpace ℂ ((α × α') × (β × β')) :=
  WithLp.toLp 2 fun x => η (x.1.1, x.2.1) * η' (x.1.2, x.2.2)

/-- Combining pair vectors multiplies their norms; in particular normalized pair sources on
one pair of parties combine into one normalized pair source.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, last sentence of
the statement and of the proof, `04-compression.tex`, lines 68–70 and 125–127. -/
theorem norm_pairCombine (η : EuclideanSpace ℂ (α × β)) (η' : EuclideanSpace ℂ (α' × β')) :
    ‖pairCombine η η'‖ = ‖η‖ * ‖η'‖ := by
  have h : ‖pairCombine η η'‖ ^ 2 = (‖η‖ * ‖η'‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum, ← Finset.sum_product',
      Finset.univ_product_univ]
    simp only [pairCombine, PiLp.toLp_apply, norm_mul, mul_pow]
    exact Fintype.sum_equiv (Equiv.prodProdProdComm α α' β β') _ _ fun _ => rfl
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

end PairCombine

end EuclideanSpace

namespace CyclicInsertion

open EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Insertion of a vector `v` at position `k` among copies of `η`: the product vector with
`v` in register `k` and `η` in every other register. -/
def insertAt (η : EuclideanSpace ℂ ι) (k : κ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ (κ → ι) :=
  LinearMap.toContinuousLinearMap (piTensorMultilinear.toLinearMap (fun _ => η) k)

theorem insertAt_apply (η : EuclideanSpace ℂ ι) (k : κ) (v : EuclideanSpace ℂ ι) :
    insertAt η k v = piTensor (Function.update (fun _ => η) k v) := rfl

@[simp]
theorem insertAt_self (η : EuclideanSpace ℂ ι) (k : κ) :
    insertAt η k η = tensorPower κ η := by
  rw [insertAt_apply, Function.update_eq_self_iff.2 rfl]
  rfl

/-- Insertion at the first of `n + 1` positions prepares `n` copies of `η` next to the
input. -/
theorem insertAt_zero {n : ℕ} (η v : EuclideanSpace ℂ ι) :
    insertAt η (0 : Fin (n + 1)) v = piTensor (Fin.cons v fun _ => η) := by
  rw [insertAt_apply]
  congr 1
  ext j : 1
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- Two insertions into copies of a unit vector `η`: at equal positions the inner product is
that of the inserted vectors, and at different positions it factors through `η`. -/
theorem inner_insertAt_insertAt {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (j k : κ)
    (v w : EuclideanSpace ℂ ι) :
    ⟪insertAt η j v, insertAt η k w⟫_ℂ =
      if j = k then ⟪v, w⟫_ℂ else ⟪v, η⟫_ℂ * ⟪η, w⟫_ℂ := by
  have hηη : ⟪η, η⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hη]; norm_num
  rw [insertAt_apply, insertAt_apply, inner_piTensor]
  split_ifs with hjk
  · subst hjk
    rw [Fintype.prod_eq_single j fun l hl => by
      simp [Function.update_of_ne hl, inner_self_eq_norm_sq_to_K, hη]]
    simp
  · rw [Fintype.prod_eq_mul j k hjk fun l hl => by
      simp [Function.update_of_ne hl.1, Function.update_of_ne hl.2,
        inner_self_eq_norm_sq_to_K, hη]]
    simp [Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk)]

theorem norm_insertAt {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (k : κ)
    (v : EuclideanSpace ℂ ι) : ‖insertAt η k v‖ = ‖v‖ := by
  rw [insertAt_apply, norm_piTensor, Fintype.prod_eq_single k fun l hl => by
    simp [Function.update_of_ne hl, hη]]
  simp

theorem norm_insertAt_le_one {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (k : κ) :
    ‖insertAt η k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_insertAt hη, one_mul]

/-- The permutation of the registers of `(ℂ^ι)^{⊗ κ}` that moves register `j` to register
`σ j`. -/
def registerPerm (ι : Type*) [Fintype ι] (σ : Equiv.Perm κ) :
    EuclideanSpace ℂ (κ → ι) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ → ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.arrowCongr σ (Equiv.refl ι))

theorem registerPerm_piTensor (σ : Equiv.Perm κ) (v : κ → EuclideanSpace ℂ ι) :
    registerPerm ι σ (piTensor v) = piTensor (v ∘ σ.symm) := by
  ext f
  simp only [registerPerm, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    piTensor_apply, Function.comp_apply]
  exact Fintype.prod_equiv σ _ _ fun j => by simp [Equiv.arrowCongr_apply]

/-- Moving the insertion position from `k` to `σ k` is the register permutation `σ`. -/
theorem insertAt_perm (η : EuclideanSpace ℂ ι) (σ : Equiv.Perm κ) (k : κ) :
    insertAt η (σ k) =
      (registerPerm ι σ : EuclideanSpace ℂ (κ → ι) →L[ℂ] _) ∘L insertAt η k := by
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, insertAt_apply,
    LinearIsometryEquiv.coe_coe'', registerPerm_piTensor]
  congr 1
  rw [Function.update_comp_equiv, Equiv.symm_symm]
  rfl

omit [Fintype κ] [DecidableEq κ] in
/-- Index-level form of the locality of register permutations: for pair registers
`ι = α × β`, the index map of a register permutation acts by the same permutation on the `α`
indices and on the `β` indices.  This is a statement about index bijections only; the
corresponding operator factorization is not formalized. -/
theorem registerPerm_pair_index {α β : Type*} (σ : Equiv.Perm κ) (f : κ → α × β) :
    Equiv.arrowProdEquivProdArrow κ (fun _ => α) (fun _ => β)
        ((Equiv.arrowCongr σ (Equiv.refl (α × β))) f) =
      ((Equiv.arrowCongr σ (Equiv.refl α))
          (Equiv.arrowProdEquivProdArrow κ (fun _ => α) (fun _ => β) f).1,
        (Equiv.arrowCongr σ (Equiv.refl β))
          (Equiv.arrowProdEquivProdArrow κ (fun _ => α) (fun _ => β) f).2) :=
  rfl

/-- The cyclic insertion map `T_m`: the average over the `m` positions of the insertions of
the input among `m - 1` copies of `η`. -/
def cyclicInsertion (η : EuclideanSpace ℂ ι) (m : ℕ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ (Fin m → ι) :=
  ∑ k : Fin m, ((m : ℂ)⁻¹) • insertAt η k

/-- The cyclic insertion is the average of the insertion at the first position followed by
the `m` cyclic register permutations `j ↦ j + k`. -/
theorem cyclicInsertion_eq_sum_addRight {n : ℕ} (η : EuclideanSpace ℂ ι) :
    cyclicInsertion η (n + 1) =
      ∑ k : Fin (n + 1), (((n + 1 : ℕ) : ℂ)⁻¹) •
        ((registerPerm ι (Equiv.addRight k) :
          EuclideanSpace ℂ (Fin (n + 1) → ι) →L[ℂ] _) ∘L insertAt η 0) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← insertAt_perm]
  simp

/-- The ideal map `|η^{⊗ m}⟩⟨η|`. -/
def idealInsertion (η : EuclideanSpace ℂ ι) (m : ℕ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ (Fin m → ι) :=
  (innerSL ℂ η).smulRight (tensorPower (Fin m) η)

@[simp]
theorem idealInsertion_apply (η : EuclideanSpace ℂ ι) (m : ℕ) (v : EuclideanSpace ℂ ι) :
    idealInsertion η m v = ⟪η, v⟫_ℂ • tensorPower (Fin m) η := by
  simp [idealInsertion]

theorem norm_cyclicInsertion_le_one {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (m : ℕ) :
    ‖cyclicInsertion η m‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cyclicInsertion]
  calc ‖cyclicInsertion η m‖ ≤ ∑ k : Fin m, ‖((m : ℂ)⁻¹) • insertAt η k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, (m : ℝ)⁻¹ := Finset.sum_le_sum fun k _ => by
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        exact mul_le_of_le_one_right (by positivity) (norm_insertAt_le_one hη k)
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ (by exact_mod_cast hm.ne')

@[simp]
theorem cyclicInsertion_self (η : EuclideanSpace ℂ ι) {m : ℕ} (hm : m ≠ 0) :
    cyclicInsertion η m η = tensorPower (Fin m) η := by
  simp only [cyclicInsertion, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, insertAt_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [mul_inv_cancel₀ (by exact_mod_cast hm), one_smul]

/-- On the orthogonal complement of `η`, the cyclic insertion scales norms by `m^{-1/2}`:
the `m` insertion positions are pairwise orthogonal and each has the norm of the input. -/
theorem norm_cyclicInsertion_of_inner_eq_zero {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) {w : EuclideanSpace ℂ ι} (hw : ⟪η, w⟫_ℂ = 0) :
    ‖cyclicInsertion η m w‖ = ‖w‖ / Real.sqrt m := by
  have hw' : ⟪w, η⟫_ℂ = 0 := inner_eq_zero_symm.1 hw
  have hsum : ‖∑ k : Fin m, insertAt η k w‖ ^ 2 = m * ‖w‖ ^ 2 := by
    have h : ⟪∑ k : Fin m, insertAt η k w, ∑ k : Fin m, insertAt η k w⟫_ℂ =
        m • ⟪w, w⟫_ℂ := by
      simp only [sum_inner, inner_sum, inner_insertAt_insertAt hη, hw', zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
    rw [← @inner_self_eq_norm_sq ℂ, h, map_nsmul, @inner_self_eq_norm_sq ℂ, nsmul_eq_mul]
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hT : cyclicInsertion η m w = (m : ℂ)⁻¹ • ∑ k : Fin m, insertAt η k w := by
    simp [cyclicInsertion, Finset.smul_sum]
  rw [hT, norm_smul, norm_inv, Complex.norm_natCast,
    show ‖∑ k : Fin m, insertAt η k w‖ = Real.sqrt m * ‖w‖ by
      rw [← Real.sqrt_sq (norm_nonneg _), hsum, Real.sqrt_mul hmR.le,
        Real.sqrt_sq (norm_nonneg _)]]
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.2 hmR).ne'
  field_simp
  rw [Real.sq_sqrt hmR.le]

/-- The cyclic insertion and the ideal map differ only through the component orthogonal to
`η`. -/
theorem cyclicInsertion_sub_ideal_apply {η : EuclideanSpace ℂ ι} {m : ℕ} (hm : m ≠ 0)
    (v : EuclideanSpace ℂ ι) :
    (cyclicInsertion η m - idealInsertion η m) v =
      cyclicInsertion η m (v - ⟪η, v⟫_ℂ • η) := by
  rw [map_sub, map_smul, cyclicInsertion_self η hm, sub_apply,
    idealInsertion_apply]

theorem inner_sub_inner_smul_eq_zero {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    (v : EuclideanSpace ℂ ι) : ⟪η, v - ⟪η, v⟫_ℂ • η⟫_ℂ = 0 := by
  have hηη : ⟪η, η⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hη]; norm_num
  rw [inner_sub_right, inner_smul_right, hηη, mul_one, sub_self]

theorem norm_sub_inner_smul_le {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    (v : EuclideanSpace ℂ ι) : ‖v - ⟪η, v⟫_ℂ • η‖ ≤ ‖v‖ := by
  have h0 : ⟪v - ⟪η, v⟫_ℂ • η, ⟪η, v⟫_ℂ • η⟫_ℂ = 0 := by
    rw [inner_smul_right, inner_eq_zero_symm.1 (inner_sub_inner_smul_eq_zero hη v), mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_cancel] at h
  nlinarith [norm_nonneg (v - ⟪η, v⟫_ℂ • η), norm_nonneg v,
    sq_nonneg ‖⟪η, v⟫_ℂ • η‖]

/-- **One-effect estimate.** The cyclic insertion map differs from `|η^{⊗ m}⟩⟨η|` by at
most `m^{-1/2}` in operator norm.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, displayed
equation `eq:compression-one-effect`, `04-compression.tex`, lines 73–98. -/
theorem norm_cyclicInsertion_sub_ideal_le {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) :
    ‖cyclicInsertion η m - idealInsertion η m‖ ≤ 1 / Real.sqrt m := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [cyclicInsertion_sub_ideal_apply hm,
    norm_cyclicInsertion_of_inner_eq_zero hη hm (inner_sub_inner_smul_eq_zero hη v),
    one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_sub_inner_smul_le hη v) (Real.sqrt_nonneg _)

/-- **One-effect estimate, equality case.** When the orthogonal complement of `η` is
nonzero, the operator-norm distance is exactly `m^{-1/2}`.

Polynomial-PEPS manuscript (September 24, 2026), `eq:compression-one-effect`,
`04-compression.tex`, lines 88–94. -/
theorem norm_cyclicInsertion_sub_ideal_eq {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) (hperp : ∃ w : EuclideanSpace ℂ ι, w ≠ 0 ∧ ⟪η, w⟫_ℂ = 0) :
    ‖cyclicInsertion η m - idealInsertion η m‖ = 1 / Real.sqrt m := by
  refine le_antisymm (norm_cyclicInsertion_sub_ideal_le hη hm) ?_
  obtain ⟨w, hw0, hw⟩ := hperp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have happly : (cyclicInsertion η m - idealInsertion η m) w = cyclicInsertion η m w := by
    rw [cyclicInsertion_sub_ideal_apply hm, hw, zero_smul, sub_zero]
  have h := (cyclicInsertion η m - idealInsertion η m).le_opNorm w
  rw [happly, norm_cyclicInsertion_of_inner_eq_zero hη hm hw] at h
  rw [one_div]
  rw [div_eq_inv_mul] at h
  exact le_of_mul_le_mul_right (by linarith) hwpos

/-- **One-effect estimate, degenerate case.** When the orthogonal complement of `η` is zero,
the cyclic insertion map equals the ideal map.

Polynomial-PEPS manuscript (September 24, 2026), `eq:compression-one-effect` and the
sentence after it, `04-compression.tex`, lines 88–95. -/
theorem cyclicInsertion_sub_ideal_eq_zero {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) (hperp : ∀ w : EuclideanSpace ℂ ι, ⟪η, w⟫_ℂ = 0 → w = 0) :
    cyclicInsertion η m - idealInsertion η m = 0 := by
  ext1 v
  rw [cyclicInsertion_sub_ideal_apply hm, hperp _ (inner_sub_inner_smul_eq_zero hη v),
    map_zero, zero_apply]

/-- The one-effect estimate is unchanged by adjoining a spectator space.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 95–96. -/
theorem norm_rTensor_cyclicInsertion_sub_ideal_le {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℂ S] :
    ‖(cyclicInsertion η m - idealInsertion η m).rTensor S‖ ≤ 1 / Real.sqrt m :=
  (ContinuousLinearMap.norm_rTensor_le _ _).trans (norm_cyclicInsertion_sub_ideal_le hη hm)

end CyclicInsertion
