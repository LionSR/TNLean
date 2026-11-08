/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleTimeReversal
import TNLean.MPS.Symmetry.MPDO.Vectorized
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Time reversal makes the anomaly of a group of matrix product operators real

Let `𝒯 = v^{⊗N} K` be an antiunitary time reversal, with `v` unitary and `K` complex
conjugation, and let `g ↦ O_g` be a group of matrix product operators with normal tensors.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563, Section `sec:TRS`, lines 865--891) impose
`𝒯 O_g = O_g 𝒯` and conclude that the anomaly three-cocycle `ω` is cohomologous to its
complex conjugate, hence to a real three-cocycle.

The argument is formalized at the level of the tensors.

* The time-reversed tensor `MPOTensor.timeReversal v T`, with letters
  `∑_{k,l} v_{ik} (T^{kl})^* (v_{jl})^*`, generates `𝒯 O 𝒯⁻¹ = v^{⊗N} O^* v^{⊗N †}`.
* Commutation with `𝒯` makes the time-reversed tensor of `O_g` generate `O_g` itself. Since the
  bond dimensions agree, the single-block reduction theorem gives an exact invertible bond
  gauge `q_g` between the two tensors: the matrices `q_g` of source line 870.
* Complex conjugation of the fusion tensors gives fusion tensors of the time-reversed family
  whose associator is `ω^*`.
* Transporting them along the bond gauges `q_g` gives fusion tensors of the original family
  with associator `ω^*`. Any two choices of fusion tensors give cohomologous associators, so
  `ω` is cohomologous to `ω^*`, which is the source's display at lines 889--890 with
  `β_{g,h}` the relative scalar of the two choices.

The scalar conclusion, that a three-cochain cohomologous to its conjugate is cohomologous to a
real one, is `TNLean.Algebra.ScalarThreeCochain.exists_cohomologousTo_star_eq_self`.

The gauge transport of fusion tensors along exact bond gauges is stated for an arbitrary
family with the same bond dimensions; it shows that the associator is unchanged.

## Main definitions

* `MPOTensor.timeReversal`: the tensor generating `𝒯 O 𝒯⁻¹`.
* `MPOTensor.GroupFamily.CommutesWithTimeReversal`: `𝒯 O_g = O_g 𝒯` for every `g`.
* `MPOTensor.GroupFamily.withTensor`: a family with the same bond dimensions and new tensors.
* `MPOTensor.GroupFamily.FusionData.gaugeTransport`: fusion tensors transported along exact
  bond gauges.
* `MPOTensor.GroupFamily.FusionData.timeReversal`: the conjugated fusion tensors of the
  time-reversed family.

## Main results

* `MPOTensor.mpo_timeReversal`: `O(𝒯T) = v^{⊗N} O(T)^* v^{⊗N †}`.
* `MPOTensor.GroupFamily.FusionData.isAssociator_gaugeTransport`: the associator is unchanged
  by a gauge transport.
* `MPOTensor.GroupFamily.FusionData.isAssociator_timeReversal`: the conjugated fusion tensors
  have associator `ω^*`.
* `MPOTensor.GroupFamily.FusionData.omega_cohomologousTo_star_of_timeReversal`: commutation
  with time reversal makes `ω` cohomologous to `ω^*`.
* `MPOTensor.GroupFamily.FusionData.exists_real_cohomologousTo_omega_of_timeReversal`: `ω`
  is cohomologous to a real three-cochain.

## References

* Garre-Rubio, Lootens, Molnár, arXiv:2203.12563v3, `REsubmission.tex`, Section `sec:TRS`,
  lines 865--891.
-/

open scoped Matrix Kronecker BigOperators
open TNLean.Algebra

/-! ### Recombining and conjugating letters -/

namespace MPSTensor

variable {d D D' m : ℕ}

private theorem evalWord_append_singleton (K : MPSTensor d D) (u : List (Fin d)) (a : Fin d) :
    Kraus.evalWord K (u ++ [a]) = Kraus.evalWord K u * K a := by
  rw [Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]

/-- Word evaluation commutes with entrywise complex conjugation of the letters. -/
private theorem evalWord_map_starRingEnd (K : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (fun i ↦ (K i).map (starRingEnd ℂ)) w =
      (Kraus.evalWord K w).map (starRingEnd ℂ) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih, Matrix.map_mul]

namespace IsReduction

variable {B : MPSTensor d D} {A : MPSTensor d D'}
  {V : Matrix (Fin D') (Fin D) ℂ} {W : Matrix (Fin D) (Fin D') ℂ}

/-- A reduction persists when the letters of both tensors are replaced by the same linear
combinations `∑_a c_{ia} B^a` and `∑_a c_{ia} A^a`. -/
theorem recombine (h : IsReduction B A V W) (c : Fin d → Fin d → ℂ) :
    IsReduction (fun i ↦ ∑ a, c i a • B a) (fun i ↦ ∑ a, c i a • A a) V W := by
  refine ⟨h.mul_eq_one, fun w ↦ ?_⟩
  suffices H : ∀ u, V * (Kraus.evalWord B u *
      Kraus.evalWord (fun i ↦ ∑ a, c i a • B a) w) * W =
        Kraus.evalWord A u * Kraus.evalWord (fun i ↦ ∑ a, c i a • A a) w by
    simpa using H []
  induction w with
  | nil => intro u; simpa using h.evalWord u
  | cons i w ih =>
      intro u
      simp only [Kraus.evalWord_cons, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
        Matrix.mul_smul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      have := ih (u ++ [a])
      rw [evalWord_append_singleton, evalWord_append_singleton] at this
      simpa only [Matrix.mul_assoc] using congrArg (c i a • ·) this

/-- Entrywise complex conjugation of the tensors and of the boundaries preserves a
reduction. -/
theorem map_starRingEnd (h : IsReduction B A V W) :
    IsReduction (fun i ↦ (B i).map (starRingEnd ℂ)) (fun i ↦ (A i).map (starRingEnd ℂ))
      (V.map (starRingEnd ℂ)) (W.map (starRingEnd ℂ)) := by
  refine ⟨by rw [← Matrix.map_mul, h.mul_eq_one, Matrix.map_one _ (map_zero _) (map_one _)],
    fun w ↦ ?_⟩
  rw [evalWord_map_starRingEnd, evalWord_map_starRingEnd, ← Matrix.map_mul, ← Matrix.map_mul,
    h.evalWord]

/-- A reduction with target letters `A' = Q A Q⁻¹` gives a reduction onto `A`. -/
theorem target_gauge {A' : MPSTensor d D'} {V : Matrix (Fin D') (Fin D) ℂ}
    {W : Matrix (Fin D) (Fin D') ℂ} {P Q : Matrix (Fin D') (Fin D') ℂ}
    (h : IsReduction B A' V W) (hPQ : P * Q = 1) (hA : ∀ i, A' i * Q = Q * A i) :
    IsReduction B A (P * V) (W * Q) := by
  refine ⟨by rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, h.mul_eq_one, Matrix.one_mul, hPQ],
    fun w ↦ ?_⟩
  calc P * V * Kraus.evalWord B w * (W * Q) = P * (V * Kraus.evalWord B w * W) * Q := by
        simp only [Matrix.mul_assoc]
    _ = Kraus.evalWord A w := by
        rw [h.evalWord, Matrix.mul_assoc, Kraus.evalWord_intertwine _ _ _ hA,
          ← Matrix.mul_assoc, hPQ, Matrix.one_mul]

end IsReduction

namespace IsDressedProportional

variable {B : MPSTensor d D} {X Y : Matrix (Fin m) (Fin D) ℂ} {z : ℂ}

/-- Dressed proportionality persists when the letters are replaced by linear combinations
`∑_a c_{ia} B^a`: a word of the new letters is a combination of words of the old letters of
the same length. -/
theorem recombine (h : IsDressedProportional B X Y z) (c : Fin d → Fin d → ℂ) :
    IsDressedProportional (fun i ↦ ∑ a, c i a • B a) X Y z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  suffices H : ∀ u : List (Fin d), N ≤ u.length + w.length →
      X * (Kraus.evalWord B u * Kraus.evalWord (fun i ↦ ∑ a, c i a • B a) w) =
        z • (Y * (Kraus.evalWord B u * Kraus.evalWord (fun i ↦ ∑ a, c i a • B a) w)) by
    simpa using H [] (by simpa using hw)
  clear hw
  induction w with
  | nil => intro u hu; simpa using h u (by simpa using hu)
  | cons i w ih =>
      intro u hu
      simp only [Kraus.evalWord_cons, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
        Matrix.mul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      have := ih (u ++ [a]) (by simp only [List.length_append, List.length_cons] at hu ⊢; omega)
      rw [evalWord_append_singleton] at this
      rw [smul_comm z (c i a)]
      simpa only [Matrix.mul_assoc] using congrArg (c i a • ·) this

/-- Entrywise complex conjugation of the tensor and of the boundaries conjugates the scalar
of a dressed proportionality. -/
theorem map_starRingEnd (h : IsDressedProportional B X Y z) :
    IsDressedProportional (fun i ↦ (B i).map (starRingEnd ℂ)) (X.map (starRingEnd ℂ))
      (Y.map (starRingEnd ℂ)) (starRingEnd ℂ z) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [evalWord_map_starRingEnd, ← Matrix.map_mul, ← Matrix.map_mul, h w hw]
  ext p q
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end IsDressedProportional

end MPSTensor

/-! ### The time-reversed tensor -/

namespace MPOTensor

variable {d D D₁ D₂ : ℕ}

/-- **The time-reversed tensor.** For the antiunitary `𝒯 = v^{⊗N} K`, the tensor with letters
`(𝒯T)^{ij} = ∑_{k,l} v_{ik} (T^{kl})^* (v_{jl})^*`, which generates `𝒯 O_T 𝒯⁻¹`
(`MPOTensor.mpo_timeReversal`). Source: arXiv:2203.12563, line 867. -/
noncomputable def timeReversal (v : Matrix (Fin d) (Fin d) ℂ) (T : MPOTensor d D) :
    MPOTensor d D :=
  pairTwist v (v.map (starRingEnd ℂ)) fun i j ↦ (T i j).map (starRingEnd ℂ)

/-- Entrywise conjugation of the letters conjugates every periodic operator. -/
theorem mpo_map_starRingEnd (T : MPOTensor d D) (N : ℕ) :
    mpo (fun i j ↦ (T i j).map (starRingEnd ℂ)) N = (mpo T N).map (starRingEnd ℂ) := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.map_apply]
  have hprod : ∀ l : List (Matrix (Fin D) (Fin D) ℂ),
      l.prod.map (starRingEnd ℂ) = (l.map fun A ↦ A.map (starRingEnd ℂ)).prod :=
    fun l ↦ map_list_prod (starRingEnd ℂ).mapMatrix l
  rw [AddMonoidHom.map_trace (starRingEnd ℂ), hprod, List.map_ofFn]
  rfl

/-- **The time-reversed tensor generates `𝒯 O 𝒯⁻¹`**: for `𝒯 = v^{⊗N} K`,
`O(𝒯T) = v^{⊗N} O(T)^* (v^{⊗N})^†`. Source: arXiv:2203.12563, line 867. -/
theorem mpo_timeReversal (v : Matrix (Fin d) (Fin d) ℂ) (T : MPOTensor d D) (N : ℕ) :
    mpo (timeReversal v T) N =
      Matrix.finKronecker (fun _ : Fin N ↦ v) * (mpo T N).map (starRingEnd ℂ) *
        (Matrix.finKronecker fun _ : Fin N ↦ v)ᴴ := by
  rw [timeReversal, mpo_pairTwist, mpo_map_starRingEnd, Matrix.finKronecker_transpose,
    Matrix.finKronecker_conjTranspose]
  rfl

/-- The doubled-index letters of the time-reversed tensor are linear combinations of the
conjugated doubled-index letters, with the coefficients `v_{ik} (v_{jl})^*` of `v ⊗ v^*`. -/
theorem toMPSTensor_timeReversal (v : Matrix (Fin d) (Fin d) ℂ) (T : MPOTensor d D) :
    (timeReversal v T).toMPSTensor = fun p ↦ ∑ q : Fin (d * d),
      (v p.divNat q.divNat * starRingEnd ℂ (v p.modNat q.modNat)) •
        (T.toMPSTensor q).map (starRingEnd ℂ) := by
  funext p
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [toMPSTensor, timeReversal, pairTwist, Matrix.map_apply, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp

/-- **Time reversal commutes with stacking.** For a unitary `v`, the time-reversed tensor of
the stacked product of two tensors is the stacked product of their time-reversed tensors:
`𝒯(O_1 O_2)𝒯⁻¹ = (𝒯 O_1 𝒯⁻¹)(𝒯 O_2 𝒯⁻¹)` at the level of tensors. -/
theorem mulTensor_timeReversal {v : Matrix (Fin d) (Fin d) ℂ} (hv : star v * v = 1)
    (M : MPOTensor d D₁) (N : MPOTensor d D₂) :
    mulTensor (timeReversal v M) (timeReversal v N) = timeReversal v (mulTensor M N) := by
  have hδ : ∀ b c, ∑ k, starRingEnd ℂ (v k b) * v k c = if b = c then 1 else 0 := by
    intro b c
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hv b) c
  funext i j
  ext r s
  simp only [timeReversal, pairTwist, mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_mul]
  have key : ∀ (a b c e : Fin d) (X Y : ℂ),
      ∑ k, v i a * (starRingEnd ℂ (v k b) * X) * (v k c * (starRingEnd ℂ (v j e) * Y)) =
        if c = b then v i a * (starRingEnd ℂ (v j e) * (X * Y)) else 0 := by
    intro a b c e X Y
    calc _ = (∑ k, starRingEnd ℂ (v k b) * v k c) *
          (v i a * (starRingEnd ℂ (v j e) * (X * Y))) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = _ := by rw [hδ]; split_ifs with h₁ h₂ h₂ <;> simp_all
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, c]
    rw [Finset.sum_comm]
    enter [2, e]
    rw [Finset.sum_comm]
    enter [2, a]
    rw [Finset.sum_comm]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Fintype.sum_reverse_three _

end MPOTensor

namespace MPSTensor

variable {d D D' m : ℕ}

/-- A reduction of tensors gives a reduction of their time-reversed tensors, with conjugated
boundaries. -/
theorem IsReduction.timeReversal {M : MPOTensor d D} {A : MPOTensor d D'}
    {V : Matrix (Fin D') (Fin D) ℂ} {W : Matrix (Fin D) (Fin D') ℂ}
    (h : IsReduction M.toMPSTensor A.toMPSTensor V W) (v : Matrix (Fin d) (Fin d) ℂ) :
    IsReduction (MPOTensor.timeReversal v M).toMPSTensor (MPOTensor.timeReversal v A).toMPSTensor
      (V.map (starRingEnd ℂ)) (W.map (starRingEnd ℂ)) := by
  rw [MPOTensor.toMPSTensor_timeReversal, MPOTensor.toMPSTensor_timeReversal]
  exact h.map_starRingEnd.recombine _

/-- A dressed proportionality of a tensor gives one of its time-reversed tensor, with
conjugated boundaries and conjugated scalar. -/
theorem IsDressedProportional.timeReversal {M : MPOTensor d D} {X Y : Matrix (Fin m) (Fin D) ℂ}
    {z : ℂ} (h : IsDressedProportional M.toMPSTensor X Y z) (v : Matrix (Fin d) (Fin d) ℂ) :
    IsDressedProportional (MPOTensor.timeReversal v M).toMPSTensor (X.map (starRingEnd ℂ))
      (Y.map (starRingEnd ℂ)) (starRingEnd ℂ z) := by
  rw [MPOTensor.toMPSTensor_timeReversal]
  exact h.map_starRingEnd.recombine _

end MPSTensor

/-! ### Kronecker products of bond gauges -/

namespace MPOTensor

variable {d D₁ D₂ D₃ m n n' : ℕ}

/-- The Kronecker product `X ⊗ Y = (X ⊗ 1)(1 ⊗ Y)` of two square bond matrices, on the product
bond space in the bond order of `mulTensor`. -/
noncomputable def bondKron (X : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (m * n)) (Fin (m * n)) ℂ :=
  kronId X n * idKron m Y

/-- The two factors of `X ⊗ Y` commute: `X ⊗ Y = (1 ⊗ Y)(X ⊗ 1)`. -/
theorem bondKron_eq_idKron_mul_kronId (X : Matrix (Fin m) (Fin m) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : bondKron X Y = idKron m Y * kronId X n :=
  kronId_mul_idKron X Y

/-- `(X ⊗ Y)(X' ⊗ Y') = X X' ⊗ Y Y'`. -/
theorem bondKron_mul_bondKron (X X' : Matrix (Fin m) (Fin m) ℂ)
    (Y Y' : Matrix (Fin n) (Fin n) ℂ) :
    bondKron X Y * bondKron X' Y' = bondKron (X * X') (Y * Y') := by
  rw [bondKron, bondKron, bondKron, Matrix.mul_assoc, ← Matrix.mul_assoc (idKron m Y),
    ← kronId_mul_idKron, Matrix.mul_assoc, ← Matrix.mul_assoc (kronId X n), kronId_mul,
    idKron_mul]

/-- `1 ⊗ 1 = 1`. -/
@[simp] theorem bondKron_one :
    bondKron (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [bondKron]

/-- `(X ⊗ Z)(Y ⊗ 1) = (X Y ⊗ 1)(1 ⊗ Z)`. -/
theorem bondKron_mul_kronId (X : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin n') ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    bondKron X Z * kronId Y n = kronId (X * Y) n * idKron n' Z := by
  rw [bondKron, Matrix.mul_assoc, ← kronId_mul_idKron, ← Matrix.mul_assoc, kronId_mul]

/-- `(X ⊗ Z)(1 ⊗ Y) = (1 ⊗ Z Y)(X ⊗ 1)`. -/
theorem bondKron_mul_idKron (X : Matrix (Fin m) (Fin m) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n') ℂ) :
    bondKron X Z * idKron m Y = idKron m (Z * Y) * kronId X n' := by
  rw [bondKron, Matrix.mul_assoc, idKron_mul, kronId_mul_idKron]

/-- Naturality of the bond associator for Kronecker products of square bond matrices. -/
theorem bondKron_bondKron_mul_assocInv (X : Matrix (Fin m) (Fin m) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n') (Fin n') ℂ) :
    bondKron X (bondKron Y Z) * mulTensorAssocInvMatrix m n n' =
      mulTensorAssocInvMatrix m n n' * bondKron (bondKron X Y) Z := by
  symm
  calc mulTensorAssocInvMatrix m n n' * bondKron (bondKron X Y) Z
      = mulTensorAssocInvMatrix m n n' * (kronId (kronId X n) n' *
          (kronId (idKron m Y) n' * idKron (m * n) Z)) := by
        rw [bondKron, bondKron, ← kronId_mul, Matrix.mul_assoc]
    _ = kronId X (n * n') * (idKron m (kronId Y n') *
          (idKron m (idKron n Z) * mulTensorAssocInvMatrix m n n')) := by
        rw [← Matrix.mul_assoc, assocInv_mul_kronId_kronId, Matrix.mul_assoc,
          assocInv_mul_kronId_idKron_assoc, assocInv_mul_idKron]
    _ = _ := by rw [bondKron, bondKron, ← idKron_mul]; simp only [Matrix.mul_assoc]

/-- Intertwiners of the factors give an intertwiner of the stacked letters. -/
theorem mulTensor_mul_bondKron_of_intertwine {A A' : MPOTensor d m} {B B' : MPOTensor d n}
    {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i l, A' i l * P = P * A i l) (hB : ∀ i l, B' i l * Q = Q * B i l) (i l : Fin d) :
    mulTensor A' B' i l * bondKron P Q = bondKron P Q * mulTensor A B i l := by
  rw [bondKron, ← Matrix.mul_assoc, mulTensor_mul_kronId_of_intertwine B' hA, Matrix.mul_assoc,
    mulTensor_mul_idKron_of_intertwine A hB, ← Matrix.mul_assoc]

private theorem pequiv_toMatrix_map_starRingEnd {α β : Type*} [DecidableEq β]
    (f : α ≃ β) : f.toPEquiv.toMatrix.map (starRingEnd ℂ) = f.toPEquiv.toMatrix := by
  ext p q
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

/-- Entrywise conjugation commutes with `X ↦ X ⊗ 1`. -/
theorem kronId_map_starRingEnd (X : Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    (kronId X D).map (starRingEnd ℂ) = kronId (X.map (starRingEnd ℂ)) D := by
  ext p q
  simp only [kronId, Matrix.map_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    map_mul, Matrix.one_apply]
  split_ifs <;> simp

/-- Entrywise conjugation commutes with `X ↦ 1 ⊗ X`. -/
theorem idKron_map_starRingEnd (D : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    (idKron D X).map (starRingEnd ℂ) = idKron D (X.map (starRingEnd ℂ)) := by
  ext p q
  simp only [idKron, Matrix.map_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    map_mul, Matrix.one_apply]
  split_ifs <;> simp

/-- The inverse bond associator is a real permutation matrix. -/
theorem mulTensorAssocInvMatrix_map_starRingEnd (a b c : ℕ) :
    (mulTensorAssocInvMatrix a b c).map (starRingEnd ℂ) = mulTensorAssocInvMatrix a b c :=
  pequiv_toMatrix_map_starRingEnd _

/-! ### Fusion tensors along exact bond gauges -/

namespace GroupFamily

variable {G : Type} [Group G] {F : GroupFamily G d}

/-- The family with the bond dimensions of `F` and the tensors `T`. -/
abbrev withTensor (F : GroupFamily G d) (T : ∀ g, MPOTensor d (F.bondDim g)) : GroupFamily G d where
  bondDim := F.bondDim
  bondDim_pos := F.bondDim_pos
  tensor := T

omit [Group G] in
/-- Bond identifications are real permutation matrices. -/
theorem castMat_map_starRingEnd {a b : G} (e : a = b) :
    (F.castMat e).map (starRingEnd ℂ) = F.castMat e :=
  pequiv_toMatrix_map_starRingEnd _

omit [Group G] in
/-- A family of square bond matrices commutes with bond identifications. -/
theorem castMat_mul_eq {P : ∀ g, Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ} {a b : G}
    (e : a = b) : F.castMat e * P a = P b * F.castMat e := by
  subst e
  simp

/-- **Exact bond gauges** from tensors `T g` to the tensors of `F`: mutually inverse matrices
`P g`, `Q g` with `T_g^{il} Q_g = Q_g F_g^{il}`. These are the matrices `q_g` of
arXiv:2203.12563, line 870. -/
structure BondGauge (F : GroupFamily G d) (T : ∀ g, MPOTensor d (F.bondDim g)) where
  /-- The inverse gauge. -/
  P : ∀ g, Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ
  /-- The gauge. -/
  Q : ∀ g, Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ
  P_mul_Q : ∀ g, P g * Q g = 1
  Q_mul_P : ∀ g, Q g * P g = 1
  intertwine : ∀ g i l, T g i l * Q g = Q g * F.tensor g i l

namespace BondGauge

variable {T : ∀ g, MPOTensor d (F.bondDim g)} (q : BondGauge F T)

include q in
omit [Group G] in
/-- The inverse gauge intertwines in the opposite direction: `F_g^{il} P_g = P_g T_g^{il}`. -/
theorem mul_P (g : G) (i l : Fin d) : F.tensor g i l * q.P g = q.P g * T g i l := by
  calc F.tensor g i l * q.P g = q.P g * (q.Q g * F.tensor g i l) * q.P g := by
        rw [← Matrix.mul_assoc, q.P_mul_Q, Matrix.one_mul]
    _ = q.P g * T g i l := by
        rw [← q.intertwine, Matrix.mul_assoc, Matrix.mul_assoc, q.Q_mul_P, Matrix.mul_one]

end BondGauge

namespace FusionData

variable {T : ∀ g, MPOTensor d (F.bondDim g)}

/-- **Gauge transport of fusion tensors.** Fusion tensors `(V, W)` of the tensors `T g` give
fusion tensors `(P_{gh} V (Q_g ⊗ Q_h), (P_g ⊗ P_h) W Q_{gh})` of `F`, for exact bond gauges
`(P, Q)` from `T` to `F`. -/
noncomputable def gaugeTransport (fd : FusionData (F.withTensor T)) (q : BondGauge F T) :
    FusionData F where
  V g h := q.P (g * h) * (fd.V g h * bondKron (q.Q g) (q.Q h))
  W g h := bondKron (q.P g) (q.P h) * fd.W g h * q.Q (g * h)
  isReduction g h := by
    have h1 := (fd.isReduction g h).of_intertwine
      (B' := (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor)
      (P := bondKron (q.P g) (q.P h)) (Q := bondKron (q.Q g) (q.Q h))
      (by rw [bondKron_mul_bondKron, q.Q_mul_P, q.Q_mul_P, bondKron_one])
      (fun i ↦ mulTensor_mul_bondKron_of_intertwine (q.mul_P g) (q.mul_P h) i.divNat i.modNat)
    exact h1.target_gauge (q.P_mul_Q _) (fun i ↦ q.intertwine _ _ _)

variable (fd : FusionData (F.withTensor T)) (q : BondGauge F T)

/-- The first fusion tree of the transported fusion tensors is
`P_{ghk} V^L (Q_g ⊗ Q_h ⊗ Q_k)`. -/
theorem gaugeTransport_leftV (g h k : G) :
    (fd.gaugeTransport q).leftV g h k =
      q.P (g * h * k) * (fd.leftV g h k * bondKron (bondKron (q.Q g) (q.Q h)) (q.Q k)) := by
  simp only [leftV, gaugeTransport]
  rw [Matrix.mul_assoc (q.P _), Matrix.mul_assoc (fd.V _ _), bondKron_mul_kronId,
    ← Matrix.mul_assoc (q.Q _), q.Q_mul_P, Matrix.one_mul, ← kronId_mul]
  simp only [bondKron, Matrix.mul_assoc]

/-- The second fusion tree of the transported fusion tensors is
`P_{ghk} V^R (Q_g ⊗ Q_h ⊗ Q_k)`. -/
theorem gaugeTransport_rightV (g h k : G) :
    (fd.gaugeTransport q).rightV g h k =
      q.P (g * h * k) * (fd.rightV g h k * bondKron (bondKron (q.Q g) (q.Q h)) (q.Q k)) := by
  simp only [rightV, gaugeTransport]
  rw [Matrix.mul_assoc (q.P _), Matrix.mul_assoc (fd.V _ _), bondKron_mul_idKron,
    ← Matrix.mul_assoc (q.Q _), q.Q_mul_P, Matrix.one_mul, ← idKron_mul]
  have e : idKron (F.bondDim g) (bondKron (q.Q h) (q.Q k)) *
      (kronId (q.Q g) (F.bondDim h * F.bondDim k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) =
      mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k) *
        bondKron (bondKron (q.Q g) (q.Q h)) (q.Q k) := by
    rw [← Matrix.mul_assoc, ← bondKron_eq_idKron_mul_kronId, bondKron_bondKron_mul_assocInv]
  simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mul_assoc (F.castMat _), castMat_mul_eq, Matrix.mul_assoc]
  rfl

/-- **The associator is unchanged by a gauge transport**: the two fusion trees of the
transported fusion tensors compare by the same scalar as those of the original ones. -/
theorem isAssociator_gaugeTransport {g h k : G} {z : ℂ} (hz : fd.IsAssociator g h k z) :
    (fd.gaugeTransport q).IsAssociator g h k z := by
  have hB : ∀ i, (F.tripleTensor g h k).toMPSTensor i *
      bondKron (bondKron (q.P g) (q.P h)) (q.P k) =
        bondKron (bondKron (q.P g) (q.P h)) (q.P k) *
          ((F.withTensor T).tripleTensor g h k).toMPSTensor i := fun i ↦
    mulTensor_mul_bondKron_of_intertwine
      (mulTensor_mul_bondKron_of_intertwine (q.mul_P g) (q.mul_P h)) (q.mul_P k) _ _
  have h1 := hz.of_intertwine (B' := (F.tripleTensor g h k).toMPSTensor)
    (by rw [bondKron_mul_bondKron, bondKron_mul_bondKron, q.P_mul_Q, q.P_mul_Q, q.P_mul_Q,
      bondKron_one, bondKron_one])
    (by rw [bondKron_mul_bondKron, bondKron_mul_bondKron, q.Q_mul_P, q.Q_mul_P, q.Q_mul_P,
      bondKron_one, bondKron_one]) hB
  unfold IsAssociator
  rw [gaugeTransport_leftV, gaugeTransport_rightV]
  exact h1.mul_left _

end FusionData

end GroupFamily

end MPOTensor

/-! ### Time reversal and the anomaly -/

namespace MPOTensor.GroupFamily

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d} {v : Matrix (Fin d) (Fin d) ℂ}

/-- **Commutation with time reversal.** The antiunitary `𝒯 = v^{⊗N} K` commutes with every
periodic operator of the family on every nonempty chain: `𝒯 O_g = O_g 𝒯`, that is,
`v^{⊗N} O_g^* = O_g v^{⊗N}`. Source: arXiv:2203.12563, line 869. -/
def CommutesWithTimeReversal (F : GroupFamily G d) (v : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g N, 0 < N → Matrix.finKronecker (fun _ : Fin N ↦ v) *
    (mpo (F.tensor g) N).map (starRingEnd ℂ) = mpo (F.tensor g) N * Matrix.finKronecker fun _ ↦ v

namespace FusionData

/-- **Fusion tensors of the time-reversed family.** For a unitary `v`, the entrywise conjugates
of fusion tensors of `F` are fusion tensors of the time-reversed tensors
`g ↦ 𝒯 O_g 𝒯⁻¹`. Source: arXiv:2203.12563, lines 871--889, where the conjugated fusion
tensors are compared with the original ones. -/
noncomputable def timeReversal (fd : FusionData F) (hv : star v * v = 1) :
    FusionData (F.withTensor fun g ↦ MPOTensor.timeReversal v (F.tensor g)) where
  V g h := (fd.V g h).map (starRingEnd ℂ)
  W g h := (fd.W g h).map (starRingEnd ℂ)
  isReduction g h := by
    change MPSTensor.IsReduction (mulTensor (MPOTensor.timeReversal v (F.tensor g))
      (MPOTensor.timeReversal v (F.tensor h))).toMPSTensor
      (MPOTensor.timeReversal v (F.tensor (g * h))).toMPSTensor _ _
    rw [mulTensor_timeReversal hv]
    exact (fd.isReduction g h).timeReversal v

variable (fd : FusionData F) (hv : star v * v = 1)

/-- The first fusion tree of the conjugated fusion tensors is the conjugate of the first
fusion tree. -/
theorem timeReversal_leftV (g h k : G) :
    (fd.timeReversal hv).leftV g h k = (fd.leftV g h k).map (starRingEnd ℂ) := by
  simp only [leftV, timeReversal, Matrix.map_mul, kronId_map_starRingEnd]

/-- The second fusion tree of the conjugated fusion tensors is the conjugate of the second
fusion tree. -/
theorem timeReversal_rightV (g h k : G) :
    (fd.timeReversal hv).rightV g h k = (fd.rightV g h k).map (starRingEnd ℂ) := by
  simp only [rightV, timeReversal, Matrix.map_mul, idKron_map_starRingEnd,
    castMat_map_starRingEnd, mulTensorAssocInvMatrix_map_starRingEnd]
  rfl

variable {fd} in
/-- **Conjugation of the associator.** If `ω(g,h,k) = z` for fusion tensors of `F`, then the
conjugated fusion tensors of the time-reversed family have associator `z^*`. -/
theorem isAssociator_timeReversal {g h k : G} {z : ℂ} (hz : fd.IsAssociator g h k z) :
    (fd.timeReversal hv).IsAssociator g h k (starRingEnd ℂ z) := by
  have htriple : (F.withTensor fun g ↦ MPOTensor.timeReversal v (F.tensor g)).tripleTensor
      g h k = MPOTensor.timeReversal v (F.tripleTensor g h k) := by
    change mulTensor (mulTensor (MPOTensor.timeReversal v (F.tensor g))
      (MPOTensor.timeReversal v (F.tensor h))) (MPOTensor.timeReversal v (F.tensor k)) = _
    rw [mulTensor_timeReversal hv, mulTensor_timeReversal hv]
  unfold IsAssociator
  rw [timeReversal_leftV, timeReversal_rightV, htriple]
  exact hz.timeReversal v

end FusionData

/-- **The gauges `q_g` of a time-reversal symmetry.** If the time reversal `𝒯 = v^{⊗N} K`
commutes with every periodic operator `O_g` of a group with normal tensors, then the
time-reversed tensor of each `O_g` is related to the tensor of `O_g` by an exact invertible
bond gauge. Source: arXiv:2203.12563, lines 869--870, "there are matrices `q_g` that
satisfy `∑ v_{ik} T_g^{kl} v⁻¹_{lj} = q_g⁻¹ (T_g^{ij})^* q_g`". The gauge comes from the
single-block reduction theorem: both tensors generate the same operators, and their bond
dimensions agree. -/
theorem nonempty_bondGauge_timeReversal (hF : F.IsNormalRepresentation)
    (hv : v ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hT : F.CommutesWithTimeReversal v) :
    Nonempty (BondGauge F fun g ↦ MPOTensor.timeReversal v (F.tensor g)) := by
  have hsame : ∀ g N, 0 < N →
      mpo (MPOTensor.timeReversal v (F.tensor g)) N = mpo (F.tensor g) N := by
    intro g N hN
    have hV : Matrix.finKronecker (fun _ : Fin N ↦ v) *
        (Matrix.finKronecker fun _ : Fin N ↦ v)ᴴ = 1 :=
      mul_eq_one_comm.mp (Matrix.finKronecker_conjTranspose_mul_self
        (by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hv))
    rw [mpo_timeReversal, hT g N hN, Matrix.mul_assoc, hV, Matrix.mul_one]
  have key : ∀ g, ∃ P Q : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ,
      P * Q = 1 ∧ Q * P = 1 ∧
        ∀ i l, MPOTensor.timeReversal v (F.tensor g) i l * Q = Q * F.tensor g i l := by
    intro g
    obtain ⟨P, Q, hred, -⟩ := MPSTensor.exists_isReduction_and_nilpotent_of_isNormal
      (F.tensor g).toMPSTensor (hF.isNormal g) (F.bondDim_pos g)
      (MPOTensor.timeReversal v (F.tensor g)).toMPSTensor
      (sameMPV₂Pos_toMPSTensor_of_mpo_eq (hsame g))
    have hPQ := hred.mul_eq_one
    have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
    refine ⟨P, Q, hPQ, hQP, fun i l ↦ ?_⟩
    have h1 := hred.evalWord [finProdFinEquiv (i, l)]
    simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, toMPSTensor] at h1
    have e : ((finProdFinEquiv (i, l)).divNat, (finProdFinEquiv (i, l)).modNat) = (i, l) :=
      finProdFinEquiv.symm_apply_apply (i, l)
    rw [Prod.mk.injEq] at e
    rw [e.1, e.2] at h1
    calc MPOTensor.timeReversal v (F.tensor g) i l * Q =
        Q * (P * MPOTensor.timeReversal v (F.tensor g) i l * Q) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      _ = Q * F.tensor g i l := by rw [h1]
  choose P Q hPQ hQP hint using key
  exact ⟨⟨P, Q, hPQ, hQP, hint⟩⟩

namespace FusionData

/-- **Time reversal makes the anomaly cohomologous to its conjugate.** Let `g ↦ O_g` be a
group of matrix product operators with normal tensors, and let the antiunitary time reversal
`𝒯 = v^{⊗N} K`, with `v` unitary, commute with every `O_g` on every nonempty chain. Then the
anomaly three-cochain of any choice of fusion tensors is cohomologous to its complex conjugate.

Source: arXiv:2203.12563, lines 869--890: from `𝒯 O_g = O_g 𝒯` the source obtains the gauges
`q_g`, compares the conjugated fusion tensors with the original ones by scalars `β_{g,h}`,
and concludes `ω = ω^* β_{g,h} β_{gh,k} / (β_{h,k} β_{g,hk})`. -/
theorem omega_cohomologousTo_star_of_timeReversal (hF : F.IsNormalRepresentation)
    (fd : FusionData F) (hv : v ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hT : F.CommutesWithTimeReversal v) :
    ScalarThreeCochain.CohomologousTo fd.omega (star fd.omega) := by
  obtain ⟨q⟩ := nonempty_bondGauge_timeReversal hF hv hT
  have hv' : star v * v = 1 := Matrix.mem_unitaryGroup_iff'.mp hv
  have hω : ((fd.timeReversal hv').gaugeTransport q).omega = star fd.omega := by
    funext g h k
    apply Units.ext
    simp only [Pi.star_apply, Units.coe_star]
    exact (eq_omega_of_isAssociator hF (isAssociator_gaugeTransport _ q
      (isAssociator_timeReversal hv' (isAssociator_omega hF g h k)))).symm
  have h := omega_cohomologousTo hF fd ((fd.timeReversal hv').gaugeTransport q)
  rw [hω] at h
  exact h.symm

/-- **Time reversal makes the anomaly real.** Under the hypotheses of
`MPOTensor.GroupFamily.FusionData.omega_cohomologousTo_star_of_timeReversal`, the anomaly
three-cochain is cohomologous to a real-valued three-cochain.

Source: arXiv:2203.12563, line 891: "which means that `ω` can be gauge transformed to a real
number". -/
theorem exists_real_cohomologousTo_omega_of_timeReversal (hF : F.IsNormalRepresentation)
    (fd : FusionData F) (hv : v ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hT : F.CommutesWithTimeReversal v) :
    ∃ ω' : ScalarThreeCochain G,
      ScalarThreeCochain.CohomologousTo ω' fd.omega ∧ star ω' = ω' :=
  ScalarThreeCochain.exists_cohomologousTo_star_eq_self
    (omega_cohomologousTo_star_of_timeReversal hF fd hv hT)

end FusionData

end MPOTensor.GroupFamily
