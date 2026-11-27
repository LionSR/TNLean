/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Operator.Defs
import TNLean.MPS.CanonicalForm.SimpleMPO.SimpleScaling
import TNLean.MPS.Symmetry.MPOSymmetry.Anomaly.TimeReversalAnomaly

/-!
# The anomaly is unchanged by an on-site change of basis and by a character

Let `g ↦ O_g` be a group of matrix product operators with normal tensors and a choice of fusion
tensors, with anomaly three-cocycle `ω` (arXiv:2502.20257, display preceding `eq:3-cocycle`,
`main.tex` lines 1506--1535). Two operations on the tensors leave `ω` unchanged.

* **An on-site unitary change of physical basis.** Replacing every letter by `u T^{kl} u^†`,
  that is the tensor `pairTwist u \bar u T`, conjugates every periodic operator by `u^{⊗N}`.
  Stacking commutes with the change of basis, and the doubled-index letters of the new tensors
  are fixed linear combinations of the old ones, so the same fusion tensors reduce the new
  stacked products and compare the two fusion trees by the same scalar.
* **A character.** Replacing `T_g` by `χ(g) T_g`, for nonzero scalars with
  `χ(g) χ(h) = χ(gh)`, multiplies `O_g` by `χ(g)^N`. Stacking multiplies the scalars, so again
  the same fusion tensors work with the same associator.

In both cases the new family is again a normal representation, and the anomaly three-cochain
of the transported fusion tensors is literally the old one.

## Main definitions

* `MPOTensor.GroupFamily.FusionData.physicalTwist`: fusion tensors after a change of basis.
* `MPOTensor.GroupFamily.FusionData.smulTensor`: fusion tensors after a character.

## Main results

* `MPOTensor.mulTensor_pairTwist_map_star`: a unitary change of basis commutes with stacking.
* `MPOTensor.GroupFamily.IsNormalRepresentation.withTensor_pairTwist`,
  `MPOTensor.GroupFamily.FusionData.omega_physicalTwist`: invariance under a change of basis.
* `MPOTensor.GroupFamily.IsNormalRepresentation.withTensor_smul`,
  `MPOTensor.GroupFamily.FusionData.omega_smulTensor`: invariance under a character.
-/

open MPTensor

open scoped Matrix BigOperators

/-! ### Normality from a spanning family of letters -/

namespace MPSTensor

variable {d d' D : ℕ}

/-- If every letter of `A` is a linear combination of the letters of `B`, then the words of `A`
of each length lie in the span of the words of `B` of the same length. -/
theorem wordSpan_le_of_forall_mem_span {A : MPSTensor d D} {B : MPSTensor d' D}
    (h : ∀ a, A a ∈ Submodule.span ℂ (Set.range B)) (N : ℕ) :
    Kraus.wordSpan A N ≤ Kraus.wordSpan B N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Kraus.wordSpan_succ A, Kraus.wordSpan_succ B]
      refine mul_le_mul' ih ?_
      rw [Kraus.wordSpan_one, Kraus.wordSpan_one]
      exact Submodule.span_le.2 (Set.range_subset_iff.2 h)

/-- A tensor whose letters span the letters of a normal tensor is normal. -/
theorem isNormal_of_forall_mem_span {A : MPSTensor d D} {B : MPSTensor d' D}
    (h : ∀ a, A a ∈ Submodule.span ℂ (Set.range B)) (hA : Kraus.IsNormal A) :
    Kraus.IsNormal B := by
  obtain ⟨N, hN, hA⟩ := hA
  refine ⟨N, hN, ?_⟩
  unfold Kraus.IsNBlkInjective at hA ⊢
  exact eq_top_iff.2 (hA.symm.le.trans (wordSpan_le_of_forall_mem_span h N))

section IsDressedProportional

open MPTensor.IsDressedProportional

variable {m : ℕ} {B : MPSTensor d D} {X Y : Matrix (Fin m) (Fin D) ℂ} {z : ℂ}

/-- Dressed proportionality persists when every letter is multiplied by the same scalar. -/
theorem _root_.MPTensor.IsDressedProportional.smul (h : IsDressedProportional B X Y z) (c : ℂ) :
    IsDressedProportional (fun i ↦ c • B i) X Y z := by
  simpa [ite_smul] using h.recombine fun i a ↦ if i = a then c else 0

end IsDressedProportional

end MPSTensor

/-! ### An on-site change of physical basis -/

namespace MPOTensor

variable {d D D₁ D₂ : ℕ}

/-- Two physical twists compose: `pairTwist a b (pairTwist u v M) = pairTwist (a u) (b v) M`. -/
theorem pairTwist_pairTwist (a b u v : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) :
    pairTwist a b (pairTwist u v M) = pairTwist (a * u) (b * v) M := by
  funext ⟨i, j⟩
  ext r c
  simp only [pairTwist, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, k]; rw [Finset.sum_comm]
    enter [2, k']; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k']; rw [Finset.sum_comm]
    enter [2, l']; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The trivial physical twist is the identity. -/
@[simp] theorem pairTwist_one_one (M : MPOTensor d D) : pairTwist 1 1 M = M := by
  funext ⟨i, j⟩
  simp [pairTwist, Matrix.one_apply, ite_smul]

/-- A unitary change of physical basis is undone by the adjoint change of basis. -/
theorem pairTwist_star_pairTwist {u : Matrix (Fin d) (Fin d) ℂ} (hu : star u * u = 1)
    (M : MPOTensor d D) :
    pairTwist (star u) ((star u).map (starRingEnd ℂ))
      (pairTwist u (u.map (starRingEnd ℂ)) M) = M := by
  rw [pairTwist_pairTwist, hu, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _),
    pairTwist_one_one]

/-- The doubled-index letters of a physical twist are linear combinations of the doubled-index
letters of the original tensor, with the coefficients `u_{ik} v_{jl}` of `u ⊗ v`. -/
theorem toMPSTensor_pairTwist (u v : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) :
    (pairTwist u v M).toMPSTensor = fun p ↦ ∑ q : Fin (d * d),
      (u p.divNat q.divNat * v p.modNat q.modNat) • M.toMPSTensor q := by
  funext p
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [toMPSTensor, pairTwist, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp

/-- **A unitary change of physical basis commutes with stacking**: for a unitary `u`, the
stacked product of `u M u^†` and `u N u^†` is `u (M N) u^†`, at the level of tensors. -/
theorem mulTensor_pairTwist_map_star {u : Matrix (Fin d) (Fin d) ℂ} (hu : star u * u = 1)
    (M : MPOTensor d D₁) (N : MPOTensor d D₂) :
    mulTensor (pairTwist u (u.map (starRingEnd ℂ)) M) (pairTwist u (u.map (starRingEnd ℂ)) N) =
      pairTwist u (u.map (starRingEnd ℂ)) (mulTensor M N) := by
  have hδ : ∀ b c, ∑ k, starRingEnd ℂ (u k b) * u k c = if b = c then 1 else 0 := by
    intro b c
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hu b) c
  funext ⟨i, j⟩
  ext r s
  simp only [pairTwist, mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  have key : ∀ (a b c e : Fin d) (X Y : ℂ),
      ∑ k, u i a * (starRingEnd ℂ (u k b) * X) * (u k c * (starRingEnd ℂ (u j e) * Y)) =
        if c = b then u i a * (starRingEnd ℂ (u j e) * (X * Y)) else 0 := by
    intro a b c e X Y
    calc _ = (∑ k, starRingEnd ℂ (u k b) * u k c) *
          (u i a * (starRingEnd ℂ (u j e) * (X * Y))) := by
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

/-- A unitary change of physical basis fixes the identity tensor. -/
theorem pairTwist_idTensor {u : Matrix (Fin d) (Fin d) ℂ} (hu : star u * u = 1) :
    pairTwist u (u.map (starRingEnd ℂ)) (idTensor d) = idTensor d := by
  have hu' : u * star u = 1 := mul_eq_one_comm.1 hu
  funext ⟨i, j⟩
  have hij := congrFun (congrFun hu' i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, RCLike.star_def] at hij
  simp only [pairTwist, idTensor, Matrix.map_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, smul_smul, ← Finset.sum_smul, hij]
  split_ifs <;> simp

end MPOTensor

/-! ### Transport of fusion tensors -/

namespace MPOTensor.GroupFamily

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d}

section PhysicalTwist

variable {u : Matrix (Fin d) (Fin d) ℂ} {T : ∀ g, MPOTensor d (F.bondDim g)}

/-- **A change of physical basis of a normal representation is a normal representation.** If
`T_g = u F_g u^†` for a unitary `u`, the operators of `T` are `u^{⊗N} O_g (u^{⊗N})^†`, which
multiply as the group, and the letters of `F_g` are combinations of the letters of `T_g`. -/
theorem IsNormalRepresentation.withTensor_pairTwist (hF : F.IsNormalRepresentation)
    (hu : star u * u = 1) (hT : ∀ g, T g = pairTwist u (u.map (starRingEnd ℂ)) (F.tensor g)) :
    (F.withTensor T).IsNormalRepresentation where
  isNormal g := by
    change Kraus.IsNormal (T g).toMPSTensor
    refine MPSTensor.isNormal_of_forall_mem_span (fun a ↦ ?_) (hF.isNormal g)
    rw [← pairTwist_star_pairTwist hu (F.tensor g), ← hT, toMPSTensor_pairTwist]
    exact Submodule.sum_mem _ fun q _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  operator_mul g h N hN := by
    change mpo (T g) N * mpo (T h) N = mpo (T (g * h)) N
    simp only [hT]
    rw [← mpo_mulTensor, mulTensor_pairTwist_map_star hu, mpo_pairTwist, mpo_pairTwist,
      mpo_mulTensor, hF.operator_mul g h N hN]

namespace FusionData

/-- **Fusion tensors after a change of physical basis.** If `T_g = u F_g u^†` for a unitary
`u`, the fusion tensors of `F` are fusion tensors of `T`. -/
noncomputable def physicalTwist (fd : FusionData F) (hu : star u * u = 1)
    (hT : ∀ g, T g = pairTwist u (u.map (starRingEnd ℂ)) (F.tensor g)) :
    FusionData (F.withTensor T) where
  V := fd.V
  W := fd.W
  isReduction g h := by
    change MPTensor.IsReduction (mulTensor (T g) (T h)).toMPSTensor (T (g * h)).toMPSTensor
      (fd.V g h) (fd.W g h)
    simp only [hT]
    rw [mulTensor_pairTwist_map_star hu, toMPSTensor_pairTwist, toMPSTensor_pairTwist]
    exact (fd.isReduction g h).recombine _

/-- The two fusion trees of the transported fusion tensors compare by the same scalar. -/
theorem isAssociator_physicalTwist {fd : FusionData F} (hu : star u * u = 1)
    (hT : ∀ g, T g = pairTwist u (u.map (starRingEnd ℂ)) (F.tensor g)) {g h k : G} {z : ℂ}
    (hz : fd.IsAssociator g h k z) : (fd.physicalTwist hu hT).IsAssociator g h k z := by
  change MPTensor.IsDressedProportional (mulTensor (mulTensor (T g) (T h)) (T k)).toMPSTensor
    (fd.leftV g h k) (fd.rightV g h k) z
  simp only [hT]
  rw [mulTensor_pairTwist_map_star hu, mulTensor_pairTwist_map_star hu, toMPSTensor_pairTwist]
  exact hz.recombine _

/-- **The anomaly is unchanged by an on-site unitary change of physical basis**: the transported
fusion tensors have literally the same anomaly three-cochain.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535 (the
definition of `ω`). -/
theorem omega_physicalTwist (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (hu : star u * u = 1) (hT : ∀ g, T g = pairTwist u (u.map (starRingEnd ℂ)) (F.tensor g)) :
    (fd.physicalTwist hu hT).omega = fd.omega := by
  funext g h k
  exact Units.ext (eq_omega_of_isAssociator (hF.withTensor_pairTwist hu hT)
    (isAssociator_physicalTwist hu hT (isAssociator_omega hF g h k))).symm

end FusionData

end PhysicalTwist

section Character

variable {χ : G → ℂ} {T : ∀ g, MPOTensor d (F.bondDim g)}

/-- **Multiplying a normal representation by a character gives a normal representation.** If
`T_g = χ(g) F_g` with `χ(g) ≠ 0` and `χ(g) χ(h) = χ(gh)`, the operators of `T` are
`χ(g)^N O_g`. -/
theorem IsNormalRepresentation.withTensor_smul (hF : F.IsNormalRepresentation)
    (hχ : ∀ g h, χ g * χ h = χ (g * h)) (hχ0 : ∀ g, χ g ≠ 0)
    (hT : ∀ g, T g = χ g • F.tensor g) :
    (F.withTensor T).IsNormalRepresentation where
  isNormal g := by
    change Kraus.IsNormal (T g).toMPSTensor
    rw [hT]
    exact (MPSTensor.isNormal_smul_iff (hχ0 g) _).2 (hF.isNormal g)
  operator_mul g h N hN := by
    change mpo (T g) N * mpo (T h) N = mpo (T (g * h)) N
    simp only [hT, mpo_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hF.operator_mul g h N hN, ← mul_pow, mul_comm (χ h), hχ]

namespace FusionData

/-- **Fusion tensors after a character.** If `T_g = χ(g) F_g` with `χ(g) χ(h) = χ(gh)`, the
fusion tensors of `F` are fusion tensors of `T`. -/
noncomputable def smulTensor (fd : FusionData F) (hχ : ∀ g h, χ g * χ h = χ (g * h))
    (hT : ∀ g, T g = χ g • F.tensor g) : FusionData (F.withTensor T) where
  V := fd.V
  W := fd.W
  isReduction g h := by
    change MPTensor.IsReduction (mulTensor (T g) (T h)).toMPSTensor (T (g * h)).toMPSTensor
      (fd.V g h) (fd.W g h)
    simp only [hT]
    rw [mulTensor_smul_smul, hχ]
    exact (fd.isReduction g h).smul _

/-- The two fusion trees of the transported fusion tensors compare by the same scalar. -/
theorem isAssociator_smulTensor {fd : FusionData F} (hχ : ∀ g h, χ g * χ h = χ (g * h))
    (hT : ∀ g, T g = χ g • F.tensor g) {g h k : G} {z : ℂ} (hz : fd.IsAssociator g h k z) :
    (fd.smulTensor hχ hT).IsAssociator g h k z := by
  change MPTensor.IsDressedProportional (mulTensor (mulTensor (T g) (T h)) (T k)).toMPSTensor
    (fd.leftV g h k) (fd.rightV g h k) z
  simp only [hT]
  rw [mulTensor_smul_smul, mulTensor_smul_smul]
  exact hz.smul _

/-- **The anomaly is unchanged by a character**: multiplying the tensors by nonzero scalars
`χ(g)` with `χ(g) χ(h) = χ(gh)` leaves the anomaly three-cochain of the fusion tensors
unchanged.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535 (the
definition of `ω`). -/
theorem omega_smulTensor (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (hχ : ∀ g h, χ g * χ h = χ (g * h)) (hχ0 : ∀ g, χ g ≠ 0)
    (hT : ∀ g, T g = χ g • F.tensor g) :
    (fd.smulTensor hχ hT).omega = fd.omega := by
  funext g h k
  exact Units.ext (eq_omega_of_isAssociator (hF.withTensor_smul hχ hχ0 hT)
    (isAssociator_smulTensor hχ hT (isAssociator_omega hF g h k))).symm

end FusionData

end Character

end MPOTensor.GroupFamily
