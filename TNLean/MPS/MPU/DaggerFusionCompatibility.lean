/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Conjugation
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.MPU.DaggerInverseGauge
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Daggered fusion tensors and the scalars of `prop:zetas`

Let $g\mapsto\mathcal U_g$ be a representation by simple injective MPU tensors in
canonical form, with dagger-inverse gauges
$\mathcal U_g^\dagger=T_g^\dagger\mathcal U_{g^{-1}}T_g$ (`eq:defT`) and fusion
tensors $F^<_{g,h},F^>_{g,h}$ reducing $\mathcal U_g\mathcal U_h$ onto
$\mathcal U_{gh}$ (`eq:fusion_1`, `eq:fusion_2`).  The proof of Proposition
`prop:zetas` of arXiv:2502.20257 (`main.tex`, lines 1570--1678) begins as
follows: taking the dagger of the fusion equations for the pair
$(h^{-1},g^{-1})$ and using `eq:defT`, the daggered tensors
$\bigl(F^{<,>}_{h^{-1},g^{-1}}\bigr)^\dagger$, dressed by the gauges
$T_{(gh)^{-1}}$ and $T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}}$, are again
fusion tensors for $\mathcal U_g,\mathcal U_h$.  By the uniqueness of fusion
tensors (Garre-Rubio--Schuch, Theorem 1, compiling Molnár--Ge--Schuch--Cirac,
arXiv:1706.07329v2, Theorem 22) they are then related to $F^{<,>}_{g,h}$ by a
nonzero scalar $\zeta_{g,h}$, which is `eq:defzeta`.

This file proves exactly these two steps.

* The dagger of a reduction is a reduction of the physical adjoints
  (`MPSTensor.IsReduction.physicalAdjointTensor`); the dagger here is entrywise
  conjugation together with exchange of the two physical legs, as in the source
  (line 1662: "complex conjugating every entry and swapping the legs on the
  same side").
* The physical adjoint of $\mathcal U_{h^{-1}}\mathcal U_{g^{-1}}$ is
  $\mathcal U_{g^{-1}}^\dagger\mathcal U_{h^{-1}}^\dagger$ after the product-bond
  swap (`MPOTensor.physicalAdjointTensor_mulTensor`), and `eq:defT` at
  $g^{-1}$, $h^{-1}$ and $(gh)^{-1}=h^{-1}g^{-1}$ turns it into
  $\mathcal U_g\mathcal U_h$ and the target into $\mathcal U_{gh}$.  The
  resulting reduction
  (`MPOTensor.GroupFamily.FusionData.isReduction_daggerFusion`) is the
  load-bearing tensor statement of the proof.
* $\zeta_{g,h}$ (`MPOTensor.GroupFamily.FusionData.daggerZeta`) is the scalar
  comparing the daggered fusion tensors with $F^{<}_{g,h}$ against long words;
  both equations of `eq:defzeta` hold
  (`MPOTensor.GroupFamily.FusionData.daggerZeta_defzeta`), the second with
  $\zeta_{g,h}^{-1}$.

As in `MPOTensor.GroupFamily.FusionData.omega`, the comparisons are
boundary-dressed: they hold after multiplication by every sufficiently long
word of $\mathcal U_g\mathcal U_h$, and the bare rectangular matrices are not
asserted to be proportional (arXiv:1706.07329v2, Theorem 22).  The bond spaces
of $\mathcal U_x$ and $\mathcal U_{x^{-1}}$ have equal dimension
(`MPOTensor.GroupFamily.IsRepresentation.bondDim_inv`); the daggered tensors
carry the corresponding permutation matrices explicitly.

The identity `eq:zeta` of the same proposition is proved in
`TNLean.MPS.MPU.DaggerFusionScalars`.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

/-! ### Permutation matrices of bond-dimension equalities -/

namespace MPSTensor

/-- The permutation matrix of an equality `m = n` of bond dimensions, from the
coordinates `Fin m` to `Fin n`. -/
noncomputable def reindexBondMatrix {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) ℂ :=
  (finCongr h.symm).toPEquiv.toMatrix

/-- The permutation matrix of a reflexive equality is the identity. -/
@[simp] theorem reindexBondMatrix_rfl (m : ℕ) : reindexBondMatrix (rfl : m = m) = 1 := by
  simp [reindexBondMatrix]

variable {d : ℕ}

/-- A bond-dimension identification composed with a unitary gauge intertwines a
tensor with its gauge transform: if `Y i = T† (reindex h A) i T`, then
`A i C = C Y i` for `C = E T`, where `E` is the permutation matrix of `h`. -/
theorem mul_reindexBondMatrix_mul_gauge {m n : ℕ} (h : m = n) (A : MPSTensor d m)
    (T : Matrix.unitaryGroup (Fin n) ℂ) (Y : MPSTensor d n)
    (hY : ∀ i, Y i = (T : Matrix (Fin n) (Fin n) ℂ)ᴴ * reindex h A i * T) (i) :
    A i * (reindexBondMatrix h.symm * (T : Matrix (Fin n) (Fin n) ℂ)) =
      (reindexBondMatrix h.symm * (T : Matrix (Fin n) (Fin n) ℂ)) * Y i := by
  subst h
  have hT : (T : Matrix (Fin m) (Fin m) ℂ) * (T : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
    T.property.2
  simp only [reindexBondMatrix_rfl, Matrix.one_mul, reindex_rfl, hY]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT, Matrix.one_mul]

/-- The permutation matrices of an equality of bond dimensions and of its
reverse are mutually inverse. -/
theorem reindexBondMatrix_mul_symm {m n : ℕ} (h : m = n) :
    reindexBondMatrix h * reindexBondMatrix h.symm = 1 := by
  subst h
  simp

/-- The gauge transform `E T` of a bond identification has the left and right
inverse `T† E⁻¹`. -/
theorem reindexBondMatrix_gauge_mul_inv {m n : ℕ} (h : m = n)
    (T : Matrix.unitaryGroup (Fin n) ℂ) :
    (reindexBondMatrix h.symm * (T : Matrix (Fin n) (Fin n) ℂ)) *
        ((T : Matrix (Fin n) (Fin n) ℂ)ᴴ * reindexBondMatrix h) = 1 := by
  have hT : (T : Matrix (Fin n) (Fin n) ℂ) * (T : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    T.property.2
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T : Matrix (Fin n) (Fin n) ℂ), hT, Matrix.one_mul,
    reindexBondMatrix_mul_symm]

/-- The gauge transform `T† E⁻¹` has the left inverse `E T`. -/
theorem reindexBondMatrix_gauge_inv_mul {m n : ℕ} (h : m = n)
    (T : Matrix.unitaryGroup (Fin n) ℂ) :
    ((T : Matrix (Fin n) (Fin n) ℂ)ᴴ * reindexBondMatrix h) *
        (reindexBondMatrix h.symm * (T : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
  have hT : (T : Matrix (Fin n) (Fin n) ℂ)ᴴ * (T : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    T.property.1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (reindexBondMatrix h),
    reindexBondMatrix_mul_symm, Matrix.one_mul, hT]

end MPSTensor

/-! ### Transport of reductions -/

namespace MPSTensor.IsReduction

variable {d D₁ D₁' D₂ : ℕ} {B : MPSTensor d D₂} {A : MPSTensor d D₁}
  {V : Matrix (Fin D₁) (Fin D₂) ℂ} {W : Matrix (Fin D₂) (Fin D₁) ℂ}

/-- A reduction transports along an intertwiner of the target letters with a
right inverse: if `A' i Q = Q A i` and `Q R = 1`, then `(Q V, W R)` reduces `B`
onto `A'`.  This is the target counterpart of
`MPSTensor.IsReduction.of_intertwine`, used to apply the gauge equation
`eq:defT` of arXiv:2502.20257 (lines 1552--1557) to the target of a fusion
tensor. -/
theorem of_target_intertwine {A' : MPSTensor d D₁'} {Q : Matrix (Fin D₁') (Fin D₁) ℂ}
    {R : Matrix (Fin D₁) (Fin D₁') ℂ} (hQR : Q * R = 1)
    (hA : ∀ i, A' i * Q = Q * A i) (h : IsReduction B A V W) :
    IsReduction B A' (Q * V) (W * R) := by
  have hw : ∀ w, Kraus.evalWord A' w = Q * Kraus.evalWord A w * R := fun w ↦ by
    rw [← Kraus.evalWord_intertwine _ _ _ hA w, Matrix.mul_assoc, hQR, Matrix.mul_one]
  refine ⟨?_, fun w ↦ ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, h.mul_eq_one, Matrix.one_mul, hQR]
  · rw [hw, ← h.evalWord w]
    simp only [Matrix.mul_assoc]

/-- Entrywise complex conjugation of both tensors and both matrices preserves a
reduction. -/
theorem mapStar (h : IsReduction B A V W) :
    IsReduction (MPSTensor.mapStar B) (MPSTensor.mapStar A)
      (V.map (starRingEnd ℂ)) (W.map (starRingEnd ℂ)) := by
  refine ⟨?_, fun w ↦ ?_⟩
  · rw [← Matrix.map_mul, h.mul_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [MPSTensor.evalWord_mapStar, MPSTensor.evalWord_mapStar, ← Matrix.map_mul,
      ← Matrix.map_mul, h.evalWord]

/-- A reduction from a tensor with relabelled bond coordinates is a reduction
from the original tensor, with the permutation matrices absorbed into the two
boundaries. -/
theorem of_reindexBond_source {D₂' : ℕ} {K : MPOTensor d D₂} {A : MPSTensor (d * d) D₁}
    {V : Matrix (Fin D₁) (Fin D₂') ℂ} {W : Matrix (Fin D₂') (Fin D₁) ℂ}
    (e : Fin D₂' ≃ Fin D₂) (h : IsReduction (MPOTensor.reindexBond e K).toMPSTensor A V W) :
    IsReduction K.toMPSTensor A (V * e.toPEquiv.toMatrix) (e.symm.toPEquiv.toMatrix * W) := by
  refine h.of_intertwine ?_ (fun i ↦ ?_)
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext x y
    simp [MPOTensor.toMPSTensor, MPOTensor.reindexBond]

end MPSTensor.IsReduction

namespace MPOTensor

variable {d : ℕ}

/-- The doubled-index tensor of the physical adjoint is the entrywise conjugate
of the original doubled-index tensor, with the two physical coordinates
exchanged. -/
theorem toMPSTensor_physicalAdjointTensor {D : ℕ} (U : MPOTensor d D) :
    (physicalAdjointTensor U).toMPSTensor =
      Kraus.reindexPhysical (physicalPairSwapEquiv d) (MPSTensor.mapStar U.toMPSTensor) := by
  ext ij β α
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [Kraus.reindexPhysical, MPSTensor.mapStar, MPOTensor.toMPSTensor, Matrix.map_apply]

end MPOTensor

namespace MPSTensor.IsReduction

/-- **The dagger of a reduction.** If `(V, W)` reduces the doubled-index tensor
of `K` onto that of `M`, then the entrywise conjugates `(V.map star, W.map star)` reduce the
physical adjoint of `K` onto that of `M`.

This is the step "taking the dagger of `eq:fusion_1`--`eq:fusion_2`" in the
proof of `prop:zetas`, arXiv:2502.20257, lines 1662--1677; the dagger of a
three-legged tensor conjugates every entry and exchanges the physical legs on
the same side. -/
theorem physicalAdjointTensor {d D₁ D₂ : ℕ} {K : MPOTensor d D₂} {M : MPOTensor d D₁}
    {V : Matrix (Fin D₁) (Fin D₂) ℂ} {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : IsReduction K.toMPSTensor M.toMPSTensor V W) :
    IsReduction (MPOTensor.physicalAdjointTensor K).toMPSTensor
      (MPOTensor.physicalAdjointTensor M).toMPSTensor
      (V.map (starRingEnd ℂ)) (W.map (starRingEnd ℂ)) := by
  rw [MPOTensor.toMPSTensor_physicalAdjointTensor, MPOTensor.toMPSTensor_physicalAdjointTensor]
  exact h.mapStar.reindexPhysical _

end MPSTensor.IsReduction

namespace MPOTensor.GroupFamily

variable {d : ℕ}

/-- Bond reindexings of the tensors of two equal group elements agree. -/
theorem reindex_toMPSTensor_congr {G : Type*} (F : GroupFamily G d) {x y : G} (hxy : x = y)
    {n : ℕ} (h₁ : F.bondDim x = n) (h₂ : F.bondDim y = n) :
    MPSTensor.reindex h₁ (F.tensor x).toMPSTensor =
      MPSTensor.reindex h₂ (F.tensor y).toMPSTensor := by
  subst hxy
  rfl

variable {G : Type} [Group G] {F : GroupFamily G d}

namespace IsRepresentation

variable (hF : F.IsRepresentation)
  (hc : ∀ g : G, MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)

/-- The bond dimension of the tensor of `g h` equals that of `h⁻¹ g⁻¹ = (g h)⁻¹`. -/
theorem bondDim_mul_inv_rev (hF : F.IsRepresentation) (g h : G) :
    F.bondDim (g * h) = F.bondDim (h⁻¹ * g⁻¹) :=
  (hF.bondDim_inv F (g * h)).trans (congrArg F.bondDim (mul_inv_rev g h))

/-- The leg gauge $T^\dagger_{x^{-1}}$ of a daggered fusion tensor, from the bond
space of $\mathcal U_x$ to that of $\mathcal U_{x^{-1}}$, including the
identification of the two bond dimensions.

Source: arXiv:2502.20257, `eq:defzeta`, lines 1570--1637. -/
noncomputable def daggerLegGauge (x : G) :
    Matrix (Fin (F.bondDim x⁻¹)) (Fin (F.bondDim x)) ℂ :=
  (hF.daggerInverseGauge F hc x⁻¹ : Matrix (Fin (F.bondDim x⁻¹)) (Fin (F.bondDim x⁻¹)) ℂ)ᴴ *
    MPSTensor.reindexBondMatrix (hF.bondDim_inv F x)

/-- The inverse $T_{x^{-1}}$ of the leg gauge of a daggered fusion tensor.

Source: arXiv:2502.20257, `eq:defzeta`, lines 1570--1637. -/
noncomputable def daggerLegGaugeInv (x : G) :
    Matrix (Fin (F.bondDim x)) (Fin (F.bondDim x⁻¹)) ℂ :=
  MPSTensor.reindexBondMatrix (hF.bondDim_inv F x).symm *
    (hF.daggerInverseGauge F hc x⁻¹ : Matrix (Fin (F.bondDim x⁻¹)) (Fin (F.bondDim x⁻¹)) ℂ)

/-- The leg gauge and its inverse compose to the identity on the bond space of
$\mathcal U_{x^{-1}}$. -/
theorem daggerLegGauge_mul_inv (x : G) :
    hF.daggerLegGauge hc x * hF.daggerLegGaugeInv hc x = 1 :=
  MPSTensor.reindexBondMatrix_gauge_inv_mul _ _

/-- `eq:defT` at $x^{-1}$: the leg gauge intertwines $\mathcal U_x$ with the
physical adjoint of $\mathcal U_{x^{-1}}$,
$\mathcal U_x\,T_{x^{-1}}=T_{x^{-1}}\,\mathcal U_{x^{-1}}^\dagger$, since
$(x^{-1})^{-1}=x$.

Source: arXiv:2502.20257, `eq:defT`, lines 1552--1557. -/
theorem tensor_mul_daggerLegGaugeInv (x : G) (i j : Fin d) :
    F.tensor x i j * hF.daggerLegGaugeInv hc x =
      hF.daggerLegGaugeInv hc x * physicalAdjointTensor (F.tensor x⁻¹) i j := by
  have hinv : inverseFlattening F hF x⁻¹ =
      MPSTensor.reindex (hF.bondDim_inv F x) (F.tensor x).toMPSTensor :=
    reindex_toMPSTensor_congr F (inv_inv x) _ _
  have h := MPSTensor.mul_reindexBondMatrix_mul_gauge (hF.bondDim_inv F x) (F.tensor x).toMPSTensor
    (hF.daggerInverseGauge F hc x⁻¹) (physicalAdjointTensor (F.tensor x⁻¹)).toMPSTensor
    (fun ij ↦ by rw [← hinv]; exact hF.physicalAdjointTensor_eq_daggerInverseGauge F hc x⁻¹ ij)
    (finProdFinEquiv (i, j))
  simpa only [daggerLegGaugeInv, toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] using h

/-- The target gauge $T_{(gh)^{-1}}$ of a daggered fusion tensor, from the bond
space of $\mathcal U_{h^{-1}g^{-1}}$ to that of $\mathcal U_{gh}$, including the
identification of the bond dimensions.

Source: arXiv:2502.20257, `eq:defzeta`, lines 1570--1637. -/
noncomputable def daggerTargetGauge (g h : G) :
    Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim (h⁻¹ * g⁻¹))) ℂ :=
  MPSTensor.reindexBondMatrix (hF.bondDim_mul_inv_rev g h).symm *
    (hF.daggerInverseGauge F hc (h⁻¹ * g⁻¹) :
      Matrix (Fin (F.bondDim (h⁻¹ * g⁻¹))) (Fin (F.bondDim (h⁻¹ * g⁻¹))) ℂ)

/-- The inverse $T^\dagger_{(gh)^{-1}}$ of the target gauge.

Source: arXiv:2502.20257, `eq:defzeta`, lines 1570--1637. -/
noncomputable def daggerTargetGaugeInv (g h : G) :
    Matrix (Fin (F.bondDim (h⁻¹ * g⁻¹))) (Fin (F.bondDim (g * h))) ℂ :=
  (hF.daggerInverseGauge F hc (h⁻¹ * g⁻¹) :
      Matrix (Fin (F.bondDim (h⁻¹ * g⁻¹))) (Fin (F.bondDim (h⁻¹ * g⁻¹))) ℂ)ᴴ *
    MPSTensor.reindexBondMatrix (hF.bondDim_mul_inv_rev g h)

/-- `eq:defT` at $(gh)^{-1}=h^{-1}g^{-1}$: the target gauge intertwines
$\mathcal U_{gh}$ with the physical adjoint of $\mathcal U_{h^{-1}g^{-1}}$.

Source: arXiv:2502.20257, `eq:defT`, lines 1552--1557. -/
theorem toMPSTensor_mul_daggerTargetGauge (g h : G) (i : Fin (d * d)) :
    (F.tensor (g * h)).toMPSTensor i * hF.daggerTargetGauge hc g h =
      hF.daggerTargetGauge hc g h *
        (physicalAdjointTensor (F.tensor (h⁻¹ * g⁻¹))).toMPSTensor i := by
  have hinv : inverseFlattening F hF (h⁻¹ * g⁻¹) =
      MPSTensor.reindex (hF.bondDim_mul_inv_rev g h) (F.tensor (g * h)).toMPSTensor :=
    reindex_toMPSTensor_congr F (by rw [mul_inv_rev, inv_inv, inv_inv]) _ _
  exact MPSTensor.mul_reindexBondMatrix_mul_gauge (hF.bondDim_mul_inv_rev g h)
    (F.tensor (g * h)).toMPSTensor (hF.daggerInverseGauge F hc (h⁻¹ * g⁻¹)) _
    (fun ij ↦ by rw [← hinv]; exact hF.physicalAdjointTensor_eq_daggerInverseGauge F hc _ ij) i

/-- The target gauge and its inverse compose to the identity on the bond space
of $\mathcal U_{gh}$. -/
theorem daggerTargetGauge_mul_inv (g h : G) :
    hF.daggerTargetGauge hc g h * hF.daggerTargetGaugeInv hc g h = 1 :=
  MPSTensor.reindexBondMatrix_gauge_mul_inv _ _

end IsRepresentation

namespace FusionData

variable (fd : FusionData F) (hF : F.IsRepresentation)
  (hc : ∀ g : G, MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)

/-- **The daggered left fusion tensor**
$T_{(gh)^{-1}}\bigl(F^<_{h^{-1},g^{-1}}\bigr)^\dagger
(T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}})$, the left-hand side of the first
equation of `eq:defzeta`.  The dagger conjugates every entry and exchanges the
two legs on the same side (`productBondSwapEquiv`).

Source: arXiv:2502.20257, `eq:defzeta` and the display following it,
lines 1570--1662. -/
noncomputable def daggerFusionV (g h : G) :
    Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ :=
  hF.daggerTargetGauge hc g h * (fd.V h⁻¹ g⁻¹).map (starRingEnd ℂ) *
      ((productBondSwapEquiv (F.bondDim h⁻¹) (F.bondDim g⁻¹)).toPEquiv.toMatrix :
        Matrix _ _ ℂ) *
    idKron (F.bondDim g⁻¹) (hF.daggerLegGauge hc h) *
    kronId (hF.daggerLegGauge hc g) (F.bondDim h)

/-- **The daggered right fusion tensor**
$(T_{g^{-1}}\otimes T_{h^{-1}})\bigl(F^>_{h^{-1},g^{-1}}\bigr)^\dagger
T^\dagger_{(gh)^{-1}}$, the left-hand side of the second equation of
`eq:defzeta`.

Source: arXiv:2502.20257, `eq:defzeta` and the display following it,
lines 1570--1662. -/
noncomputable def daggerFusionW (g h : G) :
    Matrix (Fin (F.bondDim g * F.bondDim h)) (Fin (F.bondDim (g * h))) ℂ :=
  kronId (hF.daggerLegGaugeInv hc g) (F.bondDim h) *
    (idKron (F.bondDim g⁻¹) (hF.daggerLegGaugeInv hc h) *
      (((productBondSwapEquiv (F.bondDim h⁻¹) (F.bondDim g⁻¹)).symm.toPEquiv.toMatrix :
        Matrix _ _ ℂ) *
        ((fd.W h⁻¹ g⁻¹).map (starRingEnd ℂ) * hF.daggerTargetGaugeInv hc g h)))

/-- **The daggered fusion tensors are fusion tensors.** The daggered tensors of
the pair $(h^{-1},g^{-1})$, dressed by the dagger-inverse gauges, reduce
$\mathcal U_g\mathcal U_h$ onto $\mathcal U_{gh}$.

This is the load-bearing tensor step of the proof of `prop:zetas`: "From taking
the dagger of `eq:fusion_1`--`eq:fusion_2`, and using `eq:defT` it follows that
$(F^{<,>}_{h^{-1},g^{-1}})^\dagger$, up to multiplication by the corresponding
$T_g$, is a valid fusion tensor for $\mathcal U_g,\mathcal U_h$"
(arXiv:2502.20257, lines 1675--1677).  The proof is the dagger of a reduction,
the product reversal under the physical adjoint, and `eq:defT` at $g^{-1}$,
$h^{-1}$ and $(gh)^{-1}$. -/
theorem isReduction_daggerFusion (g h : G) :
    MPSTensor.IsReduction (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (F.tensor (g * h)).toMPSTensor (fd.daggerFusionV hF hc g h) (fd.daggerFusionW hF hc g h) := by
  have h₀ := (fd.isReduction h⁻¹ g⁻¹).physicalAdjointTensor
  rw [physicalAdjointTensor_mulTensor] at h₀
  have h₁ := (h₀.of_target_intertwine (hF.daggerTargetGauge_mul_inv hc g h)
    (hF.toMPSTensor_mul_daggerTargetGauge hc g h)).of_reindexBond_source _
  have h₂ := h₁.of_intertwine (B' := (mulTensor (physicalAdjointTensor (F.tensor g⁻¹))
      (F.tensor h)).toMPSTensor)
    (by rw [idKron_mul, hF.daggerLegGauge_mul_inv, idKron_one])
    (fun i ↦ mulTensor_mul_idKron_of_intertwine _
      (hF.tensor_mul_daggerLegGaugeInv hc h) i.divNat i.modNat)
  have h₃ := h₂.of_intertwine (B' := (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor)
    (by rw [kronId_mul, hF.daggerLegGauge_mul_inv, kronId_one])
    (fun i ↦ mulTensor_mul_kronId_of_intertwine _
      (hF.tensor_mul_daggerLegGaugeInv hc g) i.divNat i.modNat)
  exact h₃

/-- **The scalars $\zeta_{g,h}$ of `prop:zetas`**: $\zeta_{g,h}$ is the nonzero
scalar comparing the daggered left fusion tensor with $F^<_{g,h}$ against long
words of $\mathcal U_g\mathcal U_h$
(`MPOTensor.GroupFamily.FusionData.daggerZeta_defzeta`), chosen by
`MPSTensor.dressedScalar`.

Source: arXiv:2502.20257, Proposition `prop:zetas`, `eq:defzeta`,
lines 1570--1637. -/
noncomputable def daggerZeta : ScalarCocycle G := fun p ↦
  MPSTensor.dressedScalar (mulTensor (F.tensor p.1) (F.tensor p.2)).toMPSTensor
    (fd.daggerFusionV hF hc p.1 p.2) (fd.V p.1 p.2)

/-- **`eq:defzeta`.** The daggered fusion tensors are related to the chosen
fusion tensors by $\zeta_{g,h}$ and $\zeta_{g,h}^{-1}$, against all sufficiently
long words $w$ of $B=\mathcal U_g\mathcal U_h$:
$$
  T_{(gh)^{-1}}\bigl(F^<_{h^{-1},g^{-1}}\bigr)^\dagger
    (T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}})\,B^w
    =\zeta_{g,h}\,F^<_{g,h}B^w,\qquad
  B^w(T_{g^{-1}}\otimes T_{h^{-1}})\bigl(F^>_{h^{-1},g^{-1}}\bigr)^\dagger
    T^\dagger_{(gh)^{-1}}=\zeta_{g,h}^{-1}\,B^wF^>_{g,h}.
$$

Source: arXiv:2502.20257, Proposition `prop:zetas`, `eq:defzeta`
(lines 1570--1637), with the proof at lines 1675--1677 through the
boundary-dressed uniqueness of reductions (arXiv:1706.07329v2, Theorem 22). -/
theorem daggerZeta_defzeta (g h : G) :
    MPSTensor.IsDressedProportional (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
        (fd.daggerFusionV hF hc g h) (fd.V g h) (fd.daggerZeta hF hc (g, h)) ∧
      ∃ N : ℕ, ∀ w : List (Fin (d * d)), N ≤ w.length →
        Kraus.evalWord (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor w *
            fd.daggerFusionW hF hc g h =
          ((fd.daggerZeta hF hc (g, h) : ℂ))⁻¹ •
            (Kraus.evalWord (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor w * fd.W g h) := by
  have hN := hF.isNormalRepresentation
  have hD := fd.isReduction_daggerFusion hF hc g h
  obtain ⟨z, hz, hw⟩ := hD.exists_boundary_dressed_proportional_of_nilpotencyLength_le
    (fd.isReduction g h) (hN.isNormal _) (hN.sameMPV₂Pos_mulTensor g h)
    (le_max_left _ _) (le_max_right _ _)
  have hleft : MPSTensor.IsDressedProportional
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (fd.daggerFusionV hF hc g h) (fd.V g h) z :=
    ⟨_, fun w hlen ↦ (hw w (Nat.lt_of_succ_le hlen)).1⟩
  have hζ : MPSTensor.IsDressedProportional
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (fd.daggerFusionV hF hc g h) (fd.V g h) (fd.daggerZeta hF hc (g, h)) :=
    MPSTensor.isDressedProportional_dressedScalar ⟨z, hz, hleft⟩
  have hzζ : z = fd.daggerZeta hF hc (g, h) :=
    hleft.eq_of_forall_exists_ne_zero hζ
      (hD.exists_mul_evalWord_ne_zero (hN.isNormal _) (F.bondDim_pos _))
  refine ⟨hζ, 2 * max
    (MPSTensor.reductionResidualNilpotencyLength
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor (F.tensor (g * h)).toMPSTensor
      (fd.daggerFusionV hF hc g h) (fd.daggerFusionW hF hc g h))
    (MPSTensor.reductionResidualNilpotencyLength
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor (F.tensor (g * h)).toMPSTensor
      (fd.V g h) (fd.W g h)) + 1, fun w hlen ↦ ?_⟩
  rw [← hzζ]
  exact (hw w (Nat.lt_of_succ_le hlen)).2

end FusionData

end MPOTensor.GroupFamily
