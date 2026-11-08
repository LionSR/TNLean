/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.DaggerFusionCompatibility

/-!
# The scalars of `prop:zetas` under a double dagger

Let $g\mapsto\mathcal U_g$ be a representation by simple injective MPU tensors
in canonical form, with dagger-inverse gauges $T_g$ and signs $\sigma_g$
(`eq:defT`, `eq:intro_sigma`), and a choice of fusion tensors $F^<_{g,h}$.
The daggered fusion tensor
$$
  \widetilde F^<_{g,h}=T_{(gh)^{-1}}\bigl(F^<_{h^{-1},g^{-1}}\bigr)^\dagger
    (T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}})
$$
is $\zeta_{g,h}F^<_{g,h}$ against long words (`eq:defzeta`).  The proof of
Proposition `prop:zetas` of arXiv:2502.20257 (`main.tex`, lines 1570--1678)
obtains `eq:zeta`,
$$
  \zeta_{g,h}\,\overline{\zeta_{h^{-1},g^{-1}}}=\frac{\sigma_g\sigma_h}{\sigma_{gh}},
$$
"by applying this duality twice, together with `eq:intro_sigma`"
(lines 1675--1677).  This file carries out that argument.

* The dagger operation $X\mapsto T_{(gh)^{-1}}\overline X\,
  \mathrm{swap}\,(T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}})$ on left
  boundaries of $\mathcal U_{h^{-1}}\mathcal U_{g^{-1}}$
  (`MPOTensor.GroupFamily.IsRepresentation.daggerBoundary`) transports a
  dressed proportionality with scalar $z$ to one of $\mathcal U_g\mathcal U_h$
  with scalar $\overline z$
  (`MPOTensor.GroupFamily.IsRepresentation.isDressedProportional_daggerBoundary`).
* Applying the dagger twice to $F^<_{g,h}$ returns
  $\sigma_{h^{-1}g^{-1}}\overline{\sigma_{g^{-1}}}\,\overline{\sigma_{h^{-1}}}\,
  F^<_{g,h}$ exactly
  (`MPOTensor.GroupFamily.FusionData.daggerBoundary_daggerFusionV`); this is
  `eq:intro_sigma` at $g^{-1}$, $h^{-1}$ and $h^{-1}g^{-1}$.
* Comparing the two computations on a nonvanishing long word gives `eq:zeta`
  (`MPOTensor.GroupFamily.FusionData.daggerZeta_mul_star_daggerZeta_inv`).

The daggered fusion tensors themselves form a choice of fusion tensors
(`MPOTensor.GroupFamily.FusionData.dagger`), and $\zeta$ is the scalar
comparing that choice with the original one
(`MPOTensor.GroupFamily.FusionData.daggerZeta_eq_relativeScalar`).  Hence the
anomaly three-cocycle changes by the coboundary of $\zeta$ when the fusion
tensors are daggered
(`MPOTensor.GroupFamily.FusionData.omega_eq_fusionGauge_daggerZeta`).  The
remaining step of `eq:inv_omega`, identifying the three-cocycle of the daggered
fusion tensors at $(g,h,k)$ with $\overline{\omega(k^{-1},h^{-1},g^{-1})}^{\,-1}$ by
taking the dagger of the two fusion trees, is not proved here.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

/-! ### Permutation matrices of bond identifications -/

namespace MPSTensor

/-- Permutation matrices of bond identifications compose. -/
theorem reindexBondMatrix_mul_reindexBondMatrix {m n k : ℕ} (h₁ : n = k) (h₂ : m = n) :
    reindexBondMatrix h₁ * reindexBondMatrix h₂ = reindexBondMatrix (h₂.trans h₁) := by
  subst h₁ h₂
  simp

/-- Permutation matrices of bond identifications compose, against a trailing factor. -/
theorem reindexBondMatrix_mul_reindexBondMatrix_assoc {m n k p : ℕ} (h₁ : n = k) (h₂ : m = n)
    (X : Matrix (Fin m) (Fin p) ℂ) :
    reindexBondMatrix h₁ * (reindexBondMatrix h₂ * X) = reindexBondMatrix (h₂.trans h₁) * X := by
  rw [← Matrix.mul_assoc, reindexBondMatrix_mul_reindexBondMatrix]

/-- The permutation matrix of a self-identification is the identity. -/
@[simp] theorem reindexBondMatrix_self {m : ℕ} (h : m = m) : reindexBondMatrix h = 1 :=
  reindexBondMatrix_rfl m

/-- A permutation matrix is real. -/
@[simp] theorem reindexBondMatrix_map_star {m n : ℕ} (h : m = n) :
    (reindexBondMatrix h).map (starRingEnd ℂ) = reindexBondMatrix h := by
  subst h
  simp

/-- The adjoint of a permutation matrix is the permutation matrix of the reverse
identification. -/
theorem reindexBondMatrix_conjTranspose {m n : ℕ} (h : m = n) :
    (reindexBondMatrix h)ᴴ = reindexBondMatrix h.symm := by
  subst h
  simp

/-- Reindexing a square matrix along a bond identification is conjugation by the
corresponding permutation matrices. -/
theorem reindex_finCongr_eq {m n : ℕ} (h : m = n) (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.reindex (finCongr h) (finCongr h) M =
      reindexBondMatrix h * M * reindexBondMatrix h.symm := by
  subst h
  simp

end MPSTensor

/-! ### Dressed proportionality under the dagger -/

namespace MPSTensor.IsDressedProportional

variable {d D m : ℕ} {B : MPSTensor d D} {X Y : Matrix (Fin m) (Fin D) ℂ} {z : ℂ}

/-- Entrywise complex conjugation of the tensor and both boundaries conjugates
the scalar of a dressed proportionality. -/
theorem mapStar (h : IsDressedProportional B X Y z) :
    IsDressedProportional (MPSTensor.mapStar B) (X.map (starRingEnd ℂ))
      (Y.map (starRingEnd ℂ)) (starRingEnd ℂ z) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [MPSTensor.evalWord_mapStar, ← Matrix.map_mul, h w hw]
  conv_rhs => rw [← Matrix.map_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

/-- Relabelling the physical alphabet preserves a dressed proportionality. -/
theorem reindexPhysical {d' : ℕ} (h : IsDressedProportional B X Y z) (f : Fin d' → Fin d) :
    IsDressedProportional (Kraus.reindexPhysical f B) X Y z := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun w hw ↦ by
    simp only [Kraus.evalWord_reindexPhysical]
    exact h _ (by simpa using hw)⟩

/-- **The dagger of a dressed proportionality.** If $X K^w=zYK^w$ for long words
of the doubled-index tensor of $K$, then
$\overline X(K^\dagger)^w=\overline z\,\overline Y(K^\dagger)^w$ for long words of
the physical adjoint.  This is the dagger step of the proof of `prop:zetas`,
arXiv:2502.20257, lines 1662--1677, applied to a boundary-dressed comparison. -/
theorem physicalAdjointTensor {d D₁ m : ℕ} {K : MPOTensor d D₁}
    {X Y : Matrix (Fin m) (Fin D₁) ℂ} {z : ℂ}
    (h : IsDressedProportional K.toMPSTensor X Y z) :
    IsDressedProportional (MPOTensor.physicalAdjointTensor K).toMPSTensor
      (X.map (starRingEnd ℂ)) (Y.map (starRingEnd ℂ)) (starRingEnd ℂ z) := by
  rw [MPOTensor.toMPSTensor_physicalAdjointTensor]
  exact h.mapStar.reindexPhysical _

/-- A dressed proportionality for a tensor with relabelled bond coordinates is
one for the original tensor, with the permutation matrix absorbed into the
boundaries. -/
theorem of_reindexBond_source {d D₂ D₂' m : ℕ} {K : MPOTensor d D₂}
    {X Y : Matrix (Fin m) (Fin D₂') ℂ} {z : ℂ} (e : Fin D₂' ≃ Fin D₂)
    (h : IsDressedProportional (MPOTensor.reindexBond e K).toMPSTensor X Y z) :
    IsDressedProportional K.toMPSTensor (X * (e.toPEquiv.toMatrix : Matrix (Fin D₂') (Fin D₂) ℂ))
      (Y * (e.toPEquiv.toMatrix : Matrix (Fin D₂') (Fin D₂) ℂ)) z := by
  refine h.of_intertwine (P := e.symm.toPEquiv.toMatrix) ?_ ?_ (fun i ↦ ?_)
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext x y
    simp [MPOTensor.toMPSTensor, MPOTensor.reindexBond]

end MPSTensor.IsDressedProportional

/-! ### Entrywise conjugation of Kronecker boundaries -/

namespace MPOTensor

/-- Entrywise conjugation commutes with `X ⊗ 1`. -/
theorem kronId_map_star {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    (kronId X D).map (starRingEnd ℂ) = kronId (X.map (starRingEnd ℂ)) D := by
  ext x y
  simp only [kronId, Matrix.map_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, map_mul]
  split_ifs <;> simp

/-- Entrywise conjugation commutes with `1 ⊗ X`. -/
theorem idKron_map_star {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    (idKron D X).map (starRingEnd ℂ) = idKron D (X.map (starRingEnd ℂ)) := by
  ext x y
  simp only [idKron, Matrix.map_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, map_mul]
  split_ifs <;> simp

/-- A permutation matrix is real. -/
theorem equiv_toMatrix_map_star {m n : Type*} [DecidableEq n] (e : m ≃ n) :
    (e.toPEquiv.toMatrix : Matrix m n ℂ).map (starRingEnd ℂ) = e.toPEquiv.toMatrix := by
  ext x y
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

/-- `X ⊗ 1` is linear in `X`. -/
theorem kronId_smul {m n : ℕ} (c : ℂ) (X : Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    kronId (c • X) D = c • kronId X D := by
  ext x y
  simp [kronId, Matrix.smul_kronecker]

/-- `1 ⊗ X` is linear in `X`. -/
theorem idKron_smul {m n : ℕ} (c : ℂ) (D : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    idKron D (c • X) = c • idKron D X := by
  ext x y
  simp [idKron, Matrix.kronecker_smul]

/-- Conjugating `1 ⊗ X` and `Y ⊗ 1` by the product-bond swaps exchanges the two
Kronecker factors. -/
theorem productBondSwap_mul_idKron_mul_kronId_mul_productBondSwap {a a' b b' : ℕ}
    (X : Matrix (Fin a) (Fin a') ℂ) (Y : Matrix (Fin b) (Fin b') ℂ) :
    ((productBondSwapEquiv a b).toPEquiv.toMatrix : Matrix _ _ ℂ) * idKron b X *
        kronId Y a' * ((productBondSwapEquiv b' a').toPEquiv.toMatrix : Matrix _ _ ℂ) =
      kronId X b * idKron a' Y := by
  rw [Matrix.mul_assoc _ (idKron b X), ← kronId_mul_idKron, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, kronId, kronId, idKron, idKron,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  ext x y
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp [productBondSwapEquiv, Matrix.kroneckerMap_apply, mul_comm]

end MPOTensor

namespace MPOTensor

/-- `productBondSwap_mul_idKron_mul_kronId_mul_productBondSwap` against a trailing
factor. -/
theorem productBondSwap_mul_idKron_mul_kronId_mul_productBondSwap_assoc {a a' b b' p : ℕ}
    (X : Matrix (Fin a) (Fin a') ℂ) (Y : Matrix (Fin b) (Fin b') ℂ)
    (Z : Matrix (Fin (a' * b')) (Fin p) ℂ) :
    ((productBondSwapEquiv a b).toPEquiv.toMatrix : Matrix _ _ ℂ) * (idKron b X *
        (kronId Y a' * (((productBondSwapEquiv b' a').toPEquiv.toMatrix : Matrix _ _ ℂ) * Z))) =
      kronId X b * (idKron a' Y * Z) := by
  simp only [← Matrix.mul_assoc]
  rw [productBondSwap_mul_idKron_mul_kronId_mul_productBondSwap]

end MPOTensor

namespace MPOTensor.GroupFamily

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d}

omit [Group G] in
/-- The bond identification of two equal group elements is a permutation matrix of
bond dimensions. -/
theorem castMat_eq_reindexBondMatrix {a b : G} (e : a = b) :
    F.castMat e = MPSTensor.reindexBondMatrix (congrArg F.bondDim e) :=
  rfl

namespace IsRepresentation

variable (hF : F.IsRepresentation)
  (hc : ∀ g : G, MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)

/-- The dagger-inverse gauges of two equal group elements agree after the bond
identification. -/
theorem daggerInverseGauge_congr {y y' : G} (e : y = y') :
    (hF.daggerInverseGauge F hc y' : Matrix (Fin (F.bondDim y')) (Fin (F.bondDim y')) ℂ) =
      F.castMat e *
        (hF.daggerInverseGauge F hc y : Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ) *
          F.castMat e.symm := by
  subst e
  simp

/-- The leg gauge $T^\dagger_{x^{-1}}$ has the left inverse $T_{x^{-1}}$. -/
theorem daggerLegGaugeInv_mul (x : G) :
    hF.daggerLegGaugeInv hc x * hF.daggerLegGauge hc x = 1 :=
  MPSTensor.reindexBondMatrix_gauge_mul_inv _ _

/-- **`eq:intro_sigma` in transposed form**:
$T_{y^{-1}}^{\mathsf T}\,T_y^\dagger=\overline{\sigma_y}\,\Id$, with the bond spaces of
$y$ and $y^{-1}$ identified.

Source: arXiv:2502.20257, `eq:intro_sigma`, lines 1557--1562. -/
theorem transpose_daggerInverseGauge_inv_mul_conjTranspose (y : G) :
    (hF.daggerInverseGauge F hc y⁻¹ :
      Matrix (Fin (F.bondDim y⁻¹)) (Fin (F.bondDim y⁻¹)) ℂ)ᵀ *
        (MPSTensor.reindexBondMatrix (hF.bondDim_inv F y) *
          (hF.daggerInverseGauge F hc y : Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ)ᴴ) =
      starRingEnd ℂ (hF.daggerInverseScalar F hc y) •
        MPSTensor.reindexBondMatrix (hF.bondDim_inv F y) := by
  set T : Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ :=
    ↑(hF.daggerInverseGauge F hc y)
  set T' : Matrix (Fin (F.bondDim y⁻¹)) (Fin (F.bondDim y⁻¹)) ℂ :=
    ↑(hF.daggerInverseGauge F hc y⁻¹)
  set R := MPSTensor.reindexBondMatrix (hF.bondDim_inv F y)
  set R' := MPSTensor.reindexBondMatrix (hF.bondDim_inv F y).symm
  have hσ := hF.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one F hc y
  have hI : (hF.inverseDaggerInverseGauge F hc y :
      Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ) = R' * T' * R :=
    MPSTensor.reindex_finCongr_eq _ _
  rw [hI, Matrix.map_mul, Matrix.map_mul, MPSTensor.reindexBondMatrix_map_star,
    MPSTensor.reindexBondMatrix_map_star] at hσ
  have h2 := congrArg Matrix.conjTranspose hσ
  have hbar : (T'.map (starRingEnd ℂ))ᴴ = T'ᵀ := by
    ext i j
    simp
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    hbar, MPSTensor.reindexBondMatrix_conjTranspose, Matrix.mul_assoc] at h2
  have hRR' : R * R' = 1 := by
    rw [MPSTensor.reindexBondMatrix_mul_reindexBondMatrix]
    exact MPSTensor.reindexBondMatrix_self _
  calc T'ᵀ * (R * Tᴴ) = R * (R' * (T'ᵀ * (R * Tᴴ))) := by
        rw [← Matrix.mul_assoc R, hRR', Matrix.one_mul]
    _ = R * (starRingEnd ℂ (hF.daggerInverseScalar F hc y) •
          (1 : Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ)) := congrArg (R * ·) h2
    _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- The conjugate leg gauge of $x^{-1}$ inverts the leg gauge of $x$ up to
$\overline{\sigma_{x^{-1}}}$: $\overline{T^\dagger_{x^{-1\,-1}}}\,T^\dagger_{x^{-1}}
=\overline{\sigma_{x^{-1}}}\,\Id$ after the bond identifications.

Source: arXiv:2502.20257, `eq:intro_sigma` at $x^{-1}$, lines 1557--1562. -/
theorem daggerLegGauge_inv_map_star_mul (x : G) :
    (hF.daggerLegGauge hc x⁻¹).map (starRingEnd ℂ) * hF.daggerLegGauge hc x =
      starRingEnd ℂ (hF.daggerInverseScalar F hc x⁻¹) •
        MPSTensor.reindexBondMatrix ((hF.bondDim_inv F x).trans (hF.bondDim_inv F x⁻¹)) := by
  have hbar : ((hF.daggerInverseGauge F hc x⁻¹⁻¹ :
      Matrix (Fin (F.bondDim x⁻¹⁻¹)) (Fin (F.bondDim x⁻¹⁻¹)) ℂ)ᴴ).map (starRingEnd ℂ) =
      (hF.daggerInverseGauge F hc x⁻¹⁻¹ :
        Matrix (Fin (F.bondDim x⁻¹⁻¹)) (Fin (F.bondDim x⁻¹⁻¹)) ℂ)ᵀ := by
    ext i j
    simp
  simp only [daggerLegGauge, Matrix.map_mul, MPSTensor.reindexBondMatrix_map_star, hbar,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (MPSTensor.reindexBondMatrix _), ← Matrix.mul_assoc,
    hF.transpose_daggerInverseGauge_inv_mul_conjTranspose hc x⁻¹, Matrix.smul_mul,
    MPSTensor.reindexBondMatrix_mul_reindexBondMatrix]

/-- The target gauges of the pairs $(g,h)$ and $(h^{-1},g^{-1})$ compose to
$\sigma_{h^{-1}g^{-1}}$: $T_{(gh)^{-1}}\overline{T_{(h^{-1}g^{-1})^{-1}}}
=\sigma_{h^{-1}g^{-1}}\Id$ after the bond identifications.

Source: arXiv:2502.20257, `eq:intro_sigma` at $h^{-1}g^{-1}$, lines 1557--1562. -/
theorem daggerTargetGauge_mul_map_star_mul (g h : G) {p : ℕ}
    (Z : Matrix (Fin (F.bondDim (g * h))) (Fin p) ℂ) :
    hF.daggerTargetGauge hc g h * ((hF.daggerTargetGauge hc h⁻¹ g⁻¹).map (starRingEnd ℂ) *
        (F.castMat (congrArg₂ (· * ·) (inv_inv g).symm (inv_inv h).symm) * Z)) =
      hF.daggerInverseScalar F hc (h⁻¹ * g⁻¹) • Z := by
  set y := h⁻¹ * g⁻¹
  have hσ := hF.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one F hc y
  have hI : (hF.inverseDaggerInverseGauge F hc y :
      Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ) =
      MPSTensor.reindexBondMatrix (hF.bondDim_inv F y).symm *
        (hF.daggerInverseGauge F hc y⁻¹ : Matrix (Fin (F.bondDim y⁻¹)) (Fin (F.bondDim y⁻¹)) ℂ) *
          MPSTensor.reindexBondMatrix (hF.bondDim_inv F y) :=
    MPSTensor.reindex_finCongr_eq _ _
  rw [hI, Matrix.map_mul, Matrix.map_mul, MPSTensor.reindexBondMatrix_map_star,
    MPSTensor.reindexBondMatrix_map_star] at hσ
  simp only [Matrix.mul_assoc] at hσ
  have hT := hF.daggerInverseGauge_congr hc (mul_inv_rev h⁻¹ g⁻¹)
  simp only [daggerTargetGauge, Matrix.map_mul, MPSTensor.reindexBondMatrix_map_star, hT,
    castMat_eq_reindexBondMatrix, Matrix.mul_assoc,
    MPSTensor.reindexBondMatrix_mul_reindexBondMatrix_assoc]
  calc _ = MPSTensor.reindexBondMatrix (hF.bondDim_mul_inv_rev g h).symm *
        (((hF.daggerInverseGauge F hc y : Matrix (Fin (F.bondDim y)) (Fin (F.bondDim y)) ℂ) *
          (MPSTensor.reindexBondMatrix (hF.bondDim_inv F y).symm *
            ((hF.daggerInverseGauge F hc y⁻¹ :
              Matrix (Fin (F.bondDim y⁻¹)) (Fin (F.bondDim y⁻¹)) ℂ).map (starRingEnd ℂ) *
                MPSTensor.reindexBondMatrix (hF.bondDim_inv F y)))) *
          (MPSTensor.reindexBondMatrix (hF.bondDim_mul_inv_rev g h) * Z)) := by
        simp only [Matrix.mul_assoc, MPSTensor.reindexBondMatrix_mul_reindexBondMatrix_assoc]
        rfl
    _ = _ := by
        rw [hσ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
          MPSTensor.reindexBondMatrix_mul_reindexBondMatrix_assoc,
          MPSTensor.reindexBondMatrix_self, Matrix.one_mul]

/-- **The dagger of a left boundary** of $\mathcal U_{h^{-1}}\mathcal U_{g^{-1}}$:
$$
  X\longmapsto T_{(gh)^{-1}}\,\overline X\,\mathrm{swap}\,
    (T^\dagger_{g^{-1}}\otimes T^\dagger_{h^{-1}}),
$$
a left boundary of $\mathcal U_g\mathcal U_h$.  The dagger conjugates every entry
and exchanges the two bond legs on the same side; the bond spaces of $x$ and
$x^{-1}$ are identified as in `MPOTensor.GroupFamily.IsRepresentation.daggerLegGauge`.
The daggered fusion tensor $\widetilde F^<_{g,h}$ is the dagger of $F^<_{h^{-1},g^{-1}}$.

Source: arXiv:2502.20257, `eq:defzeta` and the display following it,
lines 1570--1662. -/
noncomputable def daggerBoundary (g h : G)
    (X : Matrix (Fin (F.bondDim (h⁻¹ * g⁻¹))) (Fin (F.bondDim h⁻¹ * F.bondDim g⁻¹)) ℂ) :
    Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ :=
  hF.daggerTargetGauge hc g h * X.map (starRingEnd ℂ) *
      ((productBondSwapEquiv (F.bondDim h⁻¹) (F.bondDim g⁻¹)).toPEquiv.toMatrix :
        Matrix _ _ ℂ) *
    idKron (F.bondDim g⁻¹) (hF.daggerLegGauge hc h) *
    kronId (hF.daggerLegGauge hc g) (F.bondDim h)

/-- **The dagger transports dressed proportionalities.** If $XB'^w=zYB'^w$ for long
words of $B'=\mathcal U_{h^{-1}}\mathcal U_{g^{-1}}$, then the daggers of $X$ and
$Y$ satisfy the same relation with $\overline z$ against long words of
$\mathcal U_g\mathcal U_h$.

This is the boundary-dressed form of "taking the dagger of
`eq:fusion_1`--`eq:fusion_2`, and using `eq:defT`" in the proof of `prop:zetas`,
arXiv:2502.20257, lines 1675--1677. -/
theorem isDressedProportional_daggerBoundary (g h : G)
    {X Y : Matrix (Fin (F.bondDim (h⁻¹ * g⁻¹))) (Fin (F.bondDim h⁻¹ * F.bondDim g⁻¹)) ℂ}
    {z : ℂ} (hXY : MPSTensor.IsDressedProportional
      (mulTensor (F.tensor h⁻¹) (F.tensor g⁻¹)).toMPSTensor X Y z) :
    MPSTensor.IsDressedProportional (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (hF.daggerBoundary hc g h X) (hF.daggerBoundary hc g h Y) (starRingEnd ℂ z) := by
  have h₀ := hXY.physicalAdjointTensor
  rw [physicalAdjointTensor_mulTensor] at h₀
  have h₁ := h₀.of_reindexBond_source _
  have h₂ := h₁.of_intertwine
    (B' := (mulTensor (physicalAdjointTensor (F.tensor g⁻¹)) (F.tensor h)).toMPSTensor)
    (P := idKron (F.bondDim g⁻¹) (hF.daggerLegGaugeInv hc h))
    (by rw [idKron_mul, hF.daggerLegGaugeInv_mul, idKron_one])
    (by rw [idKron_mul, hF.daggerLegGauge_mul_inv, idKron_one])
    (fun i ↦ mulTensor_mul_idKron_of_intertwine _
      (hF.tensor_mul_daggerLegGaugeInv hc h) i.divNat i.modNat)
  have h₃ := h₂.of_intertwine (B' := (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor)
    (P := kronId (hF.daggerLegGaugeInv hc g) (F.bondDim h))
    (by rw [kronId_mul, hF.daggerLegGaugeInv_mul, kronId_one])
    (by rw [kronId_mul, hF.daggerLegGauge_mul_inv, kronId_one])
    (fun i ↦ mulTensor_mul_kronId_of_intertwine _
      (hF.tensor_mul_daggerLegGaugeInv hc g) i.divNat i.modNat)
  have h₄ := h₃.mul_left (hF.daggerTargetGauge hc g h)
  simpa only [daggerBoundary, Matrix.mul_assoc] using h₄

end IsRepresentation

end MPOTensor.GroupFamily

namespace MPOTensor.GroupFamily.FusionData

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d}
  (fd : FusionData F) (hF : F.IsRepresentation)
  (hc : ∀ g : G, MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)

/-- The daggered left fusion tensor is the dagger of $F^<_{h^{-1},g^{-1}}$. -/
theorem daggerFusionV_eq_daggerBoundary (g h : G) :
    fd.daggerFusionV hF hc g h = hF.daggerBoundary hc g h (fd.V h⁻¹ g⁻¹) := by
  simp only [daggerFusionV, IsRepresentation.daggerBoundary, Matrix.mul_assoc]

/-- **The daggered fusion tensors form a choice of fusion tensors**
(arXiv:2502.20257, proof of `prop:zetas`, lines 1675--1677). -/
noncomputable def dagger : FusionData F where
  V := fd.daggerFusionV hF hc
  W := fd.daggerFusionW hF hc
  isReduction := fd.isReduction_daggerFusion hF hc

/-- The scalars $\zeta_{g,h}$ of `eq:defzeta` compare the daggered choice of fusion
tensors with the original one. -/
theorem daggerZeta_eq_relativeScalar :
    fd.daggerZeta hF hc = (fd.dagger hF hc).relativeScalar fd :=
  rfl

/-- Fusion tensors of equal pairs of group elements agree after the bond
identifications. -/
theorem V_congr {a a' b b' : G} (ea : a = a') (eb : b = b') :
    fd.V a' b' = F.castMat (congrArg₂ (· * ·) ea eb) * (fd.V a b *
      (kronId (F.castMat ea.symm) (F.bondDim b) * idKron (F.bondDim a') (F.castMat eb.symm))) := by
  subst ea eb
  simp

/-- The bond legs of the double dagger: the leg gauges of $(h^{-1},g^{-1})$,
conjugated and exchanged, compose with those of $(g,h)$ to
$\overline{\sigma_{g^{-1}}}\,\overline{\sigma_{h^{-1}}}\,\Id$.

Source: arXiv:2502.20257, `eq:intro_sigma` at $g^{-1}$ and $h^{-1}$,
lines 1557--1562. -/
theorem daggerLegGauge_double (g h : G) :
    kronId (F.castMat (inv_inv g)) (F.bondDim h) *
      (idKron (F.bondDim g⁻¹⁻¹) (F.castMat (inv_inv h)) *
        (kronId ((hF.daggerLegGauge hc g⁻¹).map (starRingEnd ℂ)) (F.bondDim h⁻¹⁻¹) *
          (idKron (F.bondDim g⁻¹) ((hF.daggerLegGauge hc h⁻¹).map (starRingEnd ℂ)) *
            (idKron (F.bondDim g⁻¹) (hF.daggerLegGauge hc h) *
              kronId (hF.daggerLegGauge hc g) (F.bondDim h))))) =
      (starRingEnd ℂ (hF.daggerInverseScalar F hc g⁻¹) *
        starRingEnd ℂ (hF.daggerInverseScalar F hc h⁻¹)) • 1 := by
  rw [← Matrix.mul_assoc (idKron _ ((hF.daggerLegGauge hc h⁻¹).map _)), idKron_mul,
    hF.daggerLegGauge_inv_map_star_mul hc h, ← kronId_mul_idKron, ← Matrix.mul_assoc
      (kronId ((hF.daggerLegGauge hc g⁻¹).map _) _), kronId_mul,
    hF.daggerLegGauge_inv_map_star_mul hc g, ← kronId_mul_idKron_assoc, ← Matrix.mul_assoc,
    kronId_mul, idKron_mul]
  simp only [castMat_eq_reindexBondMatrix, Matrix.mul_smul,
    MPSTensor.reindexBondMatrix_mul_reindexBondMatrix, MPSTensor.reindexBondMatrix_self,
    kronId_smul, idKron_smul, kronId_one, idKron_one, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, mul_comm]

/-- **The double dagger of a fusion tensor.** Daggering $F^<_{g,h}$ twice returns
$\sigma_{h^{-1}g^{-1}}\overline{\sigma_{g^{-1}}}\,\overline{\sigma_{h^{-1}}}\,F^<_{g,h}$
exactly: the conjugations cancel, and the gauges compose by `eq:intro_sigma`.

Source: arXiv:2502.20257, proof of `prop:zetas`, "applying this duality twice,
together with `eq:intro_sigma`", lines 1675--1677. -/
theorem daggerBoundary_daggerFusionV (g h : G) :
    hF.daggerBoundary hc g h (fd.daggerFusionV hF hc h⁻¹ g⁻¹) =
      (hF.daggerInverseScalar F hc (h⁻¹ * g⁻¹) *
        (starRingEnd ℂ (hF.daggerInverseScalar F hc g⁻¹) *
          starRingEnd ℂ (hF.daggerInverseScalar F hc h⁻¹))) • fd.V g h := by
  rw [daggerFusionV_eq_daggerBoundary]
  simp only [IsRepresentation.daggerBoundary, Matrix.map_mul, idKron_map_star,
    kronId_map_star, equiv_toMatrix_map_star, Matrix.map_starRingEnd_map_starRingEnd,
    Matrix.mul_assoc]
  rw [fd.V_congr (inv_inv g).symm (inv_inv h).symm]
  simp only [Matrix.mul_assoc]
  rw [productBondSwap_mul_idKron_mul_kronId_mul_productBondSwap_assoc,
    daggerLegGauge_double hF hc g h, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_smul, hF.daggerTargetGauge_mul_map_star_mul hc g h, smul_smul]
  congr 1
  ring

/-- **`eq:zeta`** (arXiv:2502.20257, Proposition `prop:zetas`, lines 1638--1642):
$$
  \zeta_{g,h}\,\overline{\zeta_{h^{-1},g^{-1}}}=\frac{\sigma_g\sigma_h}{\sigma_{gh}}.
$$
The proof follows the source, lines 1675--1677: the defining relation
`eq:defzeta` at $(h^{-1},g^{-1})$, daggered, compares the double dagger of
$F^<_{g,h}$ with $\widetilde F^<_{g,h}$ by $\overline{\zeta_{h^{-1},g^{-1}}}$, and
`eq:defzeta` at $(g,h)$ compares $\widetilde F^<_{g,h}$ with $F^<_{g,h}$ by
$\zeta_{g,h}$; the double dagger is the explicit multiple
`MPOTensor.GroupFamily.FusionData.daggerBoundary_daggerFusionV` of $F^<_{g,h}$, and
$\overline{\sigma_x}=\sigma_x^{-1}=\sigma_{x^{-1}}$ by `eq:intro_sigma`. -/
theorem daggerZeta_mul_star_daggerZeta_inv (g h : G) :
    (fd.daggerZeta hF hc (g, h) : ℂ) * starRingEnd ℂ (fd.daggerZeta hF hc (h⁻¹, g⁻¹)) =
      hF.daggerInverseScalar F hc g * hF.daggerInverseScalar F hc h /
        hF.daggerInverseScalar F hc (g * h) := by
  have hN := hF.isNormalRepresentation
  have hstar (x : G) :
      starRingEnd ℂ (hF.daggerInverseScalar F hc x⁻¹) = hF.daggerInverseScalar F hc x := by
    have h₁ := hF.daggerInverseScalar_mul_inverse_eq_one F hc x
    have h₂ := hF.daggerInverseScalar_mul_star_eq_one F hc x⁻¹
    calc starRingEnd ℂ (hF.daggerInverseScalar F hc x⁻¹) =
          hF.daggerInverseScalar F hc x * hF.daggerInverseScalar F hc x⁻¹ *
            starRingEnd ℂ (hF.daggerInverseScalar F hc x⁻¹) := by rw [h₁, one_mul]
      _ = hF.daggerInverseScalar F hc x := by rw [mul_assoc, h₂, mul_one]
  have hne (x : G) : hF.daggerInverseScalar F hc x ≠ 0 := by
    intro h0
    have := hF.daggerInverseScalar_mul_inverse_eq_one F hc x
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hinv :
      hF.daggerInverseScalar F hc (h⁻¹ * g⁻¹) = (hF.daggerInverseScalar F hc (g * h))⁻¹ := by
    rw [← mul_inv_rev]
    exact eq_inv_of_mul_eq_one_right (hF.daggerInverseScalar_mul_inverse_eq_one F hc (g * h))
  set c := hF.daggerInverseScalar F hc (h⁻¹ * g⁻¹) *
    (starRingEnd ℂ (hF.daggerInverseScalar F hc g⁻¹) *
      starRingEnd ℂ (hF.daggerInverseScalar F hc h⁻¹))
  have hc0 : c ≠ 0 := by
    simp only [c, hstar]
    exact mul_ne_zero (by rw [hinv]; exact inv_ne_zero (hne _)) (mul_ne_zero (hne _) (hne _))
  have ht := hF.isDressedProportional_daggerBoundary hc g h
    (fd.daggerZeta_defzeta hF hc h⁻¹ g⁻¹).1
  rw [fd.daggerBoundary_daggerFusionV hF hc g h, ← fd.daggerFusionV_eq_daggerBoundary] at ht
  have hcomp := ht.trans (fd.daggerZeta_defzeta hF hc g h).1
  have hscalar : MPSTensor.IsDressedProportional (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (c • fd.V g h) (fd.V g h) c :=
    ⟨0, fun w _ ↦ by rw [Matrix.smul_mul]⟩
  have key := hcomp.eq_of_forall_exists_ne_zero hscalar fun N ↦ by
    obtain ⟨w, hw, hw0⟩ := (fd.isReduction g h).exists_mul_evalWord_ne_zero
      (hN.isNormal _) (F.bondDim_pos _) N
    exact ⟨w, hw, by rw [Matrix.smul_mul]; exact smul_ne_zero hc0 hw0⟩
  rw [mul_comm, key]
  simp only [c, hstar, hinv]
  field_simp [hne (g * h)]

/-- **The anomaly three-cocycle under the change to daggered fusion tensors.**
Replacing the fusion tensors by the daggered ones multiplies $\omega$ by the
coboundary of $\zeta$:
$$
  \omega(g,h,k)=\frac{\zeta_{g,hk}\zeta_{h,k}}{\zeta_{g,h}\zeta_{gh,k}}\,
    \widetilde\omega(g,h,k),
$$
where $\widetilde\omega$ is the three-cocycle of the daggered fusion tensors.  This
is the gauge-change half of the proof of `eq:inv_omega`
(arXiv:2502.20257, `eq:omegagauge` and lines 1662--1677); the identification of
$\widetilde\omega(g,h,k)$ with $\overline{\omega(k^{-1},h^{-1},g^{-1})}^{\,-1}$, by
taking the dagger of the two fusion trees, is not proved here. -/
theorem omega_eq_fusionGauge_daggerZeta :
    fd.omega = ScalarThreeCochain.fusionGauge (fd.daggerZeta hF hc) (fd.dagger hF hc).omega :=
  omega_eq_fusionGauge hF.isNormalRepresentation (fd.dagger hF hc) fd

end MPOTensor.GroupFamily.FusionData
