/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycle
import TNLean.MPS.Core.ReductionComposition
import TNLean.MPS.FundamentalTheorem.Reduction.MPOProduct

/-!
# The anomaly three-cocycle of a group of matrix product operators

Let `g ↦ O_g` be a group-indexed family of matrix product operator tensors with
normal doubled-index tensors, positive bond dimensions, and the exact operator
law `O_g O_h = O_{gh}` on every nonempty chain.  A choice of fusion tensors
(`MPOTensor.GroupFamily.FusionData`) is a reduction `(V_{g,h}, W_{g,h})` of the
stacked product of `O_g` and `O_h` onto `O_{gh}` for every pair.

For three elements the triple product reduces onto `O_{ghk}` along the two
fusion trees

* `V^L = V_{gh,k} (V_{g,h} ⊗ 1)`, fusing `g` with `h` first, and
* `V^R = V_{g,hk} (1 ⊗ V_{h,k}) a⁻¹`, fusing `h` with `k` first, where `a` is
  the bond associator.

Two reductions onto a normal tensor agree against long words up to a nonzero
scalar; the scalar comparing these two trees is `ω(g,h,k)`:
`V^L T^w = ω(g,h,k) V^R T^w` for all long words `w` of the triple product `T`.
Equivalently `T^w W^R = ω(g,h,k) T^w W^L`, which is the display defining `ω` in
arXiv:2502.20257, `main.tex` lines 1506--1535, with `F^> = W` and `F^< = V`.

## Main definitions

* `MPOTensor.GroupFamily.IsNormalRepresentation`: normal tensors with the exact
  positive-length operator law.
* `MPOTensor.GroupFamily.FusionData`: a choice of fusion tensors.
* `MPOTensor.GroupFamily.FusionData.IsAssociator`: the left-dressed
  characterization of the value `ω(g,h,k)`.
* `MPOTensor.GroupFamily.FusionData.omega`: the anomaly three-cochain.

## Main results

* `MPOTensor.GroupFamily.FusionData.isAssociator_omega` and
  `MPOTensor.GroupFamily.FusionData.eq_omega_of_isAssociator`: `ω(g,h,k)` is the
  unique scalar with the dressed identity.
* `MPOTensor.GroupFamily.FusionData.isCocycle_omega`: the three-cocycle equation
  `eq:3-cocycle`.
* `MPOTensor.GroupFamily.FusionData.omega_eq_fusionGauge`: changing the fusion
  tensors changes `ω` by the coboundary of `eq:omegagauge`, so the cohomology
  class is independent of the choice
  (`MPOTensor.GroupFamily.FusionData.omega_cohomologousTo`).

The three-cochain is not normalized here.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor

variable {d : ℕ}

/-- Equal periodic operators at every positive length give equal positive-length
matrix product vectors of the doubled-index tensors.

Source: arXiv:1606.00608, Section 4.1 (the operator family `O_N` and its matrix
entries). -/
theorem sameMPV₂Pos_toMPSTensor_of_mpo_eq {D₁ D₂ : ℕ} {M : MPOTensor d D₁}
    {M' : MPOTensor d D₂} (h : ∀ N, 0 < N → mpo M N = mpo M' N) :
    MPSTensor.SameMPV₂Pos M.toMPSTensor M'.toMPSTensor := by
  intro N hN ρ
  rw [mpv_toMPSTensor, mpv_toMPSTensor, h N hN]

namespace GroupFamily

universe u

variable {G : Type u} [Group G]

/-- A group-indexed family of matrix product operator tensors represents the
group with normal tensors when every doubled-index tensor is normal and the
periodic operators multiply exactly as the group on every nonempty chain.

Source: arXiv:2502.20257, lines 1403--1407 (the representation law); normality
of the tensors is the hypothesis under which the fusion tensors exist, see
`MPOTensor.GroupFamily.IsNormalRepresentation.nonempty_fusionData`. -/
structure IsNormalRepresentation (F : GroupFamily G d) : Prop where
  isNormal : ∀ g, Kraus.IsNormal (F.tensor g).toMPSTensor
  operator_mul : ∀ g h N, 0 < N →
    mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N

/-- An exact representation by simple injective tensors has normal tensors. -/
theorem IsRepresentation.isNormalRepresentation {F : GroupFamily G d}
    (hF : F.IsRepresentation) : F.IsNormalRepresentation :=
  ⟨fun g ↦ (hF.isInjective g).isNormal, hF.operator_mul⟩

variable {F : GroupFamily G d}

/-- The permutation matrix identifying the bond spaces of the tensors indexed by
two equal group elements, such as `g * (h * k)` and `g * h * k`. -/
noncomputable def castMat (F : GroupFamily G d) {a b : G} (e : a = b) :
    Matrix (Fin (F.bondDim b)) (Fin (F.bondDim a)) ℂ :=
  (finCongr (congrArg F.bondDim e.symm)).toPEquiv.toMatrix

omit [Group G] in
/-- Identifying a bond space with itself is the identity. -/
@[simp] theorem castMat_rfl (a : G) : F.castMat (rfl : a = a) = 1 := by
  simp [castMat]

omit [Group G] in
/-- Bond identifications compose. -/
@[simp] theorem castMat_mul_castMat {a b c : G} (e₁ : a = b) (e₂ : b = c) :
    F.castMat e₂ * F.castMat e₁ = F.castMat (e₁.trans e₂) := by
  subst e₁ e₂
  simp

omit [Group G] in
/-- Bond identifications compose, against a trailing factor. -/
@[simp] theorem castMat_mul_castMat_assoc {a b c : G} {n : ℕ} (e₁ : a = b) (e₂ : b = c)
    (X : Matrix (Fin (F.bondDim a)) (Fin n) ℂ) :
    F.castMat e₂ * (F.castMat e₁ * X) = F.castMat (e₁.trans e₂) * X := by
  rw [← Matrix.mul_assoc, castMat_mul_castMat]

omit [Group G] in
/-- A reduction onto the tensor of `a` is a reduction onto the tensor of any
`b = a`, after identifying the bond spaces. -/
theorem isReduction_castMat {D : ℕ} {B : MPSTensor (d * d) D} {a b : G}
    {V : Matrix (Fin (F.bondDim a)) (Fin D) ℂ} {W : Matrix (Fin D) (Fin (F.bondDim a)) ℂ}
    (h : MPSTensor.IsReduction B (F.tensor a).toMPSTensor V W) (e : a = b) :
    MPSTensor.IsReduction B (F.tensor b).toMPSTensor (F.castMat e * V)
      (W * F.castMat e.symm) := by
  subst e
  simpa using h

/-- A choice of fusion tensors: for every pair `g, h`, a reduction `(V, W)` of the
stacked product of the tensors of `g` and `h` onto the tensor of `g * h`.

Source: arXiv:2502.20257, equations `eq:fusion_1` and `eq:fusion_2`, `main.tex`
lines 1403--1497, with `F^<_{g,h} = V g h` and `F^>_{g,h} = W g h`. -/
structure FusionData (F : GroupFamily G d) where
  /-- The left fusion tensor `F^<_{g,h}`. -/
  V : ∀ g h : G, Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ
  /-- The right fusion tensor `F^>_{g,h}`. -/
  W : ∀ g h : G, Matrix (Fin (F.bondDim g * F.bondDim h)) (Fin (F.bondDim (g * h))) ℂ
  isReduction : ∀ g h, MPSTensor.IsReduction
    (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor (F.tensor (g * h)).toMPSTensor
    (V g h) (W g h)

namespace IsNormalRepresentation

/-- Stacking the tensors of `g` and `h` gives the positive-length matrix product
vectors of the tensor of `g * h`.

Source: arXiv:2502.20257, lines 1403--1407. -/
theorem sameMPV₂Pos_mulTensor (hF : F.IsNormalRepresentation) (g h : G) :
    MPSTensor.SameMPV₂Pos (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (F.tensor (g * h)).toMPSTensor :=
  sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
    rw [mpo_mulTensor, hF.operator_mul g h N hN]

/-- **Existence of fusion tensors** (arXiv:2502.20257, `eq:fusion_2`, citing the
single-block reduction theorem of Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2,
Proposition 20). -/
theorem nonempty_fusionData (hF : F.IsNormalRepresentation) : Nonempty (FusionData F) := by
  choose V W hVW using fun g h : G ↦
    MPSTensor.exists_isReduction_and_nilpotent_of_isNormal (F.tensor (g * h)).toMPSTensor
      (hF.isNormal _) (F.bondDim_pos _) _ (hF.sameMPV₂Pos_mulTensor g h)
  exact ⟨⟨V, W, fun g h ↦ (hVW g h).1⟩⟩

end IsNormalRepresentation

/-- The stacked triple product `(O_g O_h) O_k`. -/
noncomputable abbrev tripleTensor (F : GroupFamily G d) (g h k : G) :
    MPOTensor d (F.bondDim g * F.bondDim h * F.bondDim k) :=
  mulTensor (mulTensor (F.tensor g) (F.tensor h)) (F.tensor k)

namespace FusionData

variable (fd : FusionData F)

/-- The left boundary of the fusion tree fusing `g` with `h` first:
`V_{gh,k} (V_{g,h} ⊗ 1)`.

Source: arXiv:2502.20257, right-hand side of the display preceding
`eq:3-cocycle`, `main.tex` lines 1506--1535. -/
noncomputable def leftV (g h k : G) :
    Matrix (Fin (F.bondDim (g * h * k))) (Fin (F.bondDim g * F.bondDim h * F.bondDim k)) ℂ :=
  fd.V (g * h) k * kronId (fd.V g h) (F.bondDim k)

/-- The right boundary of the fusion tree fusing `g` with `h` first. -/
noncomputable def leftW (g h k : G) :
    Matrix (Fin (F.bondDim g * F.bondDim h * F.bondDim k)) (Fin (F.bondDim (g * h * k))) ℂ :=
  kronId (fd.W g h) (F.bondDim k) * fd.W (g * h) k

/-- The left boundary of the fusion tree fusing `h` with `k` first:
`V_{g,hk} (1 ⊗ V_{h,k}) a⁻¹`, with `a` the bond associator.

Source: arXiv:2502.20257, left-hand side of the display preceding
`eq:3-cocycle`, `main.tex` lines 1506--1535. -/
noncomputable def rightV (g h k : G) :
    Matrix (Fin (F.bondDim (g * h * k))) (Fin (F.bondDim g * F.bondDim h * F.bondDim k)) ℂ :=
  F.castMat (mul_assoc g h k).symm *
    (fd.V g (h * k) * idKron (F.bondDim g) (fd.V h k) *
      mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))

/-- The right boundary of the fusion tree fusing `h` with `k` first. -/
noncomputable def rightW (g h k : G) :
    Matrix (Fin (F.bondDim g * F.bondDim h * F.bondDim k)) (Fin (F.bondDim (g * h * k))) ℂ :=
  mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k) *
      (idKron (F.bondDim g) (fd.W h k) * fd.W g (h * k)) *
    F.castMat (mul_assoc g h k).symm.symm

/-- The fusion tree fusing `g` with `h` first reduces the triple product onto the
tensor of `g * h * k`. -/
theorem isReduction_left (g h k : G) :
    MPSTensor.IsReduction (F.tripleTensor g h k).toMPSTensor
      (F.tensor (g * h * k)).toMPSTensor (fd.leftV g h k) (fd.leftW g h k) :=
  ((fd.isReduction g h).mulTensor_kronId (F.tensor k)).trans (fd.isReduction (g * h) k)

/-- The fusion tree fusing `h` with `k` first reduces the triple product onto the
tensor of `g * h * k`. -/
theorem isReduction_right (g h k : G) :
    MPSTensor.IsReduction (F.tripleTensor g h k).toMPSTensor
      (F.tensor (g * h * k)).toMPSTensor (fd.rightV g h k) (fd.rightW g h k) :=
  isReduction_castMat ((((fd.isReduction h k).mulTensor_idKron (F.tensor g)).trans
    (fd.isReduction g (h * k))).mulTensor_assoc_left) (mul_assoc g h k).symm

/-- The characterization of the value `ω(g,h,k)`: the two fusion trees of the
triple product satisfy `V^L T^w = z V^R T^w` for all long words `w`.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
def IsAssociator (g h k : G) (z : ℂ) : Prop :=
  MPSTensor.IsDressedProportional (F.tripleTensor g h k).toMPSTensor
    (fd.leftV g h k) (fd.rightV g h k) z

open Classical in
/-- **The anomaly three-cochain of a choice of fusion tensors**: `ω(g,h,k)` is the
nonzero scalar comparing the two fusion trees of the triple product
(`MPOTensor.GroupFamily.FusionData.isAssociator_omega`).  It is set to one if no
such scalar exists, which does not happen for a normal representation.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
noncomputable def omega : ScalarThreeCochain G := fun g h k ↦
  if hz : ∃ z : ℂ, z ≠ 0 ∧ fd.IsAssociator g h k z then Units.mk0 hz.choose hz.choose_spec.1
  else 1

variable {fd}

/-- The triple product has the positive-length matrix product vectors of the
tensor of `g * h * k`. -/
theorem _root_.MPOTensor.GroupFamily.IsNormalRepresentation.sameMPV₂Pos_tripleTensor
    (hF : F.IsNormalRepresentation) (g h k : G) :
    MPSTensor.SameMPV₂Pos (F.tripleTensor g h k).toMPSTensor
      (F.tensor (g * h * k)).toMPSTensor :=
  sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
    simp only [mpo_mulTensor, ← hF.operator_mul _ _ N hN]

/-- `ω(g,h,k)` satisfies the characterizing dressed identity.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
theorem isAssociator_omega (hF : F.IsNormalRepresentation) (g h k : G) :
    fd.IsAssociator g h k (fd.omega g h k) := by
  have hex : ∃ z : ℂ, z ≠ 0 ∧ fd.IsAssociator g h k z :=
    (fd.isReduction_left g h k).exists_isDressedProportional (fd.isReduction_right g h k)
      (hF.isNormal _) (hF.sameMPV₂Pos_tripleTensor g h k)
  simp only [omega, hex, ↓reduceDIte, Units.val_mk0]
  exact hex.choose_spec.2

/-- The left boundary of the first fusion tree is nonzero against arbitrarily long
words of the triple product. -/
theorem exists_leftV_mul_evalWord_ne_zero (hF : F.IsNormalRepresentation) (g h k : G)
    (N : ℕ) : ∃ w, N ≤ w.length ∧
      fd.leftV g h k * Kraus.evalWord (F.tripleTensor g h k).toMPSTensor w ≠ 0 :=
  (fd.isReduction_left g h k).exists_mul_evalWord_ne_zero (hF.isNormal _)
    (F.bondDim_pos _) N

/-- **Uniqueness of `ω(g,h,k)`**: any scalar satisfying the characterizing dressed
identity is `ω(g,h,k)`. -/
theorem eq_omega_of_isAssociator (hF : F.IsNormalRepresentation) {g h k : G} {z : ℂ}
    (hz : fd.IsAssociator g h k z) : z = fd.omega g h k :=
  MPSTensor.IsDressedProportional.eq_of_forall_exists_ne_zero hz
    (isAssociator_omega hF g h k) (exists_leftV_mul_evalWord_ne_zero hF g h k)

/-- Moving a bond identification out of a fusion tensor with a factor on the
right. -/
theorem V_mul_kronId_castMat {a b : G} (e : a = b) (l : G) {n : ℕ}
    (X : Matrix (Fin (F.bondDim a)) (Fin n) ℂ) :
    fd.V b l * kronId (F.castMat e * X) (F.bondDim l) =
      F.castMat (congrArg (· * l) e) * (fd.V a l * kronId X (F.bondDim l)) := by
  subst e
  simp

/-- Moving a bond identification out of a fusion tensor with a factor on the
left. -/
theorem V_mul_idKron_castMat (g : G) {a b : G} (e : a = b) {n : ℕ}
    (X : Matrix (Fin (F.bondDim a)) (Fin n) ℂ) :
    fd.V g b * idKron (F.bondDim g) (F.castMat e * X) =
      F.castMat (congrArg (g * ·) e) * (fd.V g a * idKron (F.bondDim g) X) := by
  subst e
  simp

/-- **The anomaly three-cochain is a three-cocycle** (arXiv:2502.20257,
`eq:3-cocycle`, `main.tex` lines 1536--1540):
`ω(gh,k,l) ω(g,h,kl) = ω(g,h,k) ω(g,hk,l) ω(h,k,l)`.

The five fusion trees of the fourfold product are reductions onto the tensor of
`g h k l`; adjacent trees differ by one value of `ω` against long words, and
comparing the two paths around the pentagon on a nonvanishing word gives the
identity. -/
theorem isCocycle_omega (hF : F.IsNormalRepresentation) :
    ScalarThreeCochain.IsCocycle fd.omega := by
  intro g h k l
  have hS : ∀ N, 0 < N → ∀ a b : G,
      mpo (F.tensor a) N * mpo (F.tensor b) N = mpo (F.tensor (a * b)) N :=
    fun N hN a b ↦ hF.operator_mul a b N hN
  -- the five pairwise relations
  have h1 := ((isAssociator_omega (fd := fd) hF g h k).mulTensor_kronId
    (F.tensor l)).mul_left (fd.V (g * h * k) l)
  have h5 := (isAssociator_omega (fd := fd) hF (g * h) k l).pullback
    (((fd.isReduction g h).mulTensor_kronId (F.tensor k)).mulTensor_kronId (F.tensor l))
    (sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
      simp only [mpo_mulTensor, ← hS N hN, Matrix.mul_assoc])
  have h4 := (isAssociator_omega (fd := fd) hF g h (k * l)).pullback
    ((fd.isReduction k l).mulTensor_idKron
      (mulTensor (F.tensor g) (F.tensor h))).mulTensor_assoc_left
    (sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
      simp only [mpo_mulTensor, ← hS N hN, Matrix.mul_assoc])
  have h2 := (isAssociator_omega (fd := fd) hF g (h * k) l).pullback
    (((fd.isReduction h k).mulTensor_idKron (F.tensor g)).mulTensor_assoc_left.mulTensor_kronId
      (F.tensor l))
    (sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
      simp only [mpo_mulTensor, ← hS N hN, Matrix.mul_assoc])
  have hPQ : (kronId (mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
        (F.bondDim l) *
        mulTensorAssocMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l)) *
      (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l) *
        kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
          (F.bondDim l)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mulTensorAssocMatrix _ _ _),
      mulTensorAssocMatrix_mul_invMatrix, Matrix.one_mul, kronId_mul,
      mulTensorAssocMatrix_mul_invMatrix, kronId_one]
  have hQP : (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l) *
        kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
          (F.bondDim l)) *
      (kronId (mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
        (F.bondDim l) *
        mulTensorAssocMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kronId _ _), kronId_mul,
      mulTensorAssocInvMatrix_mul_matrix, kronId_one, Matrix.one_mul,
      mulTensorAssocInvMatrix_mul_matrix]
  have h3 := (((isAssociator_omega (fd := fd) hF h k l).mulTensor_idKron
    (F.tensor g)).mul_left (fd.V g (h * k * l))).of_intertwine hPQ hQP (fun i ↦ by
      change mulTensor (mulTensor (mulTensor (F.tensor g) (F.tensor h)) (F.tensor k))
          (F.tensor l) i.divNat i.modNat * _ = _ * mulTensor (F.tensor g)
          (mulTensor (mulTensor (F.tensor h) (F.tensor k)) (F.tensor l)) i.divNat i.modNat
      rw [← Matrix.mul_assoc, mulTensor_mul_kronId_of_intertwine (F.tensor l)
        (mulTensor_mul_assocMatrix (F.tensor g) (F.tensor h) (F.tensor k)),
        Matrix.mul_assoc, mulTensor_mul_assocMatrix, Matrix.mul_assoc])
  -- identifications of the fusion trees
  have hA5 : fd.leftV (g * h) k l * kronId (kronId (fd.V g h) (F.bondDim k)) (F.bondDim l) =
      fd.V (g * h * k) l * kronId (fd.leftV g h k) (F.bondDim l) := by
    simp only [leftV, Matrix.mul_assoc, kronId_mul]
  have hB2 : fd.V (g * h * k) l * kronId (fd.rightV g h k) (F.bondDim l) =
      F.castMat (by simp only [mul_assoc] : g * (h * k) * l = g * h * k * l) *
        (fd.leftV g (h * k) l * kronId (idKron (F.bondDim g) (fd.V h k) *
          mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (F.bondDim l)) := by
    rw [rightV, V_mul_kronId_castMat]
    congr 1
    simp only [leftV, Matrix.mul_assoc, kronId_mul]
  have hC3 : F.castMat (by simp only [mul_assoc] : g * (h * k) * l = g * h * k * l) *
        (fd.rightV g (h * k) l * kronId (idKron (F.bondDim g) (fd.V h k) *
          mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (F.bondDim l)) =
      F.castMat (by simp only [mul_assoc] : g * (h * k * l) = g * h * k * l) *
        (fd.V g (h * k * l) * idKron (F.bondDim g) (fd.leftV h k l) *
          (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l) *
            kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
              (F.bondDim l))) := by
    rw [rightV, Matrix.mul_assoc (F.castMat _), castMat_mul_castMat_assoc]
    congr 1
    simp only [leftV, ← kronId_mul, ← idKron_mul, Matrix.mul_assoc,
      assocInv_mul_kronId_idKron_assoc]
  have hD4 : F.castMat (by simp only [mul_assoc] : g * (h * k * l) = g * h * k * l) *
        (fd.V g (h * k * l) * idKron (F.bondDim g) (fd.rightV h k l) *
          (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (F.bondDim l) *
            kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k))
              (F.bondDim l))) =
      F.castMat (by simp only [mul_assoc] : g * h * (k * l) = g * h * k * l) *
        (fd.rightV g h (k * l) * (idKron (F.bondDim g * F.bondDim h) (fd.V k l) *
          mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (F.bondDim l))) := by
    rw [rightV, rightV, V_mul_idKron_castMat]
    simp only [Matrix.mul_assoc, castMat_mul_castMat_assoc]
    congr 1
    simp only [← idKron_mul, Matrix.mul_assoc, assocInv_mul_idKron_assoc]
    rw [← Matrix.mul_assoc (idKron _ (mulTensorAssocInvMatrix _ _ _)), assocInv_pentagon]
  have hE4 : F.castMat (by simp only [mul_assoc] : g * h * (k * l) = g * h * k * l) *
        (fd.leftV g h (k * l) * (idKron (F.bondDim g * F.bondDim h) (fd.V k l) *
          mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (F.bondDim l))) =
      fd.rightV (g * h) k l * kronId (kronId (fd.V g h) (F.bondDim k)) (F.bondDim l) := by
    simp only [leftV, rightV, Matrix.mul_assoc]
    congr 1
    rw [kronId_mul_idKron_assoc, assocInv_mul_kronId_kronId]
  -- the two paths around the pentagon
  have hBC := h2.mul_left (F.castMat (by simp only [mul_assoc] :
    g * (h * k) * l = g * h * k * l))
  rw [← hB2, hC3] at hBC
  have hCD := h3.mul_left (F.castMat (by simp only [mul_assoc] :
    g * (h * k * l) = g * h * k * l))
  have hED := h4.mul_left (F.castMat (by simp only [mul_assoc] :
    g * h * (k * l) = g * h * k * l))
  rw [hE4, ← hD4] at hED
  rw [hA5] at h5
  have path₁ := (h1.trans hBC).trans hCD
  have path₂ := h5.trans hED
  have hA := ((fd.isReduction_left g h k).mulTensor_kronId (F.tensor l)).trans
    (fd.isReduction (g * h * k) l)
  have key := path₂.eq_of_forall_exists_ne_zero path₁
    (hA.exists_mul_evalWord_ne_zero (hF.isNormal _) (F.bondDim_pos _))
  apply Units.ext
  simpa only [Units.val_mul] using key

open Classical in
/-- The scalar comparing two choices of fusion tensors: `β(g,h)` is the nonzero
scalar with `V_{g,h} B^w = β(g,h) V'_{g,h} B^w` for all long words `w` of the
stacked product `B` of the tensors of `g` and `h`
(`MPOTensor.GroupFamily.FusionData.isDressedProportional_relativeScalar`).  It
is set to one if no such scalar exists, which does not happen for a normal
representation.

Source: the scalar gauge freedom of the fusion tensors, arXiv:2502.20257,
`eq:scalar_fus_ten`, `main.tex` lines 1500--1504, under which
`F^> ↦ β F^>` and `F^< ↦ β⁻¹ F^<`. -/
noncomputable def relativeScalar (fd fd' : FusionData F) : ScalarCocycle G := fun g h ↦
  if hz : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor (fd.V g h) (fd'.V g h) z then
    Units.mk0 hz.choose hz.choose_spec.1
  else 1

/-- Two choices of fusion tensors differ, against long words, by the scalar
`relativeScalar`. -/
theorem isDressedProportional_relativeScalar (hF : F.IsNormalRepresentation)
    (fd fd' : FusionData F) (g h : G) :
    MPSTensor.IsDressedProportional (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (fd.V g h) (fd'.V g h) (fd.relativeScalar fd' g h) := by
  have hex : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor (fd.V g h) (fd'.V g h) z :=
    (fd.isReduction g h).exists_isDressedProportional (fd'.isReduction g h)
      (hF.isNormal _) (hF.sameMPV₂Pos_mulTensor g h)
  simp only [relativeScalar, hex, ↓reduceDIte, Units.val_mk0]
  exact hex.choose_spec.2

/-- **Change of fusion tensors changes `ω` by a coboundary** (arXiv:2502.20257,
`eq:omegagauge`, `main.tex` lines 1541--1545): if `β` compares two choices of
fusion tensors, then `ω'(g,h,k) = β(g,hk) β(h,k) / (β(g,h) β(gh,k)) ω(g,h,k)`. -/
theorem omega_eq_fusionGauge (hF : F.IsNormalRepresentation) (fd fd' : FusionData F) :
    fd'.omega = ScalarThreeCochain.fusionGauge (fd.relativeScalar fd') fd.omega := by
  funext g h k
  have hβ := isDressedProportional_relativeScalar hF fd fd'
  have hS : ∀ N, 0 < N → ∀ a b : G,
      mpo (F.tensor a) N * mpo (F.tensor b) N = mpo (F.tensor (a * b)) N :=
    fun N hN a b ↦ hF.operator_mul a b N hN
  have hleft : MPSTensor.IsDressedProportional (F.tripleTensor g h k).toMPSTensor
      (fd.leftV g h k) (fd'.leftV g h k)
      (fd.relativeScalar fd' g h * fd.relativeScalar fd' (g * h) k) :=
    (((hβ g h).mulTensor_kronId (F.tensor k)).mul_left (fd.V (g * h) k)).trans
      ((hβ (g * h) k).pullback ((fd'.isReduction g h).mulTensor_kronId (F.tensor k))
        (sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
          simp only [mpo_mulTensor, ← hS N hN]))
  have hright : MPSTensor.IsDressedProportional (F.tripleTensor g h k).toMPSTensor
      (fd.rightV g h k) (fd'.rightV g h k)
      (fd.relativeScalar fd' h k * fd.relativeScalar fd' g (h * k)) :=
    ((((hβ h k).mulTensor_idKron (F.tensor g)).mul_left (fd.V g (h * k))).trans
      ((hβ g (h * k)).pullback ((fd'.isReduction h k).mulTensor_idKron (F.tensor g))
        (sameMPV₂Pos_toMPSTensor_of_mpo_eq fun N hN ↦ by
          simp only [mpo_mulTensor, ← hS N hN]))).of_intertwine
      (mulTensorAssocMatrix_mul_invMatrix _ _ _) (mulTensorAssocInvMatrix_mul_matrix _ _ _)
      (fun i ↦ mulTensor_mul_assocMatrix _ _ _ i.divNat i.modNat) |>.mul_left _
  have hne : ((fd.relativeScalar fd' h k * fd.relativeScalar fd' g (h * k) : ℂˣ) : ℂ) ≠ 0 :=
    Units.ne_zero _
  have key := eq_omega_of_isAssociator (fd := fd) hF
    ((hleft.trans (isAssociator_omega (fd := fd') hF g h k)).trans (hright.symm (by
      simpa only [Units.val_mul] using hne)))
  apply Units.ext
  simp only [ScalarThreeCochain.fusionGauge, ScalarThreeCochain.coboundary, Units.val_mul,
    Units.val_div_eq_div_val, ← key]
  field_simp

/-- **The cohomology class of `ω` does not depend on the fusion tensors**
(arXiv:2502.20257, `eq:omegagauge` and the sentence following it, `main.tex`
lines 1541--1546). -/
theorem omega_cohomologousTo (hF : F.IsNormalRepresentation) (fd fd' : FusionData F) :
    ScalarThreeCochain.CohomologousTo fd'.omega fd.omega :=
  ⟨fd.relativeScalar fd', (omega_eq_fusionGauge hF fd fd').symm⟩

/-- For an exact representation by simple injective tensors, `ω` is a
three-cocycle (arXiv:2502.20257, `eq:3-cocycle`). -/
theorem isCocycle_omega_of_isRepresentation (hF : F.IsRepresentation) :
    ScalarThreeCochain.IsCocycle fd.omega :=
  isCocycle_omega hF.isNormalRepresentation

end FusionData

end GroupFamily

end MPOTensor
